from flask import Flask, request, render_template, send_file, flash, redirect, url_for, jsonify, session
import os, uuid, shutil, re
from threading import Thread
from site_scraper import SiteScraper
import json
from datetime import datetime, timedelta
import time
import logging
from functools import wraps

app = Flask(__name__)

# Пароль для доступа (из переменной окружения)
APP_PASSWORD = os.environ.get('APP_PASSWORD', 'admin123')

# Фиксированный secret_key на основе пароля — сессии сохраняются между перезапусками
import hashlib
app.secret_key = hashlib.sha256(f"scraper_session_{APP_PASSWORD}".encode()).hexdigest()

# Сессия длится 30 дней
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(days=30)

def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not session.get('logged_in'):
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function

JOB_DIR = 'jobs'
os.makedirs(JOB_DIR, exist_ok=True)

def cleanup_old_jobs():
    """Remove job folders older than 24 hours, but NEVER remove running jobs"""
    import fcntl
    
    try:
        cutoff_time = datetime.now() - timedelta(hours=24)
        cleaned = 0
        
        for job_id in os.listdir(JOB_DIR):
            job_path = os.path.join(JOB_DIR, job_id)
            if os.path.isdir(job_path):
                try:
                    # Check creation time
                    creation_time = datetime.fromtimestamp(os.path.getctime(job_path))
                    if creation_time < cutoff_time:
                        
                        # ⚠️ КРИТИЧЕСКАЯ ПРОВЕРКА: НЕ УДАЛЯЕМ АКТИВНЫЕ ЗАДАЧИ
                        status_file = os.path.join(job_path, 'status.json')
                        is_active = False
                        
                        if os.path.exists(status_file):
                            try:
                                with open(status_file, 'r') as f:
                                    fcntl.flock(f.fileno(), fcntl.LOCK_SH)  # Shared lock
                                    status_data = json.load(f)
                                    job_status = status_data.get('status', 'unknown')
                                    
                                    # НЕ удаляем если задача активна
                                    if job_status in ['running', 'starting', 'archiving']:
                                        is_active = True
                                        logging.info(f"Skipping cleanup of active job {job_id} (status: {job_status})")
                                    
                                    # Проверяем timestamp - если совсем недавно обновлялся, тоже не удаляем
                                    last_update = status_data.get('timestamp', '')
                                    if last_update:
                                        try:
                                            last_time = datetime.fromisoformat(last_update.replace('Z', '+00:00'))
                                            if datetime.now() - last_time < timedelta(minutes=30):
                                                is_active = True
                                                logging.info(f"Skipping cleanup of recently active job {job_id}")
                                        except:
                                            pass
                            except Exception as e:
                                logging.debug(f"Could not read status for cleanup check: {e}")
                                # Если не можем прочитать статус, НЕ удаляем (безопасно)
                                is_active = True
                        
                        # Удаляем только если задача точно завершена
                        if not is_active:
                            shutil.rmtree(job_path)
                            cleaned += 1
                            logging.info(f"Cleaned up completed job: {job_id}")
                            
                except Exception as e:
                    logging.warning(f"Failed to cleanup job {job_id}: {e}")
        
        if cleaned > 0:
            logging.info(f"Cleanup completed: removed {cleaned} old jobs")
        else:
            logging.debug("No old jobs to cleanup")
            
    except Exception as e:
        logging.error(f"Cleanup process failed: {e}")

def periodic_cleanup():
    """Run cleanup every hour"""
    while True:
        try:
            time.sleep(3600)  # Wait 1 hour
            cleanup_old_jobs()
        except Exception as e:
            logging.error(f"Periodic cleanup error: {e}")
            time.sleep(3600)  # Continue after error

# Start cleanup thread
cleanup_thread = Thread(target=periodic_cleanup, daemon=True)
cleanup_thread.start()
logging.info("Auto-cleanup service started")

@app.route('/login', methods=['GET', 'POST'])
def login():
    if session.get('logged_in'):
        return redirect(url_for('index'))
    
    error = None
    if request.method == 'POST':
        password = request.form.get('password', '')
        if password == APP_PASSWORD:
            session['logged_in'] = True
            session.permanent = True
            return redirect(url_for('index'))
        else:
            error = 'Неверный пароль'
    
    return render_template('login.html', error=error)

@app.route('/logout')
def logout():
    session.pop('logged_in', None)
    return redirect(url_for('login'))

@app.route('/', methods=['GET','POST'])
@login_required
def index():
    if request.method == 'POST':
        src = request.form['source_url'].strip()
        tgt = src  # Используем исходный URL как target (без замены домена)
        depth = int(request.form.get('depth',3))
        conc = int(request.form.get('concurrency',4))
        dmin = float(request.form.get('delay_min',1))
        dmax = float(request.form.get('delay_max',3))
        respect_robots = bool(request.form.get('respect_robots'))
        rewrite_content = bool(request.form.get('rewrite_content'))
        exclude_blog = bool(request.form.get('exclude_blog'))
        rewrite_language = request.form.get('rewrite_language', 'polish')
        job_id = str(uuid.uuid4())
        job_path = os.path.join(JOB_DIR, job_id)
        os.makedirs(job_path, exist_ok=True)
        out_dir = os.path.join(job_path, 'output')

        def run():
            status_file = os.path.join(job_path, 'status.json')
            
            def update_status(status, message, progress=0):
                import fcntl
                
                # THREAD-SAFE status обновление с блокировкой файла
                try:
                    # Проверяем существует ли job_path - если удален cleanup'ом, создаем заново
                    if not os.path.exists(os.path.dirname(status_file)):
                        os.makedirs(os.path.dirname(status_file), exist_ok=True)
                        logging.warning(f"Recreated job directory for {job_id} (was cleaned up)")
                    
                    # Check if task was cancelled - don't overwrite cancelled status
                    current_status = None
                    if os.path.exists(status_file):
                        try:
                            with open(status_file, 'r') as f:
                                fcntl.flock(f.fileno(), fcntl.LOCK_SH)  # Shared lock for reading
                                current_status = json.load(f)
                        except Exception as e:
                            logging.debug(f"Could not read status file: {e}")
                        
                        # If already cancelled, don't update status unless it's an error
                        if current_status and current_status.get('status') == 'cancelled' and status != 'error':
                            logging.info(f"Skipping status update '{status}' because task is cancelled")
                            return
                    
                    # Write status with exclusive lock
                    with open(status_file, 'w') as f:
                        fcntl.flock(f.fileno(), fcntl.LOCK_EX)  # Exclusive lock for writing
                        json.dump({
                            'status': status,
                            'message': message,
                            'progress': progress,
                            'timestamp': datetime.now().isoformat(),
                            'job_id': job_id  # Add job_id для отладки
                        }, f, ensure_ascii=False)
                        f.flush()  # Ensure written to disk
                        
                except Exception as e:
                    logging.error(f"Failed to update status for {job_id}: {e}")
                    # Fallback - create простой статус без блокировки если блокировка не сработала
                    try:
                        with open(status_file, 'w') as f:
                            json.dump({
                                'status': status,
                                'message': message,
                                'progress': progress,
                                'timestamp': datetime.now().isoformat(),
                                'job_id': job_id
                            }, f, ensure_ascii=False)
                    except:
                        logging.error(f"Critical: Could not write status file for {job_id}")
            
            try:
                update_status('running', 'Инициализация скрапера...', 0)
                sc = SiteScraper(src, tgt, out_dir,
                                 max_depth=depth,
                                 concurrency=conc,
                                 delay=(dmin,dmax),
                                 respect_robots=respect_robots,
                                 rewrite_content=rewrite_content,
                                 exclude_blog=exclude_blog,
                                 rewrite_language=rewrite_language,
                                 status_callback=update_status,
                                 job_id=job_id)
                
                # Execute scraping and check result
                scrape_result = sc.scrape()
                
                # If scraping was cancelled or failed, don't proceed with archiving
                if scrape_result and scrape_result.get('status') in ['cancelled', 'error']:
                    logging.info(f"Scraping {scrape_result.get('status')}: {scrape_result.get('message')}")
                    return  # Exit without archiving
                
                update_status('archiving', 'Создание ZIP архива...', 90)
                
                # Проверяем есть ли файлы для архивирования
                if os.path.exists(out_dir) and os.listdir(out_dir):
                    zip_path = os.path.join(job_path, 'result.zip')
                    try:
                        # Первая попытка - стандартный метод
                        shutil.make_archive(os.path.join(job_path,'result'),'zip',out_dir)
                        
                        # КРИТИЧНО: Проверяем что архив действительно создан и не пустой
                        import time
                        time.sleep(0.1)  # Даем файловой системе время закрыть файл
                        
                        if os.path.exists(zip_path) and os.path.getsize(zip_path) > 0:
                            # Синхронизируем данные на диск
                            with open(zip_path, 'rb') as zf:
                                os.fsync(zf.fileno())
                            # Дополнительная проверка перед установкой completed
                            time.sleep(0.2)  # Даем время ФС
                            if os.path.exists(zip_path) and os.path.getsize(zip_path) > 0:
                                logging.info(f"Archive created successfully: {zip_path} ({os.path.getsize(zip_path)} bytes)")
                                update_status('completed', 'Готово! Архив создан', 100)
                            else:
                                raise Exception("Архив исчез после создания")
                        else:
                            raise Exception("Архив не создался или пустой")
                    except Exception as archive_error:
                        logging.error(f"Standard archive creation failed: {archive_error}")
                        try:
                            # Вторая попытка - создаем архив без сжатия
                            import zipfile
                            with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_STORED) as zipf:
                                for root, dirs, files in os.walk(out_dir):
                                    for file in files:
                                        file_path = os.path.join(root, file)
                                        arcname = os.path.relpath(file_path, out_dir)
                                        try:
                                            zipf.write(file_path, arcname)
                                        except Exception as e:
                                            logging.warning(f"Skipping file {file_path}: {e}")
                            
                            # Проверяем что архив создался и не пустой
                            if os.path.exists(zip_path) and os.path.getsize(zip_path) > 0:
                                update_status('completed', 'Архив создан успешно', 100)
                            else:
                                raise Exception("Архив пустой или не создался")
                                
                        except Exception as final_error:
                            logging.error(f"Final archive creation failed: {final_error}")
                            # Третья попытка - копируем файлы и создаем простейший архив
                            try:
                                import zipfile
                                import tempfile
                                with tempfile.TemporaryDirectory() as temp_dir:
                                    # Копируем файлы во временную директорию
                                    temp_out = os.path.join(temp_dir, 'site')
                                    shutil.copytree(out_dir, temp_out)
                                    
                                    with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED, compresslevel=1) as zipf:
                                        for root, dirs, files in os.walk(temp_out):
                                            for file in files:
                                                file_path = os.path.join(root, file)
                                                arcname = os.path.relpath(file_path, temp_out)
                                                zipf.write(file_path, arcname)
                                
                                if os.path.exists(zip_path) and os.path.getsize(zip_path) > 0:
                                    update_status('completed', 'Архив создан (резервный метод)', 100)
                                else:
                                    update_status('error', 'Не удалось создать архив', 0)
                            except Exception as backup_error:
                                logging.error(f"Backup archive creation failed: {backup_error}")
                                update_status('error', f'Ошибка создания архива: {str(backup_error)}', 0)
                else:
                    update_status('error', 'Нет файлов для архивирования', 0)
            except Exception as e:
                update_status('error', f'Ошибка: {str(e)}', 0)

        Thread(target=run).start()
        flash(f'Задача {job_id} запущена')
        return redirect(url_for('status', job_id=job_id))

    return render_template('index.html')

def _validate_job_id(job_id):
    """Validate job_id to prevent path traversal attacks"""
    # Job ID should be a valid UUID format
    if not re.match(r'^[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$', job_id):
        return False
    # Additional check - no path separators
    if '/' in job_id or '\\' in job_id or '..' in job_id:
        return False
    return True

@app.route('/status/<job_id>')
@login_required
def status(job_id):
    # Validate job_id to prevent path traversal
    if not _validate_job_id(job_id):
        flash('Неверный ID задачи')
        return redirect(url_for('index'))
    
    # Read status file - THREAD-SAFE с блокировкой
    status_file = os.path.join(JOB_DIR, job_id, 'status.json')
    current_status = {'status': 'unknown', 'message': 'Статус неизвестен', 'progress': 0}
    
    if os.path.exists(status_file):
        try:
            import fcntl
            with open(status_file, 'r') as f:
                fcntl.flock(f.fileno(), fcntl.LOCK_SH)  # Shared lock для чтения
                current_status = json.load(f)
                
                # Дополнительная проверка целостности данных
                if not isinstance(current_status, dict):
                    current_status = {'status': 'error', 'message': 'Поврежденный файл статуса', 'progress': 0}
                if 'status' not in current_status:
                    current_status['status'] = 'unknown'
                if 'message' not in current_status:
                    current_status['message'] = 'Статус неизвестен'
                if 'progress' not in current_status:
                    current_status['progress'] = 0
                    
        except Exception as e:
            logging.warning(f"Failed to read status for {job_id}: {e}")
            current_status = {'status': 'error', 'message': f'Ошибка чтения статуса: {str(e)}', 'progress': 0}
    
    # Определяем ready - архив готов ТОЛЬКО если статус completed И файл существует И размер > 0
    zipf = os.path.join(JOB_DIR, job_id, 'result.zip')
    ready = (current_status.get('status') == 'completed' and 
             os.path.exists(zipf) and 
             os.path.getsize(zipf) > 0)
    
    if ready:
        logging.info(f"Archive ready for download: {zipf} ({os.path.getsize(zipf)} bytes)")
    
    # Calculate expiration time
    job_path = os.path.join(JOB_DIR, job_id)
    expiration_time = None
    if os.path.exists(job_path):
        creation_time = datetime.fromtimestamp(os.path.getctime(job_path))
        expiration_time = creation_time + timedelta(hours=24)
    
    return render_template('status.html', job_id=job_id, ready=ready, 
                         current_status=current_status, expiration_time=expiration_time)

@app.route('/api/status/<job_id>')
@login_required
def api_status(job_id):
    # Validate job_id to prevent path traversal
    if not _validate_job_id(job_id):
        return jsonify({'error': 'Invalid job ID'}), 400
    
    # THREAD-SAFE чтение статуса для API
    status_file = os.path.join(JOB_DIR, job_id, 'status.json')
    current_status = {'status': 'unknown', 'message': 'Статус неизвестен', 'progress': 0}
    
    if os.path.exists(status_file):
        try:
            import fcntl
            with open(status_file, 'r') as f:
                fcntl.flock(f.fileno(), fcntl.LOCK_SH)  # Shared lock для чтения
                current_status = json.load(f)
                
                # Проверка целостности данных для API
                if not isinstance(current_status, dict):
                    current_status = {'status': 'error', 'message': 'Поврежденный файл статуса', 'progress': 0}
                    
        except Exception as e:
            logging.warning(f"API failed to read status for {job_id}: {e}")
            current_status = {'status': 'error', 'message': f'Ошибка чтения статуса: {str(e)}', 'progress': 0}
    
    # Определяем ready - архив готов ТОЛЬКО если статус completed И файл существует И размер > 0
    zipf = os.path.join(JOB_DIR, job_id, 'result.zip')
    ready = (current_status.get('status') == 'completed' and 
             os.path.exists(zipf) and 
             os.path.getsize(zipf) > 0)
    
    return jsonify({
        'ready': ready,
        'status': current_status['status'],
        'message': current_status['message'],
        'progress': current_status['progress']
    })

@app.route('/download/<job_id>')
@login_required
def download(job_id):
    # Validate job_id to prevent path traversal
    if not _validate_job_id(job_id):
        logging.warning(f"Invalid job_id attempted: {job_id}")
        flash('Неверный ID задачи')
        return redirect(url_for('index'))
        
    path = os.path.join(JOB_DIR, job_id, 'result.zip')
    logging.info(f"Download request for job {job_id}, checking path: {path}")
    
    if os.path.exists(path):
        file_size = os.path.getsize(path)
        logging.info(f"Sending file {path} (size: {file_size} bytes)")
        return send_file(path, as_attachment=True, download_name='scraped_website.zip')
    
    logging.warning(f"File not found for download: {path}")
    flash('Архив ещё не готов или был удален. Попробуйте снова.')
    return redirect(url_for('status', job_id=job_id))

@app.route('/cleanup')
@login_required
def manual_cleanup():
    """Manual cleanup endpoint"""
    try:
        cleanup_old_jobs()
        flash('Очистка старых файлов выполнена успешно!')
    except Exception as e:
        flash(f'Ошибка при очистке: {str(e)}')
    return redirect(url_for('index'))

@app.route('/stop/<job_id>')
@login_required
def stop_job(job_id):
    """Stop a running scraping task"""
    # Validate job_id to prevent path traversal
    if not _validate_job_id(job_id):
        flash('Неверный ID задачи')
        return redirect(url_for('index'))
        
    try:
        stop_file = os.path.join(JOB_DIR, job_id, 'stop.flag')
        job_path = os.path.join(JOB_DIR, job_id)
        
        if os.path.exists(job_path):
            # Create stop flag
            with open(stop_file, 'w') as f:
                f.write('STOP')
            
            # Update status
            status_file = os.path.join(job_path, 'status.json')
            with open(status_file, 'w') as f:
                json.dump({
                    'status': 'cancelled',
                    'message': 'Задача остановлена пользователем',
                    'progress': 0,
                    'timestamp': datetime.now().isoformat()
                }, f, ensure_ascii=False)
            
            flash(f'Запрос на остановку задачи {job_id} отправлен')
        else:
            flash('Задача не найдена')
            
    except Exception as e:
        flash(f'Ошибка при остановке: {str(e)}')
    
    return redirect(url_for('status', job_id=job_id))

@app.route('/force_complete/<job_id>')
@login_required
def force_complete(job_id):
    """Force complete a stuck task by creating ZIP from existing output"""
    # Validate job_id to prevent path traversal
    if not _validate_job_id(job_id):
        flash('Неверный ID задачи')
        return redirect(url_for('index'))
        
    job_path = os.path.join(JOB_DIR, job_id)
    out_dir = os.path.join(job_path, 'output')
    zip_path = os.path.join(job_path, 'result.zip')
    
    if os.path.exists(out_dir) and not os.path.exists(zip_path):
        try:
            # Create ZIP from existing output
            shutil.make_archive(os.path.join(job_path,'result'),'zip',out_dir)
            
            # Update status
            status_file = os.path.join(job_path, 'status.json')
            with open(status_file, 'w') as f:
                json.dump({
                    'status': 'completed',
                    'message': 'Принудительно завершено без AI обработки',
                    'progress': 100,
                    'timestamp': datetime.now().isoformat()
                }, f, ensure_ascii=False)
            
            flash(f'Задача {job_id} принудительно завершена')
            return redirect(url_for('status', job_id=job_id))
        except Exception as e:
            flash(f'Ошибка при принудительном завершении: {str(e)}')
    else:
        flash('Нет данных для завершения или архив уже существует')
    
    return redirect(url_for('status', job_id=job_id))

if __name__=='__main__':
    app.run(host='0.0.0.0', port=5000, debug=False)
