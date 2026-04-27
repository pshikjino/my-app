import os
import urllib.parse
import requests
from bs4 import BeautifulSoup, Tag
from bs4.element import NavigableString

from urllib.robotparser import RobotFileParser
from concurrent.futures import ThreadPoolExecutor, as_completed
import logging
import time
import random
import hashlib
import re
from openai import OpenAI
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

logging.basicConfig(level=logging.INFO,
                    format='%(asctime)s [%(levelname)s] %(message)s')

class SiteScraper:
    def __init__(self, base_url, target_domain, output_dir,
                 max_depth=2, concurrency=30, delay=(0.1,0.2),
                 user_agent=None, respect_robots=True, rewrite_content=False,
                 exclude_blog=False, rewrite_language='polish', status_callback=None, job_id=None):
        self.base_url = base_url.rstrip('/')
        self.target_domain = target_domain.rstrip('/')
        self.output_dir = output_dir
        self.max_depth = max_depth
        self.visited = set()
        self.resources = set()
        self.concurrency = min(concurrency, 50)  # Высокий параллелизм для быстрой загрузки
        self.delay = delay
        self.headers = {'User-Agent': user_agent or 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'}
        self.respect_robots = respect_robots
        self.rewrite_content = rewrite_content
        self.exclude_blog = exclude_blog
        # Normalize language to lowercase for lookup
        self.rewrite_language = rewrite_language.lower() if rewrite_language else 'polish'
        self.status_callback = status_callback
        self.job_id = job_id
        self.should_stop = False
        self.stop_file = None
        if job_id:
            self.stop_file = os.path.join('jobs', job_id, 'stop.flag')

        # Language mappings for AI prompts - HUMAN-LIKE WRITING STYLE WITH LENGTH CONTROL
        self.language_prompts = {
            'polish': 'Przepisz ten tekst po polsku, aby brzmiał jak napisany przez prawdziwego człowieka. Użyj naturalnego języka potocznego, dodaj małe błędy stylistyczne i nieformalności, jakie popełniają ludzie. Pisz jak ekspert, ale nie jak robot - dodaj osobiste uwagi, przykłady z życia, używaj prostych słów zamiast skomplikowanych terminów. WAŻNE: Zachowaj podobną długość tekstu!',
            'english': 'Rewrite this text in English to sound like it was written by a real human. Use natural conversational language, add small stylistic imperfections and informalities that humans make. Write like an expert, but not like a robot - add personal insights, real-life examples, use simple words instead of complex terms. IMPORTANT: Keep similar text length!',
            'spanish': 'Reescribe este texto en español para que suene como escrito por una persona real. Usa lenguaje natural conversacional, añade pequeñas imperfecciones estilísticas e informalidades que cometen los humanos. Escribe como un experto, pero no como un robot - añade perspectivas personales, ejemplos de la vida real, usa palabras simples en lugar de términos complejos. IMPORTANTE: ¡Mantén una longitud de texto similar!',
            'czech': 'Přepište tento text v češtině tak, aby zněl jako napsaný skutečným člověkem. Používejte přirozený konverzační jazyk, přidejte malé stylistické nedokonalosti a neformálnosti, které lidé dělají. Pište jako expert, ale ne jako robot - přidejte osobní pohledy, příklady ze života, používejte jednoduchá slova místo složitých termínů. DŮLEŽITÉ: Zachovejte podobnou délku textu!',
            'german': 'Schreiben Sie diesen Text auf Deutsch um, damit er klingt, als wäre er von einem echten Menschen geschrieben. Verwenden Sie natürliche Umgangssprache, fügen Sie kleine stilistische Unvollkommenheiten und Zwanglosigkeiten hinzu, die Menschen machen. Schreiben Sie wie ein Experte, aber nicht wie ein Roboter - fügen Sie persönliche Einsichten und Beispiele aus dem Leben hinzu, verwenden Sie einfache Wörter statt komplexer Begriffe. WICHTIG: Behalten Sie eine ähnliche Textlänge bei!'
        }
        self.total_pages = 0
        self.processed_pages = 0
        self.failed_pages = 0

        # CSS class and ID renaming mapping
        self.css_class_mapping = {}
        self.css_id_mapping = {}
        self.used_names = set()

        # Store original files for later modification
        self.downloaded_pages = []
        self.downloaded_css_files = []
        
        # Track downloaded URLs for validation during conversion
        self.downloaded_urls = set()
        self.failed_resources = set()  # Отслеживаем неудачные загрузки
        
        # КЭШ для AI переписывания - не переписываем одинаковые тексты дважды
        self.rewrite_cache = {}  # SHA1 hash -> rewritten text
        import queue
        self.rewrite_queue = queue.Queue()  # Очередь для параллельного переписывания
        
        # Link discovery statistics
        self.link_discovery_stats = {
            'sitemap_pages': 0,
            'canonical_links': 0,
            'json_ld_links': 0,
            'meta_refresh_links': 0,
            'data_attribute_links': 0,
            'pagination_links': 0,
            'comment_links': 0,
            'regular_links': 0,
            'total_unique_links': 0,
            'discovery_rounds': 0,
            'pages_processed_for_links': 0
        }

        # ОПТИМИЗИРОВАННАЯ сессия с retry стратегией и connection pool
        self.session = requests.Session()
        retry_strategy = Retry(
            total=3,
            backoff_factor=0.5,  # Меньший backoff для скорости
            status_forcelist=[429, 500, 502, 503, 504],
        )
        
        # КРИТИЧЕСКАЯ ОПТИМИЗАЦИЯ: connection pool размер для высокого параллелизма
        adapter = HTTPAdapter(
            max_retries=retry_strategy,
            pool_maxsize=50,  # Большой пул для 40+ потоков ресурсов
            pool_connections=40,  # Достаточно для высокого параллелизма
            pool_block=True  # Блокируем вместо fail'а
        )
        self.session.mount("http://", adapter)
        self.session.mount("https://", adapter)
        self.session.headers.update(self.headers)

        if self.respect_robots:
            self._init_robots()

        # Initialize OpenAI client if rewriting is enabled
        if self.rewrite_content:
            api_key = os.getenv('OPENAI_API_KEY')
            if api_key:
                self.openai_client = OpenAI(api_key=api_key, timeout=60.0)  # 60 секунд timeout на OpenAI запросы
                logging.info(f"🤖 AI rewriting ENABLED for language: {self.rewrite_language}")
                # Validate language exists
                if self.rewrite_language not in self.language_prompts:
                    logging.warning(f"⚠️ Language '{self.rewrite_language}' not found, defaulting to 'polish'")
                    self.rewrite_language = 'polish'
            else:
                logging.error("❌ OPENAI_API_KEY not found! AI rewriting DISABLED.")
                self.rewrite_content = False
        os.makedirs(self.output_dir, exist_ok=True)
        # Remove any existing stop file
        if self.stop_file and os.path.exists(self.stop_file):
            os.remove(self.stop_file)

    def _clean_url_smart(self, url):
        """Smart URL cleaning that preserves pagination query parameters but removes fragments"""
        if not url:
            return url
        
        # Always remove fragments (#)
        url_no_fragment = url.split('#')[0]
        
        # Parse URL to check query parameters
        parsed = urllib.parse.urlparse(url_no_fragment)
        if not parsed.query:
            return url_no_fragment
        
        # Pagination parameters to preserve - these are CRITICAL for crawling
        pagination_params = {
            'page', 'paged', 'offset', 'start', 'skip', 'from', 'begin',
            'p', 'pg', 'pagenum', 'pagenumber', 'page_id', 'pageId',
            'currentpage', 'current_page', 'page_no', 'pageno',
            'per_page', 'limit', 'size', 'count', 'max', 'num',
            'after', 'before', 'since', 'until', 'next', 'prev',
            'orderby', 'order', 'sort', 'sortby', 'sort_by',
            'filter', 'category', 'cat', 'tag', 'tags', 'type',
            'search', 'q', 'query', 's', 'keyword', 'term'
        }
        
        # Parse existing query parameters
        query_params = urllib.parse.parse_qs(parsed.query)
        
        # Keep only pagination-related parameters
        preserved_params = {}
        for param_name, param_values in query_params.items():
            param_lower = param_name.lower()
            
            # Check if parameter is pagination-related
            if any(page_param in param_lower for page_param in pagination_params):
                preserved_params[param_name] = param_values
                logging.debug(f"Preserving pagination parameter: {param_name}={param_values}")
        
        # Rebuild URL with only preserved parameters
        if preserved_params:
            preserved_query = urllib.parse.urlencode(preserved_params, doseq=True)
            cleaned_url = f"{parsed.scheme}://{parsed.netloc}{parsed.path}?{preserved_query}"
            logging.debug(f"Smart cleaned URL: {url} -> {cleaned_url}")
            return cleaned_url
        else:
            # No pagination parameters found, return URL without query string
            return f"{parsed.scheme}://{parsed.netloc}{parsed.path}"

    def _collect_all_links(self, soup, current_url):
        """Collect all internal links from a page including footer, header, navigation"""
        links = set()
        stats = {
            'regular_links': 0,
            'canonical_links': 0,
            'json_ld_links': 0,
            'meta_refresh_links': 0,
            'data_attribute_links': 0,
            'pagination_links': 0,
            'comment_links': 0
        }
        
        try:
            # Собираем ВСЕ ссылки на странице
            for link_tag in soup.find_all('a', href=True):
                href = link_tag.get('href')
                if not href:
                    continue

                # Пропускаем якоря, javascript, mailto, tel
                if (href.startswith('#') or href.startswith('javascript:') or
                    href.startswith('mailto:') or href.startswith('tel:')):
                    continue

                # Преобразуем относительные ссылки в абсолютные
                if href.startswith('//'):
                    href = 'https:' + href
                elif href.startswith('/'):
                    href = self.base_url + href
                elif not href.startswith('http'):
                    href = urllib.parse.urljoin(current_url, href)

                # Очищаем от фрагментов, но сохраняем pagination параметры
                clean_href = self._clean_url_smart(href)

                # Проверяем что это внутренняя ссылка используя единую логику
                if self._is_internal_url(clean_href) and clean_href != current_url:
                    links.add(clean_href)
                    stats['regular_links'] += 1
                    logging.debug(f"Found internal link: {clean_href}")

            # Дополнительно ищем ссылки в специфических элементах
            # Канонические ссылки
            for link_tag in soup.find_all('link', rel='canonical'):
                href = link_tag.get('href')
                if href:
                    # CRITICAL FIX: Normalize URL BEFORE checking if internal
                    if href.startswith('//'):
                        href = 'https:' + href
                    elif href.startswith('/'):
                        href = self.base_url + href
                    elif not href.startswith('http'):
                        href = urllib.parse.urljoin(current_url, href)
                    
                    # Now check if the normalized URL is internal
                    if self._is_internal_url(href):
                        clean_href = self._clean_url_smart(href)
                        links.add(clean_href)
                        stats['canonical_links'] += 1

            # Ссылки в JSON-LD структурированных данных
            for script_tag in soup.find_all('script', type='application/ld+json'):
                try:
                    import json
                    json_data = json.loads(script_tag.string or '')
                    # Рекурсивно ищем URL в JSON
                    def extract_urls(obj):
                        if isinstance(obj, dict):
                            for key, value in obj.items():
                                if key.lower() in ['url', 'link', 'href', '@id'] and isinstance(value, str):
                                    # CRITICAL FIX: Normalize URL BEFORE checking if internal
                                    normalized_value = value
                                    if value.startswith('//'):
                                        normalized_value = 'https:' + value
                                    elif value.startswith('/'):
                                        normalized_value = self.base_url + value
                                    elif not value.startswith('http'):
                                        normalized_value = urllib.parse.urljoin(current_url, value)
                                    
                                    # Now check if the normalized URL is internal
                                    if self._is_internal_url(normalized_value):
                                        clean_url = self._clean_url_smart(normalized_value)
                                        links.add(clean_url)
                                        stats['json_ld_links'] += 1
                                elif isinstance(value, (dict, list)):
                                    extract_urls(value)
                        elif isinstance(obj, list):
                            for item in obj:
                                extract_urls(item)

                    extract_urls(json_data)
                except:
                    pass

            # Meta refresh redirects - FIXED: case-insensitive parsing with regex
            for meta_tag in soup.find_all('meta', attrs={'http-equiv': 'refresh'}):
                content = meta_tag.get('content', '')
                if content:
                    try:
                        # Parse content like "0;url=http://example.com/page" or "0;URL=..." (case-insensitive)
                        match = re.search(r'url\s*=\s*([^;]+)', content, flags=re.IGNORECASE)
                        if match:
                            url_part = match.group(1).strip()
                            if url_part:
                                # Clean quotes and spaces
                                url_part = url_part.strip('"\' ')
                                # CRITICAL FIX: Normalize URL BEFORE checking if internal
                                if url_part.startswith('//'):
                                    url_part = 'https:' + url_part
                                elif url_part.startswith('/'):
                                    url_part = self.base_url + url_part
                                elif not url_part.startswith('http'):
                                    url_part = urllib.parse.urljoin(current_url, url_part)
                                
                                # Now check if the normalized URL is internal
                                if self._is_internal_url(url_part):
                                    clean_url = self._clean_url_smart(url_part)
                                    links.add(clean_url)
                                    stats['meta_refresh_links'] += 1
                                    logging.debug(f"Found meta refresh link: {clean_url}")
                    except Exception as e:
                        logging.debug(f"Error parsing meta refresh: {e}")

            # Data attributes with URLs (data-href, data-url, data-link, etc.)
            data_attrs = ['data-href', 'data-url', 'data-link', 'data-src', 'data-target', 
                         'data-goto', 'data-redirect', 'data-navigate', 'data-location']
            for attr in data_attrs:
                for element in soup.find_all(attrs={attr: True}):
                    href = element.get(attr)
                    if href and not href.startswith(('#', 'javascript:', 'mailto:', 'tel:')):
                        try:
                            if href.startswith('//'):
                                href = 'https:' + href
                            elif href.startswith('/'):
                                href = self.base_url + href
                            elif not href.startswith('http'):
                                href = urllib.parse.urljoin(current_url, href)
                            
                            if self._is_internal_url(href):
                                clean_href = self._clean_url_smart(href)
                                links.add(clean_href)
                                stats['data_attribute_links'] += 1
                                logging.debug(f"Found data attribute link ({attr}): {clean_href}")
                        except Exception as e:
                            logging.debug(f"Error processing data attribute {attr}: {e}")

            # Pagination links (next/prev and numbered)
            # Look for next/prev links
            for link_tag in soup.find_all(['a', 'link'], rel=True):
                rel_values = link_tag.get('rel', [])
                if isinstance(rel_values, str):
                    rel_values = [rel_values]
                
                if any(rel in ['next', 'prev', 'previous'] for rel in rel_values):
                    href = link_tag.get('href')
                    if href:
                        # CRITICAL FIX: Normalize URL BEFORE checking if internal
                        if href.startswith('//'):
                            href = 'https:' + href
                        elif href.startswith('/'):
                            href = self.base_url + href
                        elif not href.startswith('http'):
                            href = urllib.parse.urljoin(current_url, href)
                        
                        # Now check if the normalized URL is internal
                        if self._is_internal_url(href):
                            clean_href = self._clean_url_smart(href)
                            links.add(clean_href)
                            stats['pagination_links'] += 1
                            logging.debug(f"Found pagination link: {clean_href}")

            # Numbered pagination patterns
            pagination_patterns = [
                r'page[/_-]?\d+',  # page-2, page/3, page_4
                r'p\d+',  # p2, p3
                r'\d+/?$',  # ending with number
                r'page=[\d]+',  # ?page=2
                r'paged=[\d]+',  # ?paged=2 (WordPress)
                r'offset=[\d]+',  # ?offset=20
            ]
            
            for link_tag in soup.find_all('a', href=True):
                href = link_tag.get('href')
                if href:
                    # CRITICAL FIX: Normalize URL BEFORE checking if internal
                    normalized_href = href
                    if href.startswith('//'):
                        normalized_href = 'https:' + href
                    elif href.startswith('/'):
                        normalized_href = self.base_url + href
                    elif not href.startswith('http'):
                        normalized_href = urllib.parse.urljoin(current_url, href)
                    
                    # Now check if the normalized URL is internal
                    if self._is_internal_url(normalized_href):
                        # Check if link text or href contains pagination indicators
                        link_text = link_tag.get_text().strip().lower()
                        href_lower = normalized_href.lower()
                        
                        # Look for pagination indicators
                        pagination_indicators = ['next', 'prev', 'previous', 'more', 'continue', 'older', 'newer']
                        numeric_indicators = re.search(r'\b\d+\b', link_text)
                        
                        is_pagination = (
                            any(indicator in link_text for indicator in pagination_indicators) or
                            any(re.search(pattern, href_lower) for pattern in pagination_patterns) or
                            (numeric_indicators and len(link_text) < 20)  # Short text with number
                        )
                        
                        if is_pagination:
                            try:
                                clean_href = self._clean_url_smart(normalized_href)
                                links.add(clean_href)
                                stats['pagination_links'] += 1
                                logging.debug(f"Found numbered pagination link: {clean_href}")
                            except Exception as e:
                                logging.debug(f"Error processing pagination link: {e}")

            # HTML comments containing URLs
            from bs4 import Comment
            comments = soup.find_all(string=lambda text: isinstance(text, Comment))
            for comment in comments:
                comment_text = str(comment)
                # Look for URLs in comments using regex
                url_pattern = r'https?://[^\s<>"\')]+|/[^\s<>"\')]*'
                found_urls = re.findall(url_pattern, comment_text)
                
                for url in found_urls:
                    try:
                        if url.startswith('//'):
                            url = 'https:' + url
                        elif url.startswith('/'):
                            url = self.base_url + url
                        elif not url.startswith('http'):
                            url = urllib.parse.urljoin(current_url, url)
                        
                        if self._is_internal_url(url):
                            clean_url = self._clean_url_smart(url)
                            links.add(clean_url)
                            stats['comment_links'] += 1
                            logging.debug(f"Found comment URL: {clean_url}")
                    except Exception as e:
                        logging.debug(f"Error processing comment URL: {e}")

        except Exception as e:
            logging.warning(f"Error collecting links from {current_url}: {e}")

        # Update global statistics
        for key, value in stats.items():
            if key in self.link_discovery_stats:
                self.link_discovery_stats[key] += value

        # Log detailed breakdown for this page
        total_found = sum(stats.values())
        if total_found > 0:
            breakdown = ", ".join([f"{k}: {v}" for k, v in stats.items() if v > 0])
            logging.debug(f"Links from {current_url}: {total_found} total ({breakdown})")
        
        logging.debug(f"Collected {len(links)} unique links from {current_url}")
        return links

    def _get_sitemap_pages(self):
        """Get all pages from sitemap.xml files with timeout, enhanced with robots.txt discovery"""
        pages = set()
        
        # Start with common sitemap URLs
        sitemap_urls = [
            urllib.parse.urljoin(self.base_url, '/sitemap.xml'),
            urllib.parse.urljoin(self.base_url, '/sitemap_index.xml'),
            urllib.parse.urljoin(self.base_url, '/wp-sitemap.xml'),
            urllib.parse.urljoin(self.base_url, '/page-sitemap.xml'),
            urllib.parse.urljoin(self.base_url, '/post-sitemap.xml'),
            urllib.parse.urljoin(self.base_url, '/sitemap.xml.gz'),
            urllib.parse.urljoin(self.base_url, '/sitemap_index.xml.gz'),
            urllib.parse.urljoin(self.base_url, '/sitemaps.xml'),
            urllib.parse.urljoin(self.base_url, '/sitemap-index.xml'),
            urllib.parse.urljoin(self.base_url, '/robots.xml'),
            urllib.parse.urljoin(self.base_url, '/feeds/posts/default?alt=rss'),  # Blogger
            urllib.parse.urljoin(self.base_url, '/rss.xml'),  # Common RSS
            urllib.parse.urljoin(self.base_url, '/feed.xml'),  # Jekyll
            urllib.parse.urljoin(self.base_url, '/atom.xml'),  # Atom feed
        ]
        
        # Add sitemap URLs discovered from robots.txt
        robots_sitemaps = self._discover_sitemaps_from_robots()
        sitemap_urls.extend(robots_sitemaps)
        
        # Remove duplicates while preserving order
        seen = set()
        unique_sitemap_urls = []
        for url in sitemap_urls:
            if url not in seen:
                seen.add(url)
                unique_sitemap_urls.append(url)
        sitemap_urls = unique_sitemap_urls
        
        logging.info(f"Checking {len(sitemap_urls)} potential sitemap URLs")

        for sitemap_url in sitemap_urls:
            try:
                logging.info(f"Checking sitemap: {sitemap_url}")
                sitemap_resp = self.session.get(sitemap_url, timeout=10)
                if sitemap_resp.status_code == 200:
                    sitemap_soup = BeautifulSoup(sitemap_resp.text, 'xml')

                    # Handle sitemap index files
                    for sitemap_tag in sitemap_soup.find_all('sitemap'):
                        if isinstance(sitemap_tag, Tag):
                            loc_tag = sitemap_tag.find('loc')
                            if loc_tag and isinstance(loc_tag, Tag):
                                sub_sitemap_url = loc_tag.get_text().strip()
                                try:
                                    sub_resp = self.session.get(sub_sitemap_url, timeout=10)
                                    if sub_resp.status_code == 200:
                                        sub_soup = BeautifulSoup(sub_resp.text, 'xml')
                                        for loc_tag in sub_soup.find_all('loc'):
                                            if isinstance(loc_tag, Tag):
                                                page_url = loc_tag.get_text().strip()
                                                if self._is_internal_url(page_url):
                                                    # CRITICAL FIX: Filter out XML/RSS/feed files from being added as pages
                                                    if self._is_sitemap_or_feed_url(page_url):
                                                        continue
                                                    clean_url = self._clean_url_smart(page_url)
                                                    pages.add(clean_url)
                                except Exception as e:
                                    logging.debug(f"Failed sub-sitemap {sub_sitemap_url}: {e}")
                                    continue

                    # Handle regular sitemap files
                    for loc_tag in sitemap_soup.find_all('loc'):
                        if isinstance(loc_tag, Tag):
                            page_url = loc_tag.get_text().strip()
                            if self._is_internal_url(page_url):
                                # CRITICAL FIX: Filter out XML/RSS/feed files from being added as pages
                                if self._is_sitemap_or_feed_url(page_url):
                                    continue
                                clean_url = self._clean_url_smart(page_url)
                                pages.add(clean_url)

                    logging.info(f"Found {len(pages)} pages in sitemap {sitemap_url}")
            except Exception as e:
                logging.debug(f"Could not process sitemap {sitemap_url}: {e}")
                continue

        logging.info(f"Total pages discovered from sitemaps: {len(pages)}")
        return list(pages)

    def _discover_sitemaps_from_robots(self):
        """Parse robots.txt to find additional sitemap URLs"""
        sitemap_urls = []
        try:
            robots_url = urllib.parse.urljoin(self.base_url + '/', 'robots.txt')
            logging.info(f"Discovering sitemaps from robots.txt: {robots_url}")
            
            resp = self.session.get(robots_url, timeout=10)
            if resp.status_code == 200:
                robots_content = resp.text
                
                # Parse robots.txt for Sitemap: directives
                for line in robots_content.split('\n'):
                    line = line.strip()
                    if line.lower().startswith('sitemap:'):
                        sitemap_url = line.split(':', 1)[1].strip()
                        if sitemap_url:
                            # Resolve relative URLs
                            if sitemap_url.startswith('//'):
                                sitemap_url = 'https:' + sitemap_url
                            elif sitemap_url.startswith('/'):
                                sitemap_url = self.base_url + sitemap_url
                            elif not sitemap_url.startswith('http'):
                                sitemap_url = urllib.parse.urljoin(self.base_url + '/', sitemap_url)
                            
                            sitemap_urls.append(sitemap_url)
                            logging.info(f"Found sitemap in robots.txt: {sitemap_url}")
                            
                logging.info(f"Discovered {len(sitemap_urls)} sitemaps from robots.txt")
            else:
                logging.debug(f"robots.txt not accessible: HTTP {resp.status_code}")
                
        except Exception as e:
            logging.debug(f"Could not read robots.txt for sitemap discovery: {e}")
            
        return sitemap_urls

    def _is_sitemap_or_feed_url(self, url):
        """Check if a URL is a sitemap, RSS, or feed file that should not be crawled as a page"""
        url_lower = url.lower()
        
        # Common sitemap/feed file patterns
        feed_patterns = [
            'sitemap.xml', 'sitemap_index.xml', 'wp-sitemap', 'page-sitemap', 'post-sitemap',
            'sitemaps.xml', 'sitemap-index.xml', 'robots.xml',
            'rss.xml', 'feed.xml', 'atom.xml', 'feeds/', '/feed', '/rss',
            '.xml.gz', 'feed.rss', 'index.xml', 'news.xml'
        ]
        
        # Check if URL contains any feed/sitemap patterns
        for pattern in feed_patterns:
            if pattern in url_lower:
                return True
        
        # Check file extension
        parsed_url = urllib.parse.urlparse(url_lower)
        path = parsed_url.path
        
        # Skip XML files that are likely feeds/sitemaps
        if path.endswith('.xml') or path.endswith('.rss') or path.endswith('.atom'):
            return True
        
        # Skip feed query parameters
        if 'feed=' in url_lower or 'format=rss' in url_lower or 'alt=rss' in url_lower:
            return True
        
        return False

    def _log_discovery_statistics(self):
        """Log comprehensive link discovery statistics"""
        stats = self.link_discovery_stats
        
        logging.info("\n" + "="*60)
        logging.info("📊 COMPREHENSIVE LINK DISCOVERY STATISTICS")
        logging.info("="*60)
        
        # Overall discovery performance
        logging.info(f"🔍 Discovery Performance:")
        logging.info(f"   • Total unique pages found: {stats['total_unique_links']:,}")
        logging.info(f"   • Pages from sitemaps: {stats['sitemap_pages']:,}")
        logging.info(f"   • Pages from link discovery: {stats['total_unique_links'] - stats['sitemap_pages']:,}")
        logging.info(f"   • Discovery rounds completed: {stats['discovery_rounds']}")
        logging.info(f"   • Pages analyzed for links: {stats['pages_processed_for_links']:,}")
        
        # Link source breakdown
        total_links_found = sum([
            stats['regular_links'], stats['canonical_links'], stats['json_ld_links'],
            stats['meta_refresh_links'], stats['data_attribute_links'], 
            stats['pagination_links'], stats['comment_links']
        ])
        
        if total_links_found > 0:
            logging.info(f"\n🔗 Link Sources Breakdown ({total_links_found:,} total links found):")
            
            sources = [
                ('Regular <a> links', stats['regular_links']),
                ('Canonical links', stats['canonical_links']),
                ('JSON-LD structured data', stats['json_ld_links']),
                ('Meta refresh redirects', stats['meta_refresh_links']),
                ('Data attribute links', stats['data_attribute_links']),
                ('Pagination links', stats['pagination_links']),
                ('HTML comment links', stats['comment_links'])
            ]
            
            for source_name, count in sources:
                if count > 0:
                    percentage = (count / total_links_found) * 100
                    logging.info(f"   • {source_name}: {count:,} ({percentage:.1f}%)")
        
        # Discovery efficiency
        if stats['pages_processed_for_links'] > 0:
            avg_links_per_page = total_links_found / stats['pages_processed_for_links']
            logging.info(f"\n⚙️ Discovery Efficiency:")
            logging.info(f"   • Average links found per page: {avg_links_per_page:.1f}")
            
            if stats['sitemap_pages'] > 0:
                discovery_improvement = ((stats['total_unique_links'] - stats['sitemap_pages']) / stats['sitemap_pages']) * 100
                logging.info(f"   • Improvement over sitemap-only: +{discovery_improvement:.1f}%")
        
        logging.info("="*60 + "\n")

    def _generate_human_name(self, original_name, name_type="class"):
        """Generate human-readable CSS class or ID names"""
        adjectives = [
            'main', 'primary', 'secondary', 'active', 'hidden', 'visible', 'large', 'small',
            'top', 'bottom', 'left', 'right', 'center', 'full', 'half', 'wide', 'narrow',
            'light', 'dark', 'bright', 'bold', 'thin', 'thick', 'smooth', 'rough',
            'modern', 'classic', 'simple', 'complex', 'clean', 'elegant', 'basic'
        ]

        nouns = [
            'container', 'wrapper', 'content', 'section', 'header', 'footer', 'sidebar',
            'menu', 'nav', 'button', 'link', 'text', 'title', 'subtitle', 'image',
            'gallery', 'card', 'box', 'panel', 'widget', 'item', 'list', 'grid',
            'column', 'row', 'block', 'element', 'component', 'module', 'feature'
        ]

        hash_input = f"{self.base_url}_{original_name}_{name_type}"
        hash_value = hashlib.md5(hash_input.encode()).hexdigest()

        adj_index = int(hash_value[:4], 16) % len(adjectives)
        noun_index = int(hash_value[4:8], 16) % len(nouns)

        base_name = f"{adjectives[adj_index]}_{nouns[noun_index]}"

        counter = 0
        new_name = base_name
        while new_name in self.used_names:
            counter += 1
            new_name = f"{base_name}_{counter}"

        self.used_names.add(new_name)
        return new_name

    def _init_robots(self):
        try:
            self.robots = RobotFileParser()
            robots_url = urllib.parse.urljoin(self.base_url + '/', 'robots.txt')
            logging.info(f"Parsing robots.txt from {robots_url}")
            self.robots.set_url(robots_url)
            self.robots.read()
        except Exception as e:
            logging.warning(f"Could not read robots.txt: {e}, proceeding without it.")
            self.respect_robots = False

    def _url_to_local_path(self, url):
        """Convert URL to local file path with proper folder structure"""
        parsed_url = urllib.parse.urlparse(url)

        # Проверяем, является ли URL внешним
        is_external = not self._is_internal_url(url)
        
        if is_external:
            # Для внешних ресурсов создаем папку по домену
            domain = parsed_url.netloc.replace('www.', '').replace(':', '_')
            # Очищаем домен от недопустимых символов для безопасности
            domain = re.sub(r'[<>:"/\\|?*]', '_', domain)
            
            # БЕЗОПАСНАЯ обработка пути - защита от path traversal
            file_path = parsed_url.path.strip('/')
            if not file_path:
                file_path = 'index.html'
            
            # Разбираем путь на компоненты и очищаем от опасных элементов
            import pathlib
            try:
                # Удаляем опасные компоненты как ".." и нормализуем путь
                safe_path = pathlib.PurePosixPath(file_path)
                # Преобразуем в строку и убираем ведущие слеши
                file_path = str(safe_path).lstrip('/')
                
                # Запрещаем пути содержащие ".." после нормализации
                if '..' in file_path or file_path.startswith('/'):
                    # Используем безопасное имя файла на основе хеша
                    file_path = f"resource_{hashlib.md5(parsed_url.path.encode()).hexdigest()}"
            except:
                # Fallback на безопасное имя
                file_path = f"resource_{hashlib.md5(parsed_url.path.encode()).hexdigest()}"
            
            # Добавляем хеш query параметров чтобы избежать коллизий
            if parsed_url.query:
                query_hash = hashlib.md5(parsed_url.query.encode()).hexdigest()[:8]
                name, ext = os.path.splitext(file_path)
                file_path = f"{name}_{query_hash}{ext}"
            
            # НЕ добавляем .html к ресурсам - сохраняем оригинальное расширение
            # Если нет расширения, используем .bin как fallback
            if not os.path.splitext(file_path)[1]:
                file_path = file_path + '.bin'
                
            return f"external_resources/{domain}/{file_path}"

        # Для внутренних URL - обычная логика
        # Handle homepage
        if parsed_url.path in ['', '/']:
            return 'index.html'

        # Clean path
        path = parsed_url.path.strip('/')

        # Special handling for WordPress CSS/JS files with query parameters
        if '?' in url and (path.endswith('.css') or path.endswith('.js') or path.endswith('.png') or path.endswith('.jpg') or path.endswith('.webp') or path.endswith('.svg')):
            # Keep the original file extension, ignore query parameters for local path
            path = path.split('?')[0]
            return path

        # Handle trailing slash - convert to folder/index.html
        if path.endswith('/'):
            path = path.rstrip('/') + '/index.html'
        elif not '.' in os.path.basename(path):
            # No extension - treat as folder with index.html
            path = path + '/index.html'

        return path

    def _should_stop(self):
        """Check if scraping should stop"""
        if self.should_stop:
            return True
        if self.stop_file and os.path.exists(self.stop_file):
            self.should_stop = True
            logging.info(f"Stop flag detected, stopping scraping")
            return True
        return False
    
    def stop_scraping(self):
        """Request scraper to stop"""
        self.should_stop = True
        if self.stop_file:
            try:
                os.makedirs(os.path.dirname(self.stop_file), exist_ok=True)
                with open(self.stop_file, 'w') as f:
                    f.write('STOP')
                logging.info(f"Stop flag created: {self.stop_file}")
            except Exception as e:
                logging.error(f"Failed to create stop flag: {e}")

    def scrape(self):
        """Main scraping method with stop checks and timeouts"""
        try:
            start_time = time.time()
            max_runtime = 28800  # 8 hours max - for large AI rewriting jobs
            
            if self.status_callback:
                self.status_callback('running', 'Поиск страниц...', 5)

            # Check stop condition
            if self._should_stop():
                if self.status_callback:
                    self.status_callback('cancelled', 'Задача остановлена пользователем', 0)
                return {'status': 'cancelled', 'message': 'Задача остановлена пользователем'}

            # Get all pages from sitemap first with timeout
            all_pages = self._get_sitemap_pages()
            
            # Update sitemap pages statistics
            self.link_discovery_stats['sitemap_pages'] = len(all_pages)
            
            # Check runtime and stop condition
            if time.time() - start_time > max_runtime or self._should_stop():
                if self.status_callback:
                    self.status_callback('cancelled', 'Превышен максимальный лимит времени или задача остановлена', 0)
                return {'status': 'cancelled', 'message': 'Превышен максимальный лимит времени или задача остановлена'}

            # Start with homepage and add sitemap pages
            pages_to_process = [self.base_url]
            for page in all_pages:
                if page.rstrip('/') != self.base_url.rstrip('/'):
                    pages_to_process.append(page)

            # Check stop condition before link discovery
            if self._should_stop():
                if self.status_callback:
                    self.status_callback('cancelled', 'Задача остановлена пользователем', 0)
                return {'status': 'cancelled', 'message': 'Задача остановлена пользователем'}

            # Comprehensive multi-pass link discovery with breadth-first approach
            discovered_pages = set(pages_to_process)
            processed_for_links = set()  # Track which pages we've processed for link extraction
            
            max_link_discovery_pages = 2000  # Увеличиваем лимит обнаружения
            max_discovery_rounds = 3  # Меньше rounds для скорости
            min_new_links_threshold = 5  # Minimum new links to continue another round
            
            discovery_round = 0
            total_processed_for_links = 0
            
            logging.info(f"Starting comprehensive multi-pass link discovery from {len(discovered_pages)} initial pages")
            
            while discovery_round < max_discovery_rounds and total_processed_for_links < max_link_discovery_pages:
                discovery_round += 1
                round_start_count = len(discovered_pages)
                
                # Get unprocessed pages for this round (breadth-first)
                unprocessed_pages = [page for page in discovered_pages if page not in processed_for_links]
                
                if not unprocessed_pages:
                    logging.info(f"No more unprocessed pages for link discovery after round {discovery_round - 1}")
                    break
                
                # БЕЗОПАСНЫЙ ускоренный batch sizing 
                if discovery_round == 1:
                    batch_size = min(300, len(unprocessed_pages))  # First round: умеренно-агрессивно
                elif discovery_round <= 3:
                    batch_size = min(200, len(unprocessed_pages))  # Early rounds: умеренно
                else:
                    batch_size = min(100, len(unprocessed_pages))   # Later rounds: консервативно
                
                current_batch = unprocessed_pages[:batch_size]
                logging.info(f"Discovery round {discovery_round}: processing {len(current_batch)} pages for links")
                
                batch_new_links = 0
                for i, page_url in enumerate(current_batch):
                    # Check stop condition and runtime
                    if time.time() - start_time > max_runtime or self._should_stop():
                        logging.info(f"Stopping link collection: timeout or stop requested")
                        break
                    
                    if total_processed_for_links >= max_link_discovery_pages:
                        logging.info(f"Reached maximum link discovery limit ({max_link_discovery_pages})")
                        break
                        
                    try:
                        resp = self.session.get(page_url, timeout=15)
                        if resp.status_code == 200:
                            soup = BeautifulSoup(resp.text, 'html.parser')
                            page_links = self._collect_all_links(soup, page_url)
                            
                            # Count new links found
                            new_links = page_links - discovered_pages
                            if new_links:
                                batch_new_links += len(new_links)
                                discovered_pages.update(page_links)
                                logging.debug(f"Found {len(new_links)} new links from {page_url}")
                            
                        processed_for_links.add(page_url)
                        total_processed_for_links += 1
                        
                    except Exception as e:
                        logging.debug(f"Failed to collect links from {page_url}: {e}")
                        processed_for_links.add(page_url)  # Mark as processed even if failed
                        continue
                    
                    # Update progress during link collection
                    if i % 20 == 0 and self.status_callback:
                        progress = 5 + (total_processed_for_links / max_link_discovery_pages) * 5
                        self.status_callback('running', 
                                           f'Раунд {discovery_round}: обработано {i+1}/{len(current_batch)} страниц', 
                                           min(progress, 10))
                
                round_end_count = len(discovered_pages)
                round_new_links = round_end_count - round_start_count
                
                logging.info(f"Round {discovery_round} complete: found {round_new_links} new links (total: {round_end_count})")
                
                # Check if we should continue to next round
                if round_new_links < min_new_links_threshold:
                    logging.info(f"Discovery stopping: only {round_new_links} new links found (threshold: {min_new_links_threshold})")
                    break
                    
                # Check stop conditions after each round
                if time.time() - start_time > max_runtime or self._should_stop():
                    logging.info(f"Discovery stopping: timeout or stop requested")
                    break
            
            # Final statistics
            final_count = len(discovered_pages)
            discovery_improvement = final_count - len(pages_to_process)
            logging.info(f"Multi-pass discovery complete: {discovery_round} rounds, "
                        f"{total_processed_for_links} pages analyzed, "
                        f"{discovery_improvement} additional pages discovered")
            
            # Update final discovery statistics
            self.link_discovery_stats['total_unique_links'] = final_count
            self.link_discovery_stats['discovery_rounds'] = discovery_round
            self.link_discovery_stats['pages_processed_for_links'] = total_processed_for_links
            
            # Update pages to process
            pages_to_process = list(discovered_pages)

            # Apply reasonable limits with prioritization
            if len(pages_to_process) > 2000:
                logging.warning(f"Found {len(pages_to_process)} pages, applying intelligent limiting to 2000")
                
                # Prioritize pages: sitemap pages first, then homepage, then others
                sitemap_pages = [p for p in pages_to_process if p in all_pages]
                homepage_and_main = [p for p in pages_to_process if p == self.base_url or 'index' in p.lower()]
                other_pages = [p for p in pages_to_process if p not in sitemap_pages and p not in homepage_and_main]
                
                # Combine with prioritization
                prioritized_pages = list(dict.fromkeys(sitemap_pages + homepage_and_main + other_pages))  # Remove duplicates while preserving order
                pages_to_process = prioritized_pages[:2000]
                
                logging.info(f"Prioritized pages: {len(sitemap_pages)} from sitemap, "
                           f"{len(homepage_and_main)} main pages, "
                           f"{len(pages_to_process) - len(sitemap_pages) - len(homepage_and_main)} others")

            self.total_pages = len(pages_to_process)
            logging.info(f"🎯 Final page collection: {self.total_pages} pages to download")
            
            # Log comprehensive discovery statistics
            self._log_discovery_statistics()
            
            # Log discovery statistics summary
            sitemap_count = len([p for p in pages_to_process if p in all_pages])
            logging.info(f"📊 Page sources: {sitemap_count} from sitemaps, "
                        f"{self.total_pages - sitemap_count} from link discovery")

            # Download pages
            if self.status_callback:
                self.status_callback('running', f'Скачивание {self.total_pages} страниц...', 10)

            # Check stop condition before downloading
            if self._should_stop():
                if self.status_callback:
                    self.status_callback('cancelled', 'Задача остановлена пользователем', 0)
                return {'status': 'cancelled', 'message': 'Задача остановлена пользователем'}

            download_result = self._download_pages(pages_to_process, start_time, max_runtime)
            if download_result and download_result.get('status') == 'cancelled':
                return download_result

            # Check stop condition before downloading resources
            if self._should_stop():
                if self.status_callback:
                    self.status_callback('cancelled', 'Задача остановлена пользователем', 0)
                return {'status': 'cancelled', 'message': 'Задача остановлена пользователем'}

            # Download resources
            if self.status_callback:
                self.status_callback('running', 'Скачивание ресурсов...', 50)

            self._download_resources()

            # Check stop condition before URL conversion
            if self._should_stop():
                if self.status_callback:
                    self.status_callback('cancelled', 'Задача остановлена пользователем', 0)
                return {'status': 'cancelled', 'message': 'Задача остановлена пользователем'}

            # Convert URLs
            if self.status_callback:
                self.status_callback('running', 'Конвертация ссылок...', 70)

            self._convert_urls_to_local()

            # Check stop condition before AI rewriting
            if self._should_stop():
                if self.status_callback:
                    self.status_callback('cancelled', 'Задача остановлена пользователем', 0)
                return {'status': 'cancelled', 'message': 'Задача остановлена пользователем'}

            # Apply AI rewriting if enabled
            if self.rewrite_content:
                if self.status_callback:
                    self.status_callback('running', 'Переписывание текстов с AI...', 85)
                ai_result = self._rewrite_content_with_ai(start_time, max_runtime)
                if ai_result and ai_result.get('status') == 'cancelled':
                    return ai_result

            if self.status_callback:
                self.status_callback('running', 'Завершение...', 95)

            logging.info(f"Scraping complete. Processed {self.processed_pages} pages")
            
            # Return success status
            return {'status': 'completed', 'message': 'Скрапинг завершен успешно'}

        except Exception as e:
            logging.error(f"Critical error in scrape(): {e}")
            if self.status_callback:
                self.status_callback('error', f'Ошибка: {str(e)}', 0)
            return {'status': 'error', 'message': f'Ошибка: {str(e)}'}

    def _download_pages(self, pages_to_process, start_time, max_runtime):
        """Download pages with parallel processing and stop checks"""
        with ThreadPoolExecutor(max_workers=self.concurrency) as executor:
            future_to_url = {}

            for url in pages_to_process:
                # Check stop condition and runtime before submitting each task
                if time.time() - start_time > max_runtime or self._should_stop():
                    logging.info("Stopping page downloads due to timeout or stop request")
                    if self.status_callback:
                        self.status_callback('cancelled', 'Задача остановлена пользователем', 0)
                    return {'status': 'cancelled', 'message': 'Задача остановлена пользователем'}
                
                if url in self.visited:
                    continue
                self.visited.add(url)
                future = executor.submit(self._download_single_page, url)
                future_to_url[future] = url

            for future in as_completed(future_to_url):
                # Check stop condition on each completed task
                if time.time() - start_time > max_runtime or self._should_stop():
                    logging.info("Stopping page downloads due to timeout or stop request")
                    if self.status_callback:
                        self.status_callback('cancelled', 'Задача остановлена пользователем', 0)
                    return {'status': 'cancelled', 'message': 'Задача остановлена пользователем'}
                
                url = future_to_url[future]
                try:
                    success = future.result(timeout=30)
                    if success:
                        self.processed_pages += 1
                        logging.info(f"✅ Downloaded {url} ({self.processed_pages}/{self.total_pages})")
                    else:
                        self.failed_pages += 1
                        logging.warning(f"❌ Failed to download {url}")
                except Exception as e:
                    self.failed_pages += 1
                    logging.error(f"❌ Error downloading {url}: {e}")

                # Update progress
                total_processed = self.processed_pages + self.failed_pages
                progress = 10 + (total_processed / self.total_pages) * 40
                if self.status_callback:
                    self.status_callback('running', f'Обработано {total_processed}/{self.total_pages} страниц', progress)
        
        return {'status': 'completed', 'message': 'Загрузка страниц завершена'}

    def _download_single_page(self, url):
        """Download a single page safely"""
        try:
            time.sleep(random.uniform(*self.delay))

            resp = self.session.get(url, timeout=20)
            resp.raise_for_status()

            # Fix encoding
            if resp.encoding == 'ISO-8859-1':
                resp.encoding = resp.apparent_encoding or 'utf-8'
            elif not resp.encoding:
                resp.encoding = 'utf-8'

            soup = BeautifulSoup(resp.text, 'html.parser')

            # Collect resources from this page
            self._collect_resources(soup, url)

            # Collect additional links from this page for future processing
            page_links = self._collect_all_links(soup, url)
            for link in page_links:
                if link not in self.visited and len(self.visited) < 1000:
                    # Добавляем новые найденные ссылки в очередь
                    logging.debug(f"Found new link to process: {link}")

            # Save the page
            self._save_page(url, soup, resp.text)

            return True

        except Exception as e:
            logging.error(f"Failed to download {url}: {e}")
            return False

    def _collect_resources(self, soup, current_url):
        """Collect all resources from a page"""
        try:
            # CSS files - СКАЧИВАЕМ ВСЕ CSS ФАЙЛЫ (внутренние и внешние)
            for link_tag in soup.find_all('link', rel='stylesheet'):
                href = link_tag.get('href')
                if href and not href.startswith('data:'):
                    if href.startswith('//'):
                        href = 'https:' + href
                    elif href.startswith('/'):
                        href = self.base_url + href

                    full_url = urllib.parse.urljoin(current_url, href)
                    # УБИРАЕМ проверку _is_internal_url - скачиваем ВСЕ CSS
                    if full_url.startswith('http'):  # Только валидные URL
                        self.resources.add(full_url)

            # JS files - СКАЧИВАЕМ ВСЕ JS ФАЙЛЫ (внутренние и внешние)
            for script_tag in soup.find_all('script', src=True):
                src = script_tag.get('src')
                if src and not src.startswith('data:'):
                    full_url = urllib.parse.urljoin(current_url, src)
                    # УБИРАЕМ проверку _is_internal_url - скачиваем ВСЕ JS
                    if full_url.startswith('http'):  # Только валидные URL
                        self.resources.add(full_url)

            # Images (включая srcset, data-src и другие атрибуты) - СКАЧИВАЕМ ВСЕ ИЗОБРАЖЕНИЯ
            for img_tag in soup.find_all('img'):
                # Обычный src
                src = img_tag.get('src')
                if src and not src.startswith('data:') and src.strip():
                    full_url = urllib.parse.urljoin(current_url, src)
                    # УБИРАЕМ проверку _is_internal_url - скачиваем ВСЕ изображения
                    if full_url.startswith('http'):  # Только валидные URL
                        self.resources.add(full_url)

                # srcset для адаптивных изображений
                srcset = img_tag.get('srcset')
                if srcset:
                    for src_item in srcset.split(','):
                        src_url = src_item.strip().split(' ')[0]
                        if src_url and not src_url.startswith('data:') and src_url.strip():
                            full_url = urllib.parse.urljoin(current_url, src_url)
                            # УБИРАЕМ проверку _is_internal_url - скачиваем ВСЕ изображения
                            if full_url.startswith('http'):  # Только валидные URL
                                self.resources.add(full_url)

                # Lazy loading изображения
                for attr in ['data-src', 'data-original', 'data-lazy']:
                    data_src = img_tag.get(attr)
                    if data_src and not data_src.startswith('data:') and data_src.strip():
                        full_url = urllib.parse.urljoin(current_url, data_src)
                        # УБИРАЕМ проверку _is_internal_url - скачиваем ВСЕ изображения
                        if full_url.startswith('http'):  # Только валидные URL
                            self.resources.add(full_url)

            # Фоновые изображения в CSS - СКАЧИВАЕМ ВСЕ
            for element in soup.find_all(style=True):
                style = element.get('style', '')
                if 'background-image:' in style or 'background:' in style:
                    import re
                    urls = re.findall(r'url\(["\']?([^"\']+)["\']?\)', style)
                    for url in urls:
                        if not url.startswith('data:') and url.strip():
                            full_url = urllib.parse.urljoin(current_url, url)
                            # Проверяем что это изображение по расширению
                            if any(ext in full_url.lower() for ext in ['.jpg', '.jpeg', '.png', '.gif', '.webp', '.svg', '.bmp', '.ico']):
                                if full_url.startswith('http'):  # Только валидные URL
                                    self.resources.add(full_url)

            # Видео и аудио файлы - СКАЧИВАЕМ ВСЕ
            for media_tag in soup.find_all(['video', 'audio']):
                src = media_tag.get('src')
                if src and not src.startswith('data:'):
                    full_url = urllib.parse.urljoin(current_url, src)
                    # УБИРАЕМ проверку _is_internal_url - скачиваем ВСЕ медиа
                    if full_url.startswith('http'):  # Только валидные URL
                        self.resources.add(full_url)

                # Source теги внутри video/audio
                for source_tag in media_tag.find_all('source'):
                    src = source_tag.get('src')
                    if src and not src.startswith('data:'):
                        full_url = urllib.parse.urljoin(current_url, src)
                        # УБИРАЕМ проверку _is_internal_url - скачиваем ВСЕ медиа
                        if full_url.startswith('http'):  # Только валидные URL
                            self.resources.add(full_url)

            # Шрифты - СКАЧИВАЕМ ВСЕ
            for link_tag in soup.find_all('link'):
                href = link_tag.get('href')
                if href and any(ext in href.lower() for ext in ['.woff', '.woff2', '.ttf', '.otf', '.eot']):
                    full_url = urllib.parse.urljoin(current_url, href)
                    # УБИРАЕМ проверку _is_internal_url - скачиваем ВСЕ шрифты
                    if full_url.startswith('http'):  # Только валидные URL
                        self.resources.add(full_url)

        except Exception as e:
            logging.warning(f"Error collecting resources from {current_url}: {e}")

    def _remove_tracking_scripts(self, soup):
        """Удаляет трекинг-пиксели и аналитику из HTML"""
        tracking_patterns = [
            # Google
            'googletagmanager.com', 'gtag', 'gtm.js', 'analytics.js', 'ga.js',
            'google-analytics.com', 'googleadservices.com', 'googlesyndication.com',
            'doubleclick.net', 'googleads.g.doubleclick.net',
            # Facebook
            'facebook.net', 'fbevents.js', 'fbq(', 'connect.facebook.net',
            # Yandex
            'mc.yandex.ru', 'metrika', 'yandex.ru/metrika',
            # Other trackers
            'hotjar.com', 'clarity.ms', 'mouseflow.com', 'fullstory.com',
            'mixpanel.com', 'segment.com', 'amplitude.com', 'heap.io',
            'intercom.io', 'crisp.chat', 'tawk.to', 'livechatinc.com',
            'pixel', 'tracking', 'analytics'
        ]
        
        removed_count = 0
        
        # Удаляем скрипты по src
        for script in soup.find_all('script'):
            src = script.get('src', '')
            script_text = script.string or ''
            
            should_remove = False
            
            # Проверяем src
            if src:
                src_lower = src.lower()
                for pattern in tracking_patterns:
                    if pattern in src_lower:
                        should_remove = True
                        break
            
            # Проверяем содержимое скрипта
            if not should_remove and script_text:
                text_lower = script_text.lower()
                for pattern in ['gtag(', 'fbq(', 'ga(', '_gaq', 'ym(', 'dataLayer']:
                    if pattern in text_lower:
                        should_remove = True
                        break
            
            if should_remove:
                script.decompose()
                removed_count += 1
        
        # Удаляем noscript с трекингом (часто содержат пиксели-картинки)
        for noscript in soup.find_all('noscript'):
            noscript_text = str(noscript).lower()
            for pattern in tracking_patterns:
                if pattern in noscript_text:
                    noscript.decompose()
                    removed_count += 1
                    break
        
        # Удаляем iframe с трекингом
        for iframe in soup.find_all('iframe'):
            src = iframe.get('src', '').lower()
            for pattern in tracking_patterns:
                if pattern in src:
                    iframe.decompose()
                    removed_count += 1
                    break
        
        # Удаляем img пиксели (1x1 изображения для трекинга)
        for img in soup.find_all('img'):
            src = img.get('src', '').lower()
            width = img.get('width', '')
            height = img.get('height', '')
            
            # Проверяем на пиксель-трекеры (1x1 изображения)
            if (width == '1' and height == '1') or (width == '0' and height == '0'):
                for pattern in tracking_patterns:
                    if pattern in src:
                        img.decompose()
                        removed_count += 1
                        break
        
        if removed_count > 0:
            logging.info(f"🧹 Removed {removed_count} tracking elements")
        
        return soup

    def _save_page(self, url, soup, content):
        """Save a page to disk"""
        try:
            # Удаляем трекинг-скрипты перед сохранением
            soup = self._remove_tracking_scripts(soup)
            content = str(soup)
            
            local_path = self._url_to_local_path(url)
            file_path = os.path.join(self.output_dir, local_path)

            # Create directory
            os.makedirs(os.path.dirname(file_path), exist_ok=True)

            # Save file
            with open(file_path, 'w', encoding='utf-8', errors='replace') as f:
                f.write(content)

            # Track downloaded URL for validation during conversion
            self.downloaded_urls.add(url.rstrip('/'))
            # Also track clean URL without fragments but keep pagination parameters
            clean_url = self._clean_url_smart(url)
            self.downloaded_urls.add(clean_url.rstrip('/'))

            # Store for later processing
            self.downloaded_pages.append({
                'url': url,
                'local_path': local_path,
                'soup': soup
            })

        except Exception as e:
            logging.error(f"Failed to save {url}: {e}")
            raise

    def _download_resources(self):
        """БЫСТРОЕ скачивание ресурсов - высокий параллелизм + retry"""
        unique_resources = list(self.resources)
        logging.info(f"📦 Downloading {len(unique_resources)} resources with HIGH concurrency")

        if len(unique_resources) > 3000:
            logging.warning(f"Too many resources ({len(unique_resources)}), limiting to 3000")
            unique_resources = unique_resources[:3000]

        processed = 0
        failed_resources = []
        
        # ВЫСОКИЙ параллелизм для ресурсов - до 40 потоков!
        max_workers = min(40, max(20, self.concurrency))
        logging.info(f"🚀 Using {max_workers} parallel workers for resources")
        
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            future_to_url = {}

            for resource_url in unique_resources:
                referrer = self.base_url
                future = executor.submit(self._download_single_resource, resource_url, referrer)
                future_to_url[future] = resource_url

            for future in as_completed(future_to_url):
                resource_url = future_to_url[future]
                try:
                    success = future.result(timeout=60)
                    if success:
                        logging.debug(f"✅ Resource downloaded: {resource_url}")
                    else:
                        failed_resources.append(resource_url)
                    processed += 1
                except Exception as e:
                    failed_resources.append(resource_url)
                    logging.debug(f"❌ Resource failed: {resource_url}: {e}")
                    processed += 1

                if self.status_callback and processed % 10 == 0:
                    progress = 50 + (processed / len(unique_resources)) * 20
                    self.status_callback('running', f'Ресурсы: {processed}/{len(unique_resources)}', progress)

        # ФИНАЛЬНЫЙ ПРОХОД - retry для неудачных ресурсов
        if failed_resources:
            logging.info(f"🔄 Retrying {len(failed_resources)} failed resources...")
            retry_success = 0
            still_failed = []
            
            for resource_url in failed_resources:
                if self._download_single_resource(resource_url, self.base_url):
                    retry_success += 1
                else:
                    still_failed.append(resource_url)
            
            if retry_success > 0:
                logging.info(f"✅ Recovered {retry_success} resources on retry")
            
            self.failed_resources = set(still_failed)
        else:
            self.failed_resources = set()
        
        if self.failed_resources:
            logging.info(f"⚠️ {len(self.failed_resources)} ресурсов не удалось скачать")
        else:
            logging.info(f"✅ Все ресурсы успешно скачаны!")

    def _download_single_resource(self, url, referrer=None):
        """Download a single resource with RETRY + BACKOFF - БЕЗ ПАУЗ для скорости"""
        max_retries = 3
        backoff_delays = [0.4, 0.8, 1.6]  # Экспоненциальный backoff
        
        for attempt in range(max_retries):
            try:
                # SSRF защита
                import ipaddress
                from urllib.parse import urlparse
                try:
                    parsed = urlparse(url)
                    ip = ipaddress.ip_address(parsed.hostname)
                    if ip.is_private or ip.is_loopback or ip.is_link_local:
                        logging.warning(f"Skipping private IP: {url}")
                        return False
                except (ValueError, AttributeError):
                    pass
                
                # Подготавливаем headers
                headers = {}
                if referrer:
                    headers['Referer'] = referrer
                
                # Accept headers по типу
                if url.lower().endswith(('.jpg', '.jpeg', '.png', '.gif', '.webp', '.svg', '.ico')):
                    headers['Accept'] = 'image/webp,image/apng,image/*,*/*;q=0.8'
                elif url.lower().endswith('.css'):
                    headers['Accept'] = 'text/css,*/*;q=0.1'
                elif url.lower().endswith('.js'):
                    headers['Accept'] = '*/*'
                elif url.lower().endswith(('.woff', '.woff2', '.ttf', '.otf', '.eot')):
                    headers['Accept'] = 'application/font-woff2,application/font-woff,font/*,*/*;q=0.8'
                
                # БЕЗ ПАУЗ - максимальная скорость для ресурсов!
                resp = self.session.get(url, timeout=30, headers=headers)
                
                # Для 404/410 - не ретраить, ресурс не существует
                if resp.status_code in [404, 410]:
                    logging.debug(f"Resource not found (permanent): {url}")
                    return False
                
                resp.raise_for_status()

                local_path = self._url_to_local_path(url)
                
                # Исправляем расширение на основе Content-Type
                if not self._is_internal_url(url):
                    content_type = resp.headers.get('content-type', '').lower()
                    if content_type.startswith('image/') and local_path.endswith('.bin'):
                        if 'jpeg' in content_type or 'jpg' in content_type:
                            local_path = local_path.replace('.bin', '.jpg')
                        elif 'png' in content_type:
                            local_path = local_path.replace('.bin', '.png')
                        elif 'webp' in content_type:
                            local_path = local_path.replace('.bin', '.webp')
                        elif 'gif' in content_type:
                            local_path = local_path.replace('.bin', '.gif')
                        elif 'svg' in content_type:
                            local_path = local_path.replace('.bin', '.svg')
                
                file_path = os.path.join(self.output_dir, local_path)
                os.makedirs(os.path.dirname(file_path), exist_ok=True)

                with open(file_path, 'wb') as f:
                    f.write(resp.content)

                # Отслеживаем CSS файлы
                if url.lower().endswith('.css') or 'text/css' in resp.headers.get('content-type', ''):
                    self.downloaded_css_files.append({
                        'url': url,
                        'local_path': local_path
                    })

                # Добавляем в manifest успешных загрузок
                self.downloaded_urls.add(url)
                return True

            except Exception as e:
                error_str = str(e).lower()
                
                # 5xx ошибки и timeout - ретраим
                if attempt < max_retries - 1:
                    if '500' in error_str or '502' in error_str or '503' in error_str or '504' in error_str or 'timeout' in error_str:
                        logging.debug(f"Retry {attempt + 1}/{max_retries} for {url}: {e}")
                        time.sleep(backoff_delays[attempt])
                        continue
                
                logging.debug(f"Failed to download resource after {attempt + 1} attempts: {url}: {e}")
                return False
        
        return False

    def _is_internal_url(self, url):
        """
        Enhanced URL detection that properly identifies internal links with:
        - www/non-www variations
        - http/https protocol differences
        - trailing slashes
        - URL parameters and fragments
        """
        try:
            if not url or url.startswith(('#', 'javascript:', 'mailto:', 'tel:', 'data:')):
                return False
            
            # Normalize the URL for comparison
            if url.startswith('//'):
                url = 'https:' + url
            elif url.startswith('/'):
                return True  # Root-relative URLs are always internal
            elif not url.startswith('http'):
                return True  # Relative URLs are internal
            
            # Parse both URLs for domain comparison
            base_parsed = urllib.parse.urlparse(self.base_url)
            url_parsed = urllib.parse.urlparse(url)
            
            # Normalize domains (remove www prefix for comparison)
            base_domain = base_parsed.netloc.lower()
            url_domain = url_parsed.netloc.lower()
            
            if base_domain.startswith('www.'):
                base_domain = base_domain[4:]
            if url_domain.startswith('www.'):
                url_domain = url_domain[4:]
            
            # Check if domains match (including subdomains of the same domain)
            if url_domain == base_domain or url_domain.endswith('.' + base_domain):
                return True
            
            # Additional check: if original domain had www, also check with www
            if not base_parsed.netloc.startswith('www.'):
                www_base_domain = 'www.' + base_domain
                if url_domain == www_base_domain:
                    return True
            
            return False
            
        except Exception as e:
            logging.debug(f"Error checking internal URL {url}: {e}")
            return False

    def _url_exists_locally(self, url):
        """
        Check if a URL has been downloaded and exists as a local file.
        This prevents broken links from subdomain pages that weren't actually downloaded.
        Теперь также проверяет внешние ресурсы.
        """
        try:
            if not url or url.startswith(('#', 'javascript:', 'mailto:', 'tel:', 'data:')):
                return False
            
            # Convert to absolute URL first
            if url.startswith('//'):
                full_url = 'https:' + url
            elif url.startswith('/'):
                full_url = self.base_url + url
            elif not url.startswith('http'):
                # For relative URLs, we need current page context
                return True  # Assume relative URLs are safe for now
            else:
                full_url = url
            
            # Clean URL for comparison but keep pagination parameters
            clean_url = self._clean_url_smart(full_url).rstrip('/')
            
            # Check if URL is in downloaded URLs (для страниц)
            if clean_url in self.downloaded_urls:
                return True
                
            # Check if URL is in resources (для внешних ресурсов)
            if full_url in self.resources:
                return True
                
            # Проверяем существование файла в файловой системе
            try:
                local_path = self._url_to_local_path(full_url)
                file_path = os.path.join(self.output_dir, local_path)
                # Дополнительная проверка безопасности пути
                resolved_path = os.path.realpath(file_path)  # Используем realpath для лучшей защиты
                output_abs = os.path.realpath(self.output_dir)
                if resolved_path.startswith(output_abs):
                    return os.path.exists(file_path)
                else:
                    logging.warning(f"Unsafe path detected: {file_path}")
                    return False
            except:
                return False
            
        except Exception as e:
            logging.debug(f"Error checking local URL existence {url}: {e}")
            return False

    def _convert_urls_to_local(self):
        """Convert all URLs to local links in HTML files with enhanced detection"""
        logging.info("Converting URLs to local links with enhanced detection...")
        total_conversions = 0

        # Process each page and convert URLs
        for page_data in self.downloaded_pages:
            try:
                file_path = os.path.join(self.output_dir, page_data['local_path'])
                page_conversions = 0

                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()

                soup = BeautifulSoup(content, 'html.parser')

                # Calculate relative path prefix
                path_parts = page_data['local_path'].split('/')
                if len(path_parts) > 1:
                    depth = len(path_parts) - 1
                else:
                    depth = 0
                relative_prefix = '../' * depth

                def convert_url_to_local(url, attribute_name=""):
                    """Helper function to convert URL to local path with validation"""
                    nonlocal page_conversions
                    
                    if not url or url.startswith(('#', 'javascript:', 'mailto:', 'tel:', 'data:')):
                        return url
                    
                    original_url = url
                    
                    # Extract and preserve fragment (anchor) if present
                    fragment = ''
                    if '#' in url:
                        url_part, fragment = url.split('#', 1)
                        fragment = '#' + fragment
                    else:
                        url_part = url
                    
                    # Handle different URL types - ПРОВЕРЯЕМ ВСЕ URL (внутренние И внешние)
                    full_url_to_check = url_part
                    if url_part.startswith('//'):
                        full_url_to_check = 'https:' + url_part
                    elif url_part.startswith('/'):
                        full_url_to_check = self.base_url + url_part
                    elif not url_part.startswith('http'):
                        full_url_to_check = urllib.parse.urljoin(page_data['url'], url_part)
                    
                    # Проверяем был ли этот URL скачан (внутренний ИЛИ внешний)
                    # НО если скачать не удалось - оставляем оригинальный URL
                    if full_url_to_check in self.failed_resources:
                        # Ресурс не удалось скачать - оставляем оригинальный URL
                        return original_url
                    elif self._is_internal_url(url_part) or full_url_to_check in self.resources:
                        # Validate that the URL actually exists locally to prevent broken links
                        if not self._url_exists_locally(url_part) and full_url_to_check not in self.resources:
                            logging.debug(f"⚠️ Skipping conversion - URL not downloaded: {original_url}")
                            return url  # Keep original URL if not downloaded locally
                        
                        try:
                            # Convert to absolute URL first
                            if url_part.startswith('//'):
                                full_url = 'https:' + url_part
                            elif url_part.startswith('/'):
                                full_url = self.base_url + url_part
                            elif not url_part.startswith('http'):
                                full_url = urllib.parse.urljoin(page_data['url'], url_part)
                            else:
                                full_url = url_part
                            
                            # Remove parameters for local path calculation but keep clean URL
                            clean_url = full_url.split('?')[0]
                            local_path = self._url_to_local_path(clean_url)
                            
                            # Use os.path.relpath for accurate relative paths instead of manual ../
                            current_dir = os.path.dirname(page_data['local_path'])
                            if current_dir:
                                converted_url = os.path.relpath(local_path, current_dir).replace('\\', '/')
                            else:
                                converted_url = local_path
                            
                            # Restore fragment if it existed
                            converted_url += fragment
                            
                            page_conversions += 1
                            logging.debug(f"✅ Converted {attribute_name}: {original_url} -> {converted_url}")
                            return converted_url
                            
                        except Exception as e:
                            logging.warning(f"Failed to convert URL {original_url}: {e}")
                            return url
                    
                    return url

                # Convert all href attributes (a, link, area tags)
                for tag in soup.find_all(['a', 'link', 'area'], href=True):
                    if isinstance(tag, Tag) and 'href' in tag.attrs:
                        original_href = tag['href']
                        if isinstance(original_href, str):
                            converted_href = convert_url_to_local(original_href, f"{tag.name}[href]")
                            if converted_href != original_href:
                                tag['href'] = converted_href

                # Convert all src attributes (img, script, iframe, video, audio, source, track)
                for tag in soup.find_all(['img', 'script', 'iframe', 'video', 'audio', 'source', 'track'], src=True):
                    if isinstance(tag, Tag) and 'src' in tag.attrs:
                        original_src = tag['src']
                        if isinstance(original_src, str):
                            converted_src = convert_url_to_local(original_src, f"{tag.name}[src]")
                            if converted_src != original_src:
                                tag['src'] = converted_src

                # Convert srcset attributes in img and source tags
                for tag in soup.find_all(['img', 'source'], srcset=True):
                    if isinstance(tag, Tag) and 'srcset' in tag.attrs:
                        srcset = tag['srcset']
                        if srcset and isinstance(srcset, str):
                            srcset_items = []
                            for src_item in srcset.split(','):
                                parts = src_item.strip().split()
                                if parts:
                                    src_url = parts[0]
                                    converted_src = convert_url_to_local(src_url, f"{tag.name}[srcset]")
                                    if len(parts) > 1:
                                        srcset_items.append(f"{converted_src} {' '.join(parts[1:])}")
                                    else:
                                        srcset_items.append(converted_src)
                            tag['srcset'] = ', '.join(srcset_items)

                # Convert action attributes in forms
                for form in soup.find_all('form', action=True):
                    if isinstance(form, Tag) and 'action' in form.attrs:
                        original_action = form['action']
                        if isinstance(original_action, str):
                            converted_action = convert_url_to_local(original_action, "form[action]")
                            if converted_action != original_action:
                                form['action'] = converted_action

                # Convert poster attributes in video tags
                for video in soup.find_all('video', poster=True):
                    if isinstance(video, Tag) and 'poster' in video.attrs:
                        original_poster = video['poster']
                        if isinstance(original_poster, str):
                            converted_poster = convert_url_to_local(original_poster, "video[poster]")
                            if converted_poster != original_poster:
                                video['poster'] = converted_poster

                # Convert data-* attributes that contain URLs
                for tag in soup.find_all():
                    if isinstance(tag, Tag) and hasattr(tag, 'attrs') and tag.attrs:
                        for attr_name, attr_value in list(tag.attrs.items()):
                            if (attr_name.startswith('data-') and 
                                isinstance(attr_value, str) and 
                                attr_name.lower() in ['data-href', 'data-url', 'data-src', 'data-link', 'data-background']):
                                converted_value = convert_url_to_local(attr_value, f"{tag.name}[{attr_name}]")
                                if converted_value != attr_value:
                                    tag[attr_name] = converted_value

                # Convert CSS background images in style attributes
                for element in soup.find_all(style=True):
                    if isinstance(element, Tag) and 'style' in element.attrs:
                        style = element.get('style', '')
                        if style and isinstance(style, str) and 'url(' in style:
                            def replace_url(match):
                                url = match.group(1).strip('\'"')
                                element_name = getattr(element, 'name', 'unknown')
                                converted_url = convert_url_to_local(url, f"{element_name}[style]")
                                if converted_url != url:
                                    return f'url("{converted_url}")'
                                return match.group(0)

                            new_style = re.sub(r'url\(["\']?([^"\']+)["\']?\)', replace_url, style)
                            if new_style != style:
                                element['style'] = new_style

                # Convert URLs in <style> tags (CSS content)
                for style_tag in soup.find_all('style'):
                    if isinstance(style_tag, Tag) and style_tag.string:
                        css_content = style_tag.string
                        if isinstance(css_content, str) and 'url(' in css_content:
                            def replace_css_url(match):
                                url = match.group(1).strip('\'"')
                                converted_url = convert_url_to_local(url, "style[css]")
                                if converted_url != url:
                                    return f'url("{converted_url}")'
                                return match.group(0)

                            new_css = re.sub(r'url\(["\']?([^"\']+)["\']?\)', replace_css_url, css_content)
                            if new_css != css_content:
                                style_tag.string = new_css

                # ПРАВИЛЬНАЯ СЕРИАЛИЗАЦИЯ: Убираем лишние NavigableString узлы и корректно строим HTML
                final_html = self._serialize_html_safely(soup, content)
                
                # АТОМАРНАЯ ЗАПИСЬ: Пишем во временный файл и заменяем
                temp_file = file_path + '.tmp'
                with open(temp_file, 'w', encoding='utf-8') as f:
                    f.write(final_html)
                
                # Атомарная замена
                os.replace(temp_file, file_path)

                # Store the soup object for potential AI rewriting
                page_data['converted_soup'] = soup
                
                total_conversions += page_conversions
                if page_conversions > 0:
                    logging.info(f"✅ Converted {page_conversions} URLs in {page_data['local_path']}")

            except Exception as e:
                logging.error(f"Error converting URLs in {page_data.get('local_path', 'unknown')}: {e}")
        
        # Process CSS files for URL conversion
        css_conversions = self._convert_css_urls_to_local()
        total_conversions += css_conversions
        
        logging.info(f"🎯 Total URL conversions completed: {total_conversions} (including {css_conversions} CSS URLs)")

    def _convert_css_urls_to_local(self):
        """Convert URLs in CSS files to local relative paths"""
        logging.info(f"Converting URLs in {len(self.downloaded_css_files)} CSS files...")
        total_css_conversions = 0
        
        for css_data in self.downloaded_css_files:
            try:
                file_path = os.path.join(self.output_dir, css_data['local_path'])
                css_conversions = 0
                
                # Read CSS file
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    css_content = f.read()
                
                original_content = css_content
                
                # Calculate relative path from CSS file to output root
                css_dir = os.path.dirname(css_data['local_path'])
                
                def convert_css_url(match):
                    """Convert URL in CSS"""
                    nonlocal css_conversions
                    url = match.group(1).strip('\'"')
                    
                    if not url or url.startswith(('#', 'javascript:', 'mailto:', 'tel:', 'data:')):
                        return match.group(0)
                    
                    # Convert relative URL to absolute for checking
                    if url.startswith('//'):
                        full_url = 'https:' + url
                    elif url.startswith('/'):
                        full_url = self.base_url + url  
                    elif not url.startswith('http'):
                        # For relative URLs in CSS, resolve against the CSS file's original URL
                        full_url = urllib.parse.urljoin(css_data['url'], url)
                    else:
                        full_url = url
                    
                    # Если ресурс не удалось скачать - оставляем оригинальный URL
                    if full_url in self.failed_resources:
                        return match.group(0)
                    
                    # Handle different URL types
                    if self._is_internal_url(url) or full_url in self.resources:
                        # Validate that the URL actually exists locally
                        if not self._url_exists_locally(url):
                            logging.debug(f"⚠️ CSS: Skipping conversion - URL not downloaded: {url}")
                            return match.group(0)
                        
                        try:
                            # Convert to absolute URL first
                            if url.startswith('//'):
                                full_url = 'https:' + url
                            elif url.startswith('/'):
                                full_url = self.base_url + url
                            elif not url.startswith('http'):
                                # For relative URLs in CSS, resolve against the CSS file's original URL
                                full_url = urllib.parse.urljoin(css_data['url'], url)
                            else:
                                full_url = url
                            
                            # Remove parameters for local path calculation
                            clean_url = full_url.split('?')[0]
                            local_path = self._url_to_local_path(clean_url)
                            
                            # Calculate relative path from CSS file to target
                            if css_dir:
                                converted_url = os.path.relpath(local_path, css_dir).replace('\\', '/')
                            else:
                                converted_url = local_path
                            
                            css_conversions += 1
                            logging.debug(f"✅ CSS converted: {url} -> {converted_url}")
                            return f'url("{converted_url}")'
                            
                        except Exception as e:
                            logging.warning(f"Failed to convert CSS URL {url}: {e}")
                            return match.group(0)
                    
                    return match.group(0)
                
                # Convert URLs in CSS using regex
                import re
                css_content = re.sub(r'url\(["\']?([^"\']+)["\']?\)', convert_css_url, css_content)
                
                # Handle @import statements
                def convert_import_url(match):
                    nonlocal css_conversions
                    quote = match.group(1)
                    url = match.group(2)
                    
                    if self._is_internal_url(url) and self._url_exists_locally(url):
                        try:
                            if url.startswith('/'):
                                full_url = self.base_url + url
                            elif not url.startswith('http'):
                                full_url = urllib.parse.urljoin(css_data['url'], url)
                            else:
                                full_url = url
                                
                            clean_url = full_url.split('?')[0]
                            local_path = self._url_to_local_path(clean_url)
                            
                            if css_dir:
                                converted_url = os.path.relpath(local_path, css_dir).replace('\\', '/')
                            else:
                                converted_url = local_path
                            
                            css_conversions += 1
                            return f'@import {quote}{converted_url}{quote}'
                        except Exception as e:
                            logging.warning(f"Failed to convert CSS @import {url}: {e}")
                    
                    return match.group(0)
                
                css_content = re.sub(r'@import\s+(["\'])([^"\']+)\1', convert_import_url, css_content)
                
                # Save modified CSS file if any changes were made
                if css_content != original_content:
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(css_content)
                    logging.info(f"✅ Converted {css_conversions} URLs in CSS: {css_data['local_path']}")
                
                total_css_conversions += css_conversions
                
            except Exception as e:
                logging.error(f"Error converting URLs in CSS {css_data.get('local_path', 'unknown')}: {e}")
        
        return total_css_conversions

    def _rewrite_content_with_ai(self, start_time, max_runtime):
        """Apply AI content rewriting using pure DOM parsing with BeautifulSoup"""
        # DETAILED LOGGING FOR DEBUGGING
        logging.info(f"🔍 AI REWRITE DEBUG: rewrite_content={self.rewrite_content}")
        logging.info(f"🔍 AI REWRITE DEBUG: has_openai_client={hasattr(self, 'openai_client')}")
        logging.info(f"🔍 AI REWRITE DEBUG: language={self.rewrite_language}")
        logging.info(f"🔍 AI REWRITE DEBUG: downloaded_pages={len(self.downloaded_pages)}")
        
        if not self.rewrite_content or not hasattr(self, 'openai_client'):
            logging.error("❌ AI REWRITING SKIPPED - not enabled or no OpenAI client!")
            return {'status': 'completed', 'message': 'AI переписывание пропущено'}

        logging.info(f"🚀 STARTING AI REWRITING - Target: Polish language conversion")
        processed = 0
        total_replacements = 0
        total_text_nodes = 0
        skipped_nav = 0
        skipped_technical = 0
        skipped_invalid = 0
        skipped_short_or_empty = 0
        skipped_no_parent = 0
        skipped_ai_no_result = 0
        sample_skips = []
        pages_to_process = self.downloaded_pages  # ВСЕ СТРАНИЦЫ без ограничений!
        logging.info(f"📄 Processing ALL {len(pages_to_process)} pages for AI rewriting")

        # Navigation content keywords
        navigation_keywords = [
            # Menu separators
            '•', '|', '→', '/', '\\', '-', '–', '—',
            # English navigation words
            'home', 'about', 'contact', 'services', 'portfolio', 'blog', 'news',
            'shop', 'products', 'gallery', 'testimonials', 'careers', 'login',
            'register', 'account', 'profile', 'dashboard', 'settings', 'logout',
            'search', 'cart', 'checkout', 'wishlist', 'compare', 'help', 'faq',
            'support', 'privacy', 'terms', 'sitemap', 'categories', 'brands',
            'menu', 'nav', 'navigation', 'navbar', 'header', 'footer', 'breadcrumb',
            'main-nav', 'primary-nav', 'secondary-nav', 'top-nav', 'side-nav',
            # Polish navigation words
            'główna', 'strona', 'kontakt', 'o nas', 'usługi', 'portfolio',
            'aktualności', 'sklep', 'produkty', 'galeria', 'opinie', 'kariera',
            'logowanie', 'rejestracja', 'konto', 'profil', 'panel', 'ustawienia',
            'wyloguj', 'szukaj', 'koszyk', 'zamówienie', 'lista', 'porównaj',
            'pomoc', 'wsparcie', 'prywatność', 'regulamin', 'kategorie', 'marki',
            'main menu', 'główne menu', 'menu główne', 'nawigacja', 'katalog'
        ]

        def is_navigation_element(element):
            """МЯГКИЙ фильтр - пропускает ТОЛЬКО явную навигацию"""
            
            if isinstance(element, NavigableString):
                current = element.parent
            else:
                current = element
            
            # Технические теги - всегда пропускаем
            excluded_tags = {'script', 'style', 'noscript', 'meta', 'link'}
            
            # Навигационные теги - НЕ переписываем (только прямые теги)
            navigation_tags = {'nav', 'menu'}
            
            # ТОЧНЫЕ навигационные классы - требуем точное совпадение, НЕ частичное
            strict_nav_classes = {
                'navbar', 'nav-menu', 'main-nav', 'primary-nav', 'site-nav',
                'mobile-menu', 'breadcrumb', 'breadcrumbs'
            }
            
            # Навигационные роли - НЕ переписываем
            navigation_roles = {'navigation'}
            
            depth = 0
            nav_signals = 0  # Счётчик сигналов навигации
            
            while current and hasattr(current, 'name') and current.name and depth < 5:
                if current.name in ['html', 'body', '[document]']:
                    break
                
                # Технические теги - всегда пропускаем
                if current.name in excluded_tags:
                    return True
                
                # Прямые навигационные теги
                if current.name in navigation_tags:
                    nav_signals += 2
                
                # Проверка классов - ТОЧНОЕ совпадение
                element_classes = current.get('class')
                if element_classes:
                    if isinstance(element_classes, str):
                        element_classes = element_classes.split()
                    for cls in element_classes:
                        if isinstance(cls, str):
                            cls_lower = cls.lower()
                            if cls_lower in strict_nav_classes:
                                nav_signals += 2
                
                # Проверка role
                role = current.get('role')
                if role and isinstance(role, str):
                    if role.lower() in navigation_roles:
                        nav_signals += 2
                
                current = current.parent
                depth += 1
            
            # Требуем минимум 2 сигнала чтобы пропустить
            return nav_signals >= 2
        
        def is_main_content(element):
            """Проверяет находится ли элемент в ОСНОВНОМ контенте страницы"""
            if isinstance(element, NavigableString):
                current = element.parent
            else:
                current = element
            
            # Теги основного контента
            content_tags = {'main', 'article', 'section'}
            
            # Классы основного контента
            content_classes = {
                'content', 'main-content', 'post-content', 'entry-content',
                'article-content', 'page-content', 'text-content', 'body-content',
                'single-content', 'post-body', 'entry-body', 'article-body',
                'container', 'wrapper', 'inner', 'prose'
            }
            
            # Роли основного контента
            content_roles = {'main', 'article'}
            
            depth = 0
            while current and hasattr(current, 'name') and current.name and depth < 10:
                if current.name in ['html', 'body', '[document]']:
                    break
                
                # Проверяем теги контента
                if current.name in content_tags:
                    return True
                
                # Проверяем role
                role = current.get('role')
                if role and isinstance(role, str):
                    if role.lower() in content_roles:
                        return True
                
                # Проверяем классы
                element_classes = current.get('class')
                if element_classes:
                    if isinstance(element_classes, str):
                        element_classes = element_classes.split()
                    for cls in element_classes:
                        if isinstance(cls, str):
                            cls_lower = cls.lower()
                            for content_cls in content_classes:
                                if content_cls in cls_lower:
                                    return True
                
                current = current.parent
                depth += 1
            
            return False

        def is_valid_text_for_rewriting(text_content):
            """МЯГКАЯ валидация - переписываем больше контента"""
            if not text_content:
                return False
            
            stripped_text = text_content.strip()
            
            # МИНИМУМ 20 символов - переписываем больше текста
            if not stripped_text or len(stripped_text) < 20:
                return False
            
            text_lower = stripped_text.lower()
            
            # Блокируем технический код
            if ('@font-face' in text_lower or 'function(' in text_lower or 
                'document.' in text_lower or '&&' in text_lower or
                'var ' in text_lower or 'const ' in text_lower):
                return False
            
            # Блокируем URL
            if text_lower.startswith('http') or 'javascript:' in text_lower:
                return False
            
            # Блокируем код (много спецсимволов)
            if stripped_text.count('{') > 2 or stripped_text.count(';') > 3:
                return False
            
            # Требуем минимум 2 слова
            word_count = len(stripped_text.split())
            if word_count < 2:
                return False
            
            # Требуем достаточно букв (минимум 60% от длины)
            letter_count = sum(1 for c in stripped_text if c.isalpha() or c.isspace())
            if letter_count < len(stripped_text) * 0.6:
                return False
            
            return True

        def get_element_type_limits(element):
            """Get strict length limits based on element type"""
            if not element or not hasattr(element, 'name'):
                return 1.2  # Default: 20% tolerance
            
            tag_name = element.name.lower()
            
            # Strict limits for navigation and UI elements
            if tag_name in ['h1', 'h2', 'h3', 'h4', 'h5', 'h6']:
                return 1.1  # Headers: max 10% longer
            elif tag_name in ['button', 'a'] and element.parent and element.parent.name in ['nav', 'footer']:
                return 1.0  # Navigation links: same length or shorter
            elif tag_name in ['span', 'em', 'strong']:
                return 1.0  # Short spans: same length
            elif tag_name in ['title', 'label']:
                return 1.05  # Titles/labels: max 5% longer
            else:
                return 1.2  # Paragraphs and content: 20% tolerance
        
        def safe_truncate(text, max_length):
            """Safely truncate text at word boundary"""
            if len(text) <= max_length:
                return text
            
            # Find last space before max_length
            truncated = text[:max_length]
            last_space = truncated.rfind(' ')
            
            if last_space > max_length * 0.8:  # If space is reasonably close
                result = text[:last_space].rstrip()
                # Add proper punctuation if missing
                if result and result[-1] not in '.!?':
                    if result[-1] in ',;:':
                        result = result[:-1] + '.'
                    else:
                        result += '.'
                return result
            else:
                # No good space found, cut at max_length
                return text[:max_length].rstrip()

        def rewrite_text_with_ai(text_content, element=None):
            """Rewrite text using OpenAI API with CACHING + length control"""
            try:
                # КЭШИРОВАНИЕ - не переписываем одинаковые тексты
                text_hash = hashlib.sha1(text_content.strip().encode()).hexdigest()
                if text_hash in self.rewrite_cache:
                    logging.debug(f"📋 Cache hit for text: '{text_content[:30]}...'")
                    return self.rewrite_cache[text_hash]
                
                domain_name = self.target_domain.replace('https://', '').replace('http://', '').replace('www.', '')
                language_prompt = self.language_prompts.get(self.rewrite_language, self.language_prompts['english'])
                
                original_length = len(text_content.strip())
                
                # Инструкции по длине НА АНГЛИЙСКОМ (универсально для всех языков)
                if original_length <= 50:
                    length_instruction = f"Keep it SHORT (max {original_length + 10} characters)"
                elif original_length <= 150:
                    length_instruction = f"Keep MEDIUM length (around {original_length} characters, max {original_length + 30})"
                elif original_length <= 300:
                    length_instruction = f"Keep SIMILAR length (around {original_length} characters, max {original_length + 50})"
                else:
                    length_instruction = f"Keep SIMILAR length (around {original_length} characters, max {original_length + 100})"

                response = self.openai_client.chat.completions.create(
                    model="gpt-5.4-mini",
                    messages=[
                        {"role": "system", "content": f"{language_prompt} You are writing for: {domain_name}. {length_instruction}. Add subtle spoken language nuances, personal tone, small imperfections that make the text sound authentically human. Reply with ONLY the rewritten text."},
                        {"role": "user", "content": text_content.strip()}
                    ],
                    max_tokens=min(int(original_length * 1.5), 600),
                    temperature=0.85
                )

                content = response.choices[0].message.content
                rewritten_text = content.strip() if content else ""
                
                if rewritten_text and len(rewritten_text) > 5:
                    # Сохраняем в кэш
                    self.rewrite_cache[text_hash] = rewritten_text
                    logging.debug(f"✅ AI: '{text_content[:40]}...' -> '{rewritten_text[:40]}...'")
                    return rewritten_text
                
            except Exception as e:
                logging.error(f"🚨 AI rewrite failed: {type(e).__name__}: {str(e)[:100]}")
            
            return None

        for page_data in pages_to_process:
            # Check stop conditions
            if time.time() - start_time > max_runtime or self._should_stop():
                logging.info("Stopping AI rewriting due to timeout or stop request")
                if self.status_callback:
                    self.status_callback('cancelled', 'Задача остановлена пользователем', 0)
                return {'status': 'cancelled', 'message': 'Задача остановлена пользователем'}

            # ОБНОВЛЯЕМ ПРОГРЕСС В НАЧАЛЕ - чтобы пользователь видел что задача работает
            if self.status_callback:
                progress = 85 + (processed / len(pages_to_process)) * 10
                remaining = len(pages_to_process) - processed
                self.status_callback('running', f'AI переписывание: осталось {remaining} стр.', progress)

            try:
                local_path = page_data['local_path']
                file_path = os.path.join(self.output_dir, local_path)
                page_replacements = 0

                # SKIP IMAGES AND BINARY FILES - ONLY PROCESS TEXT FILES
                image_extensions = {'.jpg', '.jpeg', '.png', '.gif', '.webp', '.bmp', '.svg', '.ico', '.pdf', '.zip', '.mp4', '.mov', '.avi', '.mp3', '.wav'}
                file_extension = os.path.splitext(local_path)[1].lower()
                if file_extension in image_extensions:
                    logging.debug(f"⏭️ Skipping binary file: {local_path}")
                    processed += 1
                    continue

                # Используем уже обработанный soup объект с преобразованными URL если доступен
                content = None  # Инициализация переменной
                if 'converted_soup' in page_data and page_data['converted_soup'] is not None:
                    soup = page_data['converted_soup']
                    logging.debug(f"🔄 Using pre-converted soup for {local_path}")
                else:
                    # Fallback: читаем файл заново
                    with open(file_path, 'r', encoding='utf-8') as f:
                        content = f.read()
                    soup = BeautifulSoup(content, 'html.parser')
                    logging.warning(f"⚠️ No converted soup found for {local_path}, parsing file again")

                # Find all text-containing elements, excluding script and style
                from bs4.element import Comment
                text_elements = soup.find_all(text=True)

                for text_node in text_elements:
                    total_text_nodes += 1
                    # Check stop conditions and replacement limit - UNLIMITED!
                    if total_replacements >= 500000:  # 500k replacements - практически безлимит
                        logging.info(f"🛑 Reached maximum replacement limit (500000)")
                        break
                    
                    if time.time() - start_time > max_runtime or self._should_stop():
                        break

                    # Skip comments and non-NavigableString elements
                    if isinstance(text_node, Comment) or not isinstance(text_node, NavigableString):
                        skipped_technical += 1
                        continue
                    
                    # Ensure text_node has a parent
                    if not text_node.parent or not hasattr(text_node.parent, 'name'):
                        skipped_no_parent += 1
                        continue

                    # Skip ONLY critical technical tags - ULTRA MINIMAL
                    excluded_tags = {
                        'script', 'style', 'noscript'
                    }
                    if text_node.parent.name in excluded_tags:
                        skipped_technical += 1
                        continue

                    # Skip navigation elements using improved DOM traversal
                    if is_navigation_element(text_node):
                        skipped_nav += 1
                        continue

                    # Get text content with None check
                    text_content = getattr(text_node, 'string', None)
                    if not text_content:
                        skipped_short_or_empty += 1
                        continue
                    
                    # Preserve leading/trailing whitespace for proper replacement
                    original_text = str(text_content)
                    clean_text = original_text.strip()
                    
                    if not is_valid_text_for_rewriting(clean_text):
                        skipped_invalid += 1
                        if len(sample_skips) < 10 and clean_text:
                            sample_skips.append(f"{local_path} <{text_node.parent.name}> len={len(clean_text)} text='{clean_text[:120]}'")
                        continue

                    # Attempt AI rewriting with STRICT length control
                    rewritten_text = rewrite_text_with_ai(clean_text)
                    if rewritten_text and rewritten_text != clean_text:
                        
                        # ЖЕСТКАЯ ПРОВЕРКА ДЛИНЫ И БЕЗОПАСНОЕ УСЕЧЕНИЕ
                        original_len = len(clean_text)
                        rewritten_len = len(rewritten_text)
                        
                        # Определяем максимальную допустимую длину на основе типа элемента
                        if text_node.parent and hasattr(text_node.parent, 'name'):
                            tag_name = text_node.parent.name.lower()
                            if tag_name in ['h1', 'h2', 'h3', 'h4', 'h5', 'h6']:
                                max_allowed = int(original_len * 1.1)  # Заголовки: +10%
                            elif tag_name in ['button', 'a']:
                                max_allowed = original_len  # Кнопки/ссылки: та же длина
                            elif tag_name in ['span', 'em', 'strong'] and original_len < 30:
                                max_allowed = original_len  # Короткие элементы: та же длина
                            else:
                                max_allowed = int(original_len * 1.2)  # Контент: +20%
                        else:
                            max_allowed = int(original_len * 1.2)
                        
                        # УСЕКАЕМ ЕСЛИ ПРЕВЫШЕН ЛИМИТ
                        if rewritten_len > max_allowed:
                            # Найти последний пробел перед лимитом
                            truncated = rewritten_text[:max_allowed]
                            last_space = truncated.rfind(' ')
                            if last_space > max_allowed * 0.8:
                                rewritten_text = rewritten_text[:last_space].rstrip()
                                if rewritten_text and rewritten_text[-1] not in '.!?':
                                    rewritten_text += '.'
                            else:
                                rewritten_text = rewritten_text[:max_allowed].rstrip()
                            
                            current_tag_name = 'unknown'
                            if text_node.parent and hasattr(text_node.parent, 'name'):
                                current_tag_name = text_node.parent.name
                            logging.warning(f"⚠️ Text truncated: {rewritten_len} → {len(rewritten_text)} chars for {current_tag_name}")
                        
                        # Preserve original whitespace structure
                        leading_space = original_text[:len(original_text) - len(original_text.lstrip())]
                        trailing_space = original_text[len(original_text.rstrip()):]
                        final_text = leading_space + rewritten_text + trailing_space
                        
                        # Replace text directly in DOM tree with proper error handling
                        try:
                            # Create new NavigableString from final_text
                            from bs4.element import NavigableString as NavString
                            new_text_node = NavString(final_text)
                            text_node.replace_with(new_text_node)
                            total_replacements += 1
                            page_replacements += 1
                            logging.debug(f"📝 Replaced ({original_len}→{len(rewritten_text)} chars)")
                        except Exception as e:
                            logging.warning(f"Failed to replace text node: {e}")
                            continue
                    else:
                        skipped_ai_no_result += 1

                # ПРАВИЛЬНАЯ СЕРИАЛИЗАЦИЯ: Используем оригинальный контент если есть, или читаем файл
                if 'converted_soup' in page_data and page_data['converted_soup'] is not None:
                    # Если используем pre-converted soup, нужно прочитать оригинальный контент
                    with open(file_path, 'r', encoding='utf-8') as original_f:
                        original_content = original_f.read()
                else:
                    # Если читали файл выше, используем тот же контент
                    original_content = content
                
                final_html = self._serialize_html_safely(soup, original_content)
                
                # АТОМАРНАЯ ЗАПИСЬ: Пишем во временный файл и заменяем
                temp_file = file_path + '.tmp'
                with open(temp_file, 'w', encoding='utf-8') as f:
                    f.write(final_html)
                
                # Атомарная замена
                os.replace(temp_file, file_path)

                if page_replacements > 0:
                    logging.info(f"🤖 AI rewriting completed for {local_path} - made {page_replacements} replacements")
                else:
                    logging.info(f"🔎 No AI changes made to {local_path}; text_nodes={len(text_elements)}")

                processed += 1

            except (TimeoutError, Exception) as e:
                # Ловим все timeout ошибки: TimeoutError, APITimeoutError от OpenAI, httpx timeout
                if 'timeout' in str(type(e).__name__).lower() or 'timeout' in str(e).lower():
                    logging.error(f"⏱️ OpenAI timeout for {page_data.get('local_path', 'unknown')}: {type(e).__name__}: {e}")
                else:
                    logging.error(f"Error in AI rewriting for {page_data.get('local_path', 'unknown')}: {e}")
                processed += 1
                continue

        # Финальное обновление - НЕ меняем статус, пусть главный метод scrape() установит 'completed'
        logging.info(
            f"🔎 AI rewrite diagnostics: total_text_nodes={total_text_nodes}, "
            f"skipped_nav={skipped_nav}, skipped_technical={skipped_technical}, "
            f"skipped_invalid={skipped_invalid}, skipped_short_or_empty={skipped_short_or_empty}, "
            f"skipped_no_parent={skipped_no_parent}, skipped_ai_no_result={skipped_ai_no_result}"
        )
        if sample_skips:
            logging.info("🔎 AI skipped text samples:")
            for sample in sample_skips:
                logging.info(f"🔎 {sample}")
        logging.info(f"🤖 AI rewriting completed: {total_replacements} total replacements across {processed} pages")
        return {'status': 'completed', 'message': f'AI переписывание завершено: {total_replacements} замен в {processed} страницах'}

    def _serialize_html_safely(self, soup, original_content):
        """Безопасная сериализация HTML без лишних NavigableString узлов"""
        from bs4.element import Tag, NavigableString, Doctype
        
        # Извлекаем DOCTYPE если есть
        doctype = None
        for element in soup.contents:
            if isinstance(element, Doctype):
                doctype = element
                break
        
        # СТРУКТУРНАЯ ФИЛЬТРАЦИЯ: Удаляем только лишние корневые NavigableString узлы
        clean_contents = []
        for element in soup.contents:
            if isinstance(element, Tag):
                clean_contents.append(element)
            elif isinstance(element, Doctype):
                clean_contents.append(element)
            elif isinstance(element, NavigableString):
                # Убираем только пустые/пробельные корневые текстовые узлы
                # НЕ проверяем содержимое - важна только структурная позиция
                text = str(element).strip()
                if text:
                    # Проверяем что это НЕ лишний узел от BeautifulSoup
                    # Лишние узлы обычно находятся между основными тегами
                    is_between_tags = False
                    element_index = soup.contents.index(element)
                    
                    # Проверяем есть ли теги до и после этого текстового узла
                    has_tag_before = any(isinstance(soup.contents[i], Tag) for i in range(element_index))
                    has_tag_after = any(isinstance(soup.contents[i], Tag) for i in range(element_index + 1, len(soup.contents)))
                    
                    is_between_tags = has_tag_before and has_tag_after
                    
                    if not is_between_tags:
                        # Это может быть легитимный текст - сохраняем
                        clean_contents.append(element)
                    else:
                        logging.debug(f"Удален корневой текстовый узел между тегами: '{str(element)[:20]}'")
        
        # Проверяем структуру исходного HTML
        original_had_html = '<html' in original_content.lower()
        original_had_head = '<head' in original_content.lower()  
        original_had_body = '<body' in original_content.lower()
        
        # Строим финальный HTML
        if original_had_html or original_had_head or original_had_body:
            # Полный документ - сериализуем как есть
            if doctype:
                doctype_str = f"<!DOCTYPE {doctype}>\n"
            else:
                doctype_str = ""
            
            # Сериализуем только структурные элементы
            html_elements = [elem for elem in clean_contents if isinstance(elem, Tag)]
            if html_elements:
                body_html = ''.join(elem.decode(formatter="minimal") for elem in html_elements)
                final_html = doctype_str + body_html
            else:
                # Fallback - сериализуем все что есть
                temp_soup = BeautifulSoup('', 'html.parser')
                for elem in clean_contents:
                    if not isinstance(elem, Doctype):
                        temp_soup.append(elem)
                final_html = doctype_str + temp_soup.decode(formatter="minimal")
        else:
            # HTML фрагмент - извлекаем содержимое body
            if soup.body and soup.body.contents:
                final_html = soup.body.decode_contents(formatter="minimal")
            else:
                # Для фрагментов берем только Tag элементы
                html_elements = [elem for elem in clean_contents if isinstance(elem, Tag)]
                if html_elements:
                    final_html = ''.join(elem.decode(formatter="minimal") for elem in html_elements)
                else:
                    # Fallback - используем все содержимое
                    final_html = soup.decode(formatter="minimal")
        
        return final_html

    def __del__(self):
        """Cleanup session on destruction"""
        if hasattr(self, 'session'):
            self.session.close()