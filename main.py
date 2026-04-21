#!/usr/bin/env python3
"""
Main entry point for Replit deployment.
This file is required because .replit expects 'main.py' as entrypoint.
"""

# Import and run the Flask application
from app import app

if __name__ == '__main__':
    import os
    # Use environment PORT if available (for deployment), otherwise 5000
    port = int(os.environ.get('PORT', 5000))
    app.run(host='0.0.0.0', port=port, debug=False)