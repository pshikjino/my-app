# Overview

This is a professional web scraping application built with Flask that allows users to scrape websites, optionally rewrite content using AI, and download the results as a zip file. The system features concurrent scraping, sitemap discovery, robots.txt compliance, intelligent content processing with OpenAI integration, and universal compatibility with all website types including CDN-hosted assets.

# User Preferences

Preferred communication style: Simple, everyday language.

# System Architecture

## Frontend Architecture
- **Flask Templates**: Simple HTML templates with embedded CSS for a clean, responsive interface
- **Real-time Status Updates**: AJAX-based status polling to show scraping progress
- **Progressive Enhancement**: Forms work without JavaScript, enhanced with real-time updates

## Backend Architecture
- **Flask Web Framework**: Lightweight Python web server handling HTTP requests and responses
- **Asynchronous Job Processing**: Background threading for long-running scraping tasks
- **File-based Job Management**: Each scraping job gets a unique directory with status files and results
- **Automatic Cleanup**: Periodic removal of jobs older than 24 hours to manage disk space

## Core Scraping Engine
- **SiteScraper Class**: Main scraping engine with configurable depth, concurrency (up to 50 threads), and politeness settings
- **Multi-threaded Processing**: Concurrent page downloading with ThreadPoolExecutor (40 workers for resources)
- **Intelligent Link Discovery**: Multiple strategies including sitemap parsing, robots.txt analysis, and HTML link extraction
- **Content Filtering**: Optional blog exclusion and content type filtering
- **Rate Limiting**: Configurable delays for HTML pages only (resources download without delays for speed)
- **Retry with Backoff**: 3 retry attempts with exponential backoff (0.4s, 0.8s, 1.6s) for failed resources
- **Resource Recovery**: Final pass to retry failed resources before completion

## Content Processing Pipeline
- **HTML Parsing**: BeautifulSoup for robust HTML processing and link extraction
- **Resource Collection**: Automatic discovery and download of CSS, JS, images, and other assets
- **URL Rewriting**: Converts absolute URLs to relative paths for offline browsing
- **AI Content Rewriting**: OpenAI GPT-4.1-mini integration for content translation/rewriting in multiple languages
- **Smart Content Detection**: Rewrites text 20+ chars, soft navigation filter (only skips explicit nav/menu tags)
- **AI Caching**: SHA1-based caching to avoid rewriting duplicate text blocks
- **Tracking Removal**: Automatic removal of Google Analytics, GTM, Facebook Pixel, Yandex Metrika and other trackers

## Data Storage
- **File System Storage**: Jobs stored in local directory structure
- **Temporary Files**: Automatic cleanup of old scraping results
- **ZIP Packaging**: Results packaged for easy download

## Error Handling & Resilience
- **Retry Logic**: HTTP request retries with exponential backoff
- **Graceful Degradation**: Continues scraping even when individual pages fail
- **Stop Mechanism**: Users can cancel running jobs via stop files
- **Comprehensive Logging**: Detailed logging for debugging and monitoring

# External Dependencies

## Core Libraries
- **Flask**: Web framework for HTTP handling and templating
- **Requests**: HTTP client library with session management and retry logic
- **BeautifulSoup4**: HTML/XML parsing and manipulation
- **urllib3**: Low-level HTTP client utilities
- **lxml**: Fast XML/HTML parser backend for BeautifulSoup

## AI Integration
- **OpenAI API**: Content rewriting and translation services
- **Language Support**: Built-in prompts for Polish, English, Spanish, Czech, and German

## System Services
- **Threading**: Background job processing without blocking the web interface
- **File System Operations**: Job directory management and cleanup
- **UUID Generation**: Unique job identifiers
- **Logging**: Application monitoring and debugging

## Web Standards Compliance
- **Robots.txt Parser**: Respects website crawling policies
- **Sitemap Discovery**: Automatic sitemap detection and parsing
- **HTTP Standards**: Proper user agent strings and headers
- **Rate Limiting**: Configurable delays to avoid overwhelming target servers