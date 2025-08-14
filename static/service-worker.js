const CACHE = 'vasketid-cache-v2';
const STATIC_ASSETS = [
  '/static/style.css',
  '/static/Bg.jpg',
  '/static/icon-192.png',
  '/static/icon-512.png'
];

self.addEventListener('install', (e) => {
  e.waitUntil(caches.open(CACHE).then((c) => c.addAll(STATIC_ASSETS)));
  self.skipWaiting();
});

self.addEventListener('activate', (e) => {
  e.waitUntil(
    caches.keys().then((keys) =>
      Promise.all(keys.filter((k) => k !== CACHE).map((k) => caches.delete(k)))
    )
  );
  self.clients.claim();
});

self.addEventListener('fetch', (e) => {
  const req = e.request;

  // HTML-navigationer: altid network-first (ingen cache af / eller /login)
  if (req.mode === 'navigate') {
    e.respondWith(fetch(req).catch(() => caches.match('/static/style.css'))); // simpel fallback
    return;
  }

  // Øvrige statiske filer: cache-first
  e.respondWith(caches.match(req).then((res) => res || fetch(req)));
});