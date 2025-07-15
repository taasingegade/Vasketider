self.addEventListener('install', function(e) {
  e.waitUntil(
    caches.open('vasketid-cache').then(function(cache) {
      return cache.addAll([
        '/',
        '/login',
        '/static/style.css',
        '/static/Bg.jpg'
      ]);
    })
  );
});

self.addEventListener('fetch', function(e) {
  e.respondWith(
    caches.match(e.request).then(function(response) {
      return response || fetch(e.request);
    })
  );
});