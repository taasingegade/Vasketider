// Enkel, robust menu-controller til hamburgery
// Brug: window.VasketiderMenu.attach({ button:'#id', drawer:'#id' })
window.VasketiderMenu = {
  attach({ button, drawer, closeOnRouteChange = true } = {}) {
    const btn  = document.querySelector(button);
    const menu = document.querySelector(drawer);
    if (!btn || !menu) return;

    const close = () => {
      menu.classList.remove('show');
      btn.classList.remove('active');
      btn.setAttribute('aria-expanded', 'false');
    };

    const toggle = () => {
      const open = !menu.classList.contains('show');
      menu.classList.toggle('show', open);
      btn.classList.toggle('active', open);
      btn.setAttribute('aria-expanded', open ? 'true' : 'false');
    };

    btn.addEventListener('click', (e) => { e.stopPropagation(); toggle(); });

    // Luk ved klik udenfor
    document.addEventListener('click', (e) => {
      if (!menu.contains(e.target) && !btn.contains(e.target)) close();
    });

    // Luk ved "navigationsskift" (fx tilbage/forfra)
    if (closeOnRouteChange) {
      window.addEventListener('pageshow', close);
      window.addEventListener('popstate', close);
    }
  }
};