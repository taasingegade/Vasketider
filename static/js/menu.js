/* Vasketider – fælles hamburger/drawer logik
   Brug:
     window.VasketiderMenu.attach({ button:'#btn', drawer:'#menu' })
*/

(function(){
  if (window.VasketiderMenu) return; // safe-guard mod dobbel indlæsning

  function attach(opts){
    const btnSel = opts?.button;
    const drawerSel = opts?.drawer;
    const closeOnRouteChange = !!opts?.closeOnRouteChange;

    const btn = typeof btnSel === 'string' ? document.querySelector(btnSel) : btnSel;
    const drawer = typeof drawerSel === 'string' ? document.querySelector(drawerSel) : drawerSel;

    if (!btn || !drawer) return;

    let open = false;
    const setOpen = (v)=>{
      open = !!v;
      drawer.classList.toggle('show', open);    // din CSS bruger .login-menu.show
      btn.classList.toggle('active', open);     // animation i style.css
      btn.setAttribute('aria-expanded', String(open));
    };

    // Toggle ved klik
    const onClickBtn = (e)=>{ e.stopPropagation(); setOpen(!open); };
    btn.addEventListener('click', onClickBtn, { passive: true });

    // Luk ved klik udenfor
    const onDocClick = (e)=>{
      if (!open) return;
      if (drawer.contains(e.target) || btn.contains(e.target)) return;
      setOpen(false);
    };
    document.addEventListener('click', onDocClick);

    // Luk på Escape
    const onKey = (e)=>{
      if (e.key === 'Escape' && open) setOpen(false);
    };
    document.addEventListener('keydown', onKey);

    // Valgfrit: Luk når man navigerer (fx klik på link i menu)
    if (closeOnRouteChange){
      drawer.addEventListener('click', (ev)=>{
        const a = ev.target.closest('a[href]');
        if (a) setOpen(false);
      });
    }

    // Eksponér lille API
    return { open: ()=>setOpen(true), close: ()=>setOpen(false), toggle: ()=>setOpen(!open) };
  }

  window.VasketiderMenu = { attach };
})();