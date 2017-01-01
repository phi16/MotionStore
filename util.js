var Util = (function(){
  var u = {};
  u.width = 0;
  u.height = 0;
  u.onload = function(){
    u.canvas = document.getElementById("canvas");
    function resize(){
      u.width = u.canvas.width = document.getElementById("container").clientWidth;
      u.height = u.canvas.height;
    }
    resize();
    window.onresize = resize;
  };
  var imCache = {};
  u.imageCache = function(name){
    if(imCache[name])return imCache[name];
    var elem = document.createElement("img");
    elem.src = name;
    return imCache[name] = elem;
  };
  var cvsCache = {};
  function initCache(name,w,h){
    if(!cvsCache[name] || cvsCache[name].w!=w || cvsCache[name].h!=h){
      let sCvs = document.createElement('canvas');
      sCvs.width = w, sCvs.height = h;
      let sCtx = sCvs.getContext('2d');
      cvsCache[name] = {
        canvas : sCvs,
        context : sCtx,
        w : w,
        h : h,
        value : null
      };
    }
  }
  u.beginCache = function(name,x,y,w,h,rx,ry,v){
    rx = Math.floor(rx), ry = Math.floor(ry);
    initCache(name,rx,ry);
    let ch = cvsCache[name];
    if(ch.value != null && ch.value == v)return null;
    let ctx = ch.context;
    ctx.clearRect(0,0,rx,ry);
    ctx.save();
    ctx.scale(rx/w,ry/h);
    ctx.translate(-x,-y);
    return ctx;
  };
  u.endCache = function(name,v){
    let ch = cvsCache[name];
    ch.context.restore();
    ch.value = v;
  };
  u.getCache = function(name){
    return cvsCache[name].canvas;
  };
  u.nya = {};
  u.nyaGet = function(n){
    if(u.nya[n])return u.nya[n];
    else return 0;
  };
  return u;
})();