'use strict';

// Servidor autoritativo: o navegador envia controles, nunca vida ou posição.
const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');
const os = require('node:os');
const crypto = require('node:crypto');

const COVERS = [[-16,-19,7,3.5,5],[0,-22,9,4,5],[17,-18,5,3,8],[-22,-5,5,4,7],[21,1,6,3.7,8],[-17,14,7,3,5],[15,19,8,3.8,5],[-7,9,3,1.4,3],[9,-8,4,1.5,3],[-10,-5,3,2.6,4],[5,12,3,1.5,3],[26,25,3,2,3],[-27,-27,3,2,3]].map(([x,z,w,h,d]) => ({x,z,w,h,d}));
const WEAPONS = [{cap:30,reserve:120,damage:22,delay:.115,reload:1.7,pellets:1,spread:.009,range:75},{cap:6,reserve:30,damage:11,delay:.8,reload:2.1,pellets:8,spread:.08,range:30}];
const LOOT = [[-4,25,'ammo'],[4,25,'kit'],[-13,-14,'ammo'],[6,-16,'armor'],[24,-11,'ammo'],[-25,4,'kit'],[12,7,'ammo'],[-6,-13,'kit'],[11,26,'armor'],[-19,24,'ammo'],[26,14,'kit'],[-25,-20,'armor'],[1,0,'ammo'],[4,3,'armor']];
const SPAWNS = [[-20,29],[20,29],[-20,-29],[20,-29]];
const STATIC_FILES = new Set(['zona-zero.html','corrida-neon.html','orbita-infinita.html','index.html']);
const ACTIONS = new Set(['jump','reload','heal','start']);
const INPUT_KEYS = new Set(['token','seq','moveX','moveY','yaw','pitch','shoot','sprint','ads','weapon','actions']);
const clamp = (v,a,b) => Math.max(a,Math.min(b,v));
const neutral = () => ({moveX:0,moveY:0,yaw:0,pitch:0,shoot:false,sprint:false,ads:false,weapon:0});
const radius = room => Math.max(3,46-Math.max(0,room.time-18)*.22);
const now = () => performance.now();
const connected = (p,timestamp = now()) => p.streams.size > 0 || p.websockets.size > 0 || timestamp-p.lastPoll < 1500;

function wsFrame(value,opcode = 1) {
  const payload = Buffer.isBuffer(value) ? value : Buffer.from(value);
  const header = Buffer.alloc(payload.length<126?2:payload.length<=65535?4:10);
  header[0]=0x80|opcode;
  if(payload.length<126)header[1]=payload.length;
  else if(payload.length<=65535){header[1]=126;header.writeUInt16BE(payload.length,2);}
  else{header[1]=127;header.writeBigUInt64BE(BigInt(payload.length),2);}
  return Buffer.concat([header,payload]);
}

function rayBox(origin,direction,min,max) {
  let near = 0, far = Infinity;
  for (let i = 0; i < 3; i++) {
    if (Math.abs(direction[i]) < 1e-8) { if (origin[i] < min[i] || origin[i] > max[i]) return Infinity; }
    else {
      let a = (min[i]-origin[i])/direction[i], b = (max[i]-origin[i])/direction[i];
      if (a > b) [a,b] = [b,a];
      near = Math.max(near,a); far = Math.min(far,b);
      if (near > far) return Infinity;
    }
  }
  return far < 0 ? Infinity : near;
}
function wallDistance(origin,direction) {
  let distance = Infinity;
  for (const b of COVERS) distance = Math.min(distance,rayBox(origin,direction,[b.x-b.w/2,0,b.z-b.d/2],[b.x+b.w/2,b.h,b.z+b.d/2]));
  if (direction[1] < 0) distance = Math.min(distance,-origin[1]/direction[1]);
  return distance;
}
function insideCover(b,x,z,r = .45) { return Math.abs(x-b.x) < b.w/2+r && Math.abs(z-b.z) < b.d/2+r; }
function blocked(p,x,z) {
  return Math.abs(x) > 34.55 || Math.abs(z) > 34.55 || COVERS.some(b => insideCover(b,x,z) && p.y < b.h-.025 && p.y+1.85 > 0);
}
function move(p,dx,dz) {
  // Axis separation lets a player slide along cover without crossing corners.
  if (!blocked(p,p.x+dx,p.z)) p.x += dx;
  if (!blocked(p,p.x,p.z+dz)) p.z += dz;
}
function resetPlayer(p,index) {
  const [x,z] = SPAWNS[index % SPAWNS.length];
  Object.assign(p,{x,y:0,z,vy:0,hp:100,armor:35,stamina:100,sprinting:false,yaw:z>0?0:Math.PI,pitch:0,weapon:0,guns:WEAPONS.map(w => ({mag:w.cap,reserve:w.reserve})),kits:2,reload:0,cooldown:0,kills:0,shotId:0,grounded:true,jumpBase:0,input:neutral(),actions:[],lastInput:0});
}
function publicPlayer(p) {
  const {id,name,x,y,z,vy,hp,armor,stamina,sprinting,yaw,pitch,weapon,guns,kits,reload,cooldown,kills,shotId} = p;
  return {id,name,x,y,z,vy,hp,armor,stamina,sprinting,yaw,pitch,weapon,guns,kits,reload,cooldown,kills,shotId};
}
function snapshot(room) {
  return {room:room.code,phase:room.phase,time:room.time,radius:radius(room),hostId:room.hostId,winnerId:room.winnerId,players:[...room.players.values()].map(publicPlayer),loot:room.loot,tracers:room.tracers.map(({expires,...t})=>t),events:room.events.map(({expires,...e})=>e)};
}
function applyDamage(room,target,amount,source,headshot = false) {
  if (target.hp <= 0) return;
  const absorbed = Math.min(target.armor,amount*.65);
  target.armor -= absorbed; target.hp = Math.max(0,target.hp-amount+absorbed);
  if (source) room.events.push({id:++room.eventId,type:'hit',shooterId:source.id,targetId:target.id,amount,headshot,expires:room.time+.65});
  if (target.hp <= 0) {
    target.sprinting = false; target.reload = 0; target.actions = [];
    if (source && source !== target) { source.kills++; room.loot.push({x:target.x,z:target.z,type:'ammo',taken:false}); }
  }
}
function reload(p) {
  const gun = p.guns[p.weapon], weapon = WEAPONS[p.weapon];
  if (!p.reload && gun.mag < weapon.cap && gun.reserve > 0) p.reload = weapon.reload;
}
function shoot(room,p,input) {
  if (p.cooldown > 0 || p.reload > 0 || p.sprinting) return;
  const weapon = WEAPONS[p.weapon], gun = p.guns[p.weapon];
  if (!gun.mag) { reload(p); return; }
  gun.mag--; p.cooldown = weapon.delay; p.shotId++;
  const origin = [p.x,p.y+1.65,p.z];
  let spread = weapon.spread;
  if (input.ads && p.weapon === 0) spread *= .3;
  if (Math.hypot(input.moveX,input.moveY) > .05) spread *= 2;
  if (!p.grounded) spread *= 2;
  for (let pellet = 0; pellet < weapon.pellets; pellet++) {
    const yaw = p.yaw+(Math.random()*2-1)*spread, pitch = p.pitch+(Math.random()*2-1)*spread;
    const direction = [Math.sin(yaw)*Math.cos(pitch),Math.sin(pitch),-Math.cos(yaw)*Math.cos(pitch)];
    let nearest = Math.min(weapon.range,wallDistance(origin,direction)), target = null;
    for (const other of room.players.values()) {
      if (other === p || other.hp <= 0) continue;
      const distance = rayBox(origin,direction,[other.x-.4,other.y,other.z-.4],[other.x+.4,other.y+1.85,other.z+.4]);
      if (distance < nearest) { nearest = distance; target = other; }
    }
    const to = origin.map((v,i) => v+direction[i]*nearest);
    room.tracers.push({id:++room.tracerId,from:origin,to,shooterId:p.id,expires:room.time+.16});
    if (target) {
      const headshot = to[1] > target.y+1.43;
      const falloff = p.weapon === 1 ? clamp(1-Math.max(0,nearest-12)/24,.25,1) : 1;
      applyDamage(room,target,weapon.damage*falloff*(headshot?(p.weapon===0?1.6:1.15):1),p,headshot);
    }
  }
}
function simulatePlayer(room,p,dt,timestamp) {
  if (p.hp <= 0) return;
  const input = timestamp-p.lastInput <= 250 && connected(p,timestamp) ? p.input : {...neutral(),weapon:p.weapon,yaw:p.yaw,pitch:p.pitch};
  p.yaw = input.yaw; p.pitch = input.pitch;
  p.cooldown = Math.max(0,p.cooldown-dt);
  if (p.weapon !== input.weapon) { p.weapon = input.weapon; p.reload = 0; p.cooldown = Math.max(.2,p.cooldown); }
  if (p.reload > 0) {
    p.reload = Math.max(0,p.reload-dt);
    if (!p.reload) { const gun = p.guns[p.weapon], count = Math.min(WEAPONS[p.weapon].cap-gun.mag,gun.reserve); gun.mag += count; gun.reserve -= count; }
  }
  for (const action of p.actions.splice(0)) {
    if (action === 'reload') reload(p);
    if (action === 'heal' && p.kits > 0 && p.hp < 100) { p.kits--; p.hp = Math.min(100,p.hp+55); }
    if (action === 'jump' && p.grounded) { p.vy = 8; p.jumpBase = p.y; p.grounded = false; }
  }
  // Exact ballistic step: 8 m/s with gravity 20 gives a 1.6 m jump.
  const previousY = p.y;
  p.y += p.vy*dt-10*dt*dt; p.vy -= 20*dt;
  if (p.y > p.jumpBase+1.6) { p.y = p.jumpBase+1.6; p.vy = Math.min(0,p.vy); }
  let ground = 0;
  for (const b of COVERS) if (insideCover(b,p.x,p.z) && b.h <= previousY+.025 && p.vy <= 0) ground = Math.max(ground,b.h);
  if (p.y <= ground && p.vy <= 0) { p.y = ground; p.vy = 0; p.grounded = true; p.jumpBase = ground; }
  else p.grounded = false;
  const length = Math.hypot(input.moveX,input.moveY), moving = length > .01;
  p.sprinting = moving && input.sprint && !input.ads && !input.shoot && !p.reload && p.stamina > 0;
  p.stamina = clamp(p.stamina+(p.sprinting?-22:16)*dt,0,100);
  if (moving) {
    const speed = (p.sprinting?8:input.ads?2.8:4.7)*dt/Math.max(1,length);
    move(p,(Math.cos(p.yaw)*input.moveX+Math.sin(p.yaw)*input.moveY)*speed,(Math.sin(p.yaw)*input.moveX-Math.cos(p.yaw)*input.moveY)*speed);
  }
  if (input.shoot) shoot(room,p,input);
  const outside = Math.hypot(p.x,p.z) > radius(room);
  if (outside || room.time >= 240) applyDamage(room,p,dt*(room.time>=240?35:6+room.time*.04),null);
  if (p.hp <= 0) return;
  for (const loot of room.loot) {
    if (loot.taken || p.y > 1.4 || Math.hypot(loot.x-p.x,loot.z-p.z) >= 1.35) continue;
    loot.taken = true;
    if (loot.type === 'ammo') { p.guns[0].reserve += 36; p.guns[1].reserve += 10; }
    else if (loot.type === 'kit') p.kits++;
    else p.armor = Math.min(75,p.armor+40);
  }
}

function createServer() {
  const rooms = new Map(), tokens = new Map(), joins = new Map();
  let tickCount = 0;
  function urls(req) {
    const port = server.address()?.port || 4177, result = [`http://localhost:${port}`];
    for (const interfaces of Object.values(os.networkInterfaces())) for (const entry of interfaces || []) if (entry.family === 'IPv4' && !entry.internal) result.push(`http://${entry.address}:${port}`);
    if (req) {
      const host = String(req.headers['x-forwarded-host'] || req.headers.host || '').split(',')[0].trim();
      const proto = String(req.headers['x-forwarded-proto'] || 'http').split(',')[0].trim() === 'https' ? 'https' : 'http';
      if (/^[a-zA-Z0-9.:[\]-]+$/.test(host)) result.unshift(`${proto}://${host}`);
    }
    return [...new Set(result)];
  }
  function json(res,status,value) {
    if (res.destroyed || res.writableEnded) return;
    res.writeHead(status,{'Content-Type':'application/json; charset=utf-8','Cache-Control':'no-store','X-Content-Type-Options':'nosniff'}); res.end(JSON.stringify(value));
  }
  function removePlayer(p) {
    const room = rooms.get(p.room);
    tokens.delete(p.token);
    for (const stream of p.streams) stream.end();
    p.streams.clear();
    for (const ws of p.websockets) ws.socket.destroy();
    p.websockets.clear();
    if (!room) return;
    room.players.delete(p.id);
    if (!room.players.size) { rooms.delete(room.code); return; }
    if (room.hostId === p.id) room.hostId = room.players.keys().next().value;
    if (room.winnerId === p.id) room.winnerId = null;
  }
  function broadcast(room) {
    const message = JSON.stringify(snapshot(room)), data = `data: ${message}\n\n`;
    let frame;
    for (const p of room.players.values()) {
      for (const stream of p.streams) {
        if (stream.writableLength > 256*1024) stream.destroy();
        else if (!stream.destroyed && !stream.writableEnded) stream.write(data);
      }
      for (const ws of p.websockets) {
        if(ws.socket.writableLength>256*1024)ws.socket.destroy();
        else if(!ws.socket.destroyed)ws.socket.write(frame || (frame=wsFrame(message)));
      }
    }
  }
  function start(room) {
    room.phase = 'playing'; room.time = 0; room.winnerId = null;
    let index = 0;
    for (const p of room.players.values()) resetPlayer(p,index++);
    room.loot = LOOT.map(([x,z,type])=>({x,z,type,taken:false}));
    room.events = []; room.tracers = [];
  }
  function tick() {
    const timestamp = now(), dt = 1/30;
    for (const p of tokens.values()) {
      for(const ws of p.websockets){
        if(timestamp-ws.lastPong>25000)ws.socket.destroy();
        else if(timestamp-ws.lastPing>10000){ws.lastPing=timestamp;ws.socket.write(wsFrame(Buffer.alloc(0),9));}
      }
      if (!p.streams.size && !p.websockets.size && timestamp-Math.max(p.disconnectedAt,p.lastPoll) > 5000) removePlayer(p);
    }
    for (const room of rooms.values()) {
      if (room.phase === 'playing') {
        room.time += dt;
        for (const p of room.players.values()) simulatePlayer(room,p,dt,timestamp);
        room.tracers = room.tracers.filter(t=>t.expires>room.time);
        room.events = room.events.filter(e=>e.expires>room.time);
        const alive = [...room.players.values()].filter(p=>p.hp>0);
        if (!alive.length || (alive.length === 1 && connected(alive[0],timestamp))) { room.phase = 'ended'; room.endedAt = timestamp; room.winnerId = alive[0]?.id || null; broadcast(room); }
      } else if (room.phase === 'ended' && timestamp-room.endedAt>650) { room.events = []; room.tracers = []; }
      if (tickCount % 2 === 0) broadcast(room);
    }
    tickCount++;
    if (tickCount % 1800 === 0) for (const [ip,entry] of joins) if (timestamp-entry.start>60000) joins.delete(ip);
  }
  function originAllowed(req) {
    const origin = req.headers.origin;
    if (!origin) return true; // Native clients and same-origin GET may omit Origin.
    try {
      const parsed = new URL(origin), hosts = [req.headers.host,req.headers['x-forwarded-host']].filter(Boolean).map(v=>String(v).split(',')[0].trim().toLowerCase());
      return ['http:','https:'].includes(parsed.protocol) && parsed.origin === origin && hosts.includes(parsed.host.toLowerCase());
    } catch { return false; }
  }
  async function body(req) {
    let size = 0, chunks = [];
    if (Number(req.headers['content-length']) > 8192) throw Object.assign(new Error('Pedido muito grande.'),{status:413});
    for await (const chunk of req) {
      size += chunk.length;
      if (size > 8192) throw Object.assign(new Error('Pedido muito grande.'),{status:413});
      chunks.push(chunk);
    }
    let value;
    try { value = JSON.parse(Buffer.concat(chunks).toString('utf8')); } catch { throw Object.assign(new Error('JSON inválido.'),{status:400}); }
    if (!value || typeof value !== 'object' || Array.isArray(value)) throw Object.assign(new Error('Pedido inválido.'),{status:400});
    return value;
  }
  const server = http.createServer(async (req,res) => {
    res.setHeader('Referrer-Policy','no-referrer');
    try {
      const url = new URL(req.url,'http://localhost');
      if (!originAllowed(req)) return json(res,403,{error:'Origem não autorizada.'});
      if (req.method === 'GET' && url.pathname === '/api/info') return json(res,200,{urls:urls(req),maxPlayers:4});
      if (req.method === 'GET' && url.pathname === '/api/state') {
        const p = tokens.get(url.searchParams.get('token'));
        if (!p) return json(res,401,{error:'Sessão expirada. Entre novamente.'});
        p.lastPoll = now();
        return json(res,200,snapshot(rooms.get(p.room)));
      }
      if (req.method === 'GET' && url.pathname === '/api/events') {
        const p = tokens.get(url.searchParams.get('token'));
        if (!p) return json(res,401,{error:'Sessão expirada. Entre novamente.'});
        res.writeHead(200,{'Content-Type':'text/event-stream; charset=utf-8','Cache-Control':'no-cache, no-transform','Connection':'keep-alive','X-Accel-Buffering':'no'});
        // A token has one live stream. Reconnection replaces the previous stream.
        const previous = [...p.streams]; p.streams.add(res);
        for (const stream of previous) { p.streams.delete(stream); stream.end(); }
        res.write(`retry: 1000\ndata: ${JSON.stringify(snapshot(rooms.get(p.room)))}\n\n`);
        res.on('close',()=>{p.streams.delete(res);if(!p.streams.size && !p.websockets.size){p.disconnectedAt=now();p.input=neutral();p.actions=[];}});
        return;
      }
      if (req.method === 'POST' && ['/api/join','/api/input','/api/leave'].includes(url.pathname)) {
        const data = await body(req);
        if (url.pathname === '/api/join') {
          const ip = req.socket.remoteAddress || 'unknown', timestamp = now();
          let entry = joins.get(ip);
          if (!entry || timestamp-entry.start>60000) { entry = {start:timestamp,count:0}; joins.set(ip,entry); }
          if (++entry.count > 60) return json(res,429,{error:'Muitas tentativas. Aguarde um minuto.'});
          if (typeof data.name !== 'string') return json(res,400,{error:'Informe seu nome.'});
          const name = data.name.replace(/[\u0000-\u001f\u007f]/g,'').trim().slice(0,20);
          if (!name) return json(res,400,{error:'Informe seu nome.'});
          let room;
          if (data.create === true) {
            if (rooms.size >= 100) return json(res,503,{error:'Servidor cheio. Tente mais tarde.'});
            let code; do { code = crypto.randomBytes(5).toString('hex').slice(0,6).toUpperCase(); } while (rooms.has(code));
            room = {code,phase:'lobby',time:0,hostId:null,winnerId:null,players:new Map(),loot:[],tracers:[],events:[],eventId:0,tracerId:0};
            rooms.set(code,room);
          } else {
            if (typeof data.room !== 'string' || !/^[a-f0-9]{6}$/i.test(data.room.trim())) return json(res,400,{error:'Código de sala inválido.'});
            room = rooms.get(data.room.trim().toUpperCase());
            if (!room) return json(res,404,{error:'Sala não encontrada.'});
            if (room.phase !== 'lobby') return json(res,409,{error:'A partida já começou. Crie uma nova sala para jogar.'});
            if (room.players.size >= 4) return json(res,409,{error:'Sala cheia: máximo de quatro jogadores.'});
          }
          const p = {id:crypto.randomBytes(8).toString('hex'),token:crypto.randomBytes(24).toString('hex'),name,room:room.code,streams:new Set(),websockets:new Set(),disconnectedAt:timestamp,lastPoll:-Infinity,lastSeq:-1,rateStart:timestamp,rateCount:0};
          resetPlayer(p,room.players.size); room.players.set(p.id,p); tokens.set(p.token,p);
          if (!room.hostId) room.hostId = p.id;
          json(res,200,{token:p.token,id:p.id,room:room.code,host:room.hostId===p.id,urls:urls(req)}); broadcast(room); return;
        }
        const p = typeof data.token === 'string' ? tokens.get(data.token) : null;
        if (!p) return json(res,401,{error:'Sessão expirada. Entre novamente.'});
        if (url.pathname === '/api/leave') { removePlayer(p); return json(res,200,{ok:true}); }
        const room = rooms.get(p.room), timestamp = now();
        if (timestamp-p.rateStart>1000) { p.rateStart=timestamp; p.rateCount=0; }
        if (++p.rateCount>120) return json(res,429,{error:'Controles enviados rápido demais.'});
        if (Object.keys(data).some(key=>!INPUT_KEYS.has(key)) || !Number.isSafeInteger(data.seq) || data.seq<0) return json(res,400,{error:'Controles inválidos.'});
        for (const key of ['moveX','moveY','yaw','pitch']) if (data[key]!==undefined && (typeof data[key]!=='number' || !Number.isFinite(data[key]))) return json(res,400,{error:'Controles inválidos.'});
        for (const key of ['shoot','sprint','ads']) if (data[key]!==undefined && typeof data[key]!=='boolean') return json(res,400,{error:'Controles inválidos.'});
        if (data.weapon!==undefined && data.weapon!==0 && data.weapon!==1) return json(res,400,{error:'Arma inválida.'});
        if (data.actions!==undefined && (!Array.isArray(data.actions) || data.actions.length>5 || data.actions.some(a=>!ACTIONS.has(a)))) return json(res,400,{error:'Ação inválida.'});
        if (data.seq<=p.lastSeq) return json(res,200,{ok:true,duplicate:true});
        const actions = [...new Set(data.actions || [])];
        if (actions.includes('start') && room.phase==='lobby') {
          if (room.hostId!==p.id) return json(res,403,{error:'Somente o anfitrião pode iniciar.'});
          if ([...room.players.values()].filter(player=>connected(player,timestamp)).length<2) return json(res,409,{error:'Aguarde pelo menos dois jogadores conectados.'});
          start(room);
        }
        p.lastSeq=data.seq; p.lastInput=timestamp;
        p.input={moveX:clamp(data.moveX||0,-1,1),moveY:clamp(data.moveY||0,-1,1),yaw:data.yaw===undefined?p.yaw:data.yaw%(Math.PI*2),pitch:clamp(data.pitch===undefined?p.pitch:data.pitch,-1.2,1.2),shoot:data.shoot===true,sprint:data.sprint===true,ads:data.ads===true,weapon:data.weapon===undefined?p.weapon:data.weapon};
        if (room.phase==='playing' && p.hp>0) p.actions.push(...actions.filter(a=>a!=='start').slice(0,Math.max(0,16-p.actions.length)));
        return json(res,200,{ok:true});
      }
      if (req.method === 'GET' || req.method === 'HEAD') {
        const filename = url.pathname === '/' ? 'zona-zero.html' : url.pathname.slice(1);
        if (!STATIC_FILES.has(filename)) return json(res,404,{error:'Página não encontrada.'});
        const file = path.join(__dirname,filename);
        let stat; try { stat=await fs.promises.stat(file); } catch { return json(res,404,{error:'Página não encontrada.'}); }
        res.writeHead(200,{'Content-Type':'text/html; charset=utf-8','Content-Length':stat.size,'Cache-Control':'no-cache','X-Content-Type-Options':'nosniff'});
        if (req.method==='HEAD') return res.end();
        const stream = fs.createReadStream(file); stream.on('error',()=>res.destroy()); stream.pipe(res); return;
      }
      return json(res,404,{error:'Rota não encontrada.'});
    } catch (error) { json(res,error.status || 500,{error:error.status?error.message:'Não foi possível completar o pedido.'}); }
  });
  // Standard WebSocket transport for public reverse proxies. Controls still use
  // the validated POST endpoint; the socket carries snapshots and ping/pong only.
  server.on('upgrade',(req,socket,head)=>{
    const reject=status=>socket.end(`HTTP/1.1 ${status}\r\nConnection: close\r\nContent-Length: 0\r\n\r\n`);
    let url;try{url=new URL(req.url,'http://localhost');}catch{return reject('400 Bad Request');}
    if(url.pathname!=='/api/ws')return reject('404 Not Found');
    if(!originAllowed(req))return reject('403 Forbidden');
    const p=tokens.get(url.searchParams.get('token'));
    if(!p)return reject('401 Unauthorized');
    const key=req.headers['sec-websocket-key'];
    if(req.headers['sec-websocket-version']!=='13' || typeof key!=='string' || !/^[A-Za-z0-9+/]{22}==$/.test(key) || Buffer.from(key,'base64').length!==16 || String(req.headers.upgrade).toLowerCase()!=='websocket')return reject('400 Bad Request');
    const accept=crypto.createHash('sha1').update(key+'258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
    socket.write(`HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ${accept}\r\n\r\n`);
    socket.setNoDelay(true);
    const ws={socket,buffer:Buffer.alloc(0),lastPong:now(),lastPing:now()},previous=[...p.websockets];
    p.websockets.add(ws);for(const old of previous){p.websockets.delete(old);old.socket.destroy();}
    socket.write(wsFrame(JSON.stringify(snapshot(rooms.get(p.room)))));
    socket.on('error',()=>{});
    socket.on('close',()=>{p.websockets.delete(ws);if(!p.streams.size&&!p.websockets.size){p.disconnectedAt=now();p.input=neutral();p.actions=[];}});
    function close(code){const reason=Buffer.alloc(2);reason.writeUInt16BE(code);socket.end(wsFrame(reason,8));}
    function receive(chunk){
      if(socket.writableEnded)return;
      ws.buffer=Buffer.concat([ws.buffer,chunk]);
      if(ws.buffer.length>32768)return close(1009);
      while(ws.buffer.length>=2){
        const first=ws.buffer[0],second=ws.buffer[1],opcode=first&15;
        if((first&0x70)!==0 || !(first&0x80) || !(second&0x80))return close(1002);
        let length=second&127,offset=2;
        if(length===126){if(ws.buffer.length<4)return;length=ws.buffer.readUInt16BE(2);offset=4;}
        else if(length===127){if(ws.buffer.length<10)return;const big=ws.buffer.readBigUInt64BE(2);if(big>8192n)return close(1009);length=Number(big);offset=10;}
        if(length>8192 || (opcode>=8 && length>125))return close(1009);
        if(ws.buffer.length<offset+4+length)return;
        const mask=ws.buffer.subarray(offset,offset+4),payload=Buffer.from(ws.buffer.subarray(offset+4,offset+4+length));
        ws.buffer=ws.buffer.subarray(offset+4+length);
        for(let i=0;i<payload.length;i++)payload[i]^=mask[i%4];
        if(opcode===8){socket.end(wsFrame(payload,8));return;}
        if(opcode===9)socket.write(wsFrame(payload,10));
        else if(opcode===10)ws.lastPong=now();
        else return close(1003);
      }
    }
    socket.on('data',receive);if(head.length)receive(head);
  });
  server.requestTimeout=10000; server.headersTimeout=10000; server.keepAliveTimeout=5000;
  const timer=setInterval(tick,1000/30); timer.unref();
  server.on('close',()=>clearInterval(timer));
  server.lanUrls=()=>urls();
  server.stop=()=>{clearInterval(timer);for(const p of [...tokens.values()])removePlayer(p);return new Promise(resolve=>server.close(resolve));};
  return server;
}

module.exports = {createServer};
if (require.main === module) {
  const port = Number(process.env.PORT) || 4177, server = createServer();
  server.listen(port,'0.0.0.0',()=>{
    console.log('\nZONA ZERO — MULTIPLAYER\n');
    for (const url of server.lanUrls()) console.log(`  ${url}`);
    console.log('\nAbra um endereço, crie uma sala e compartilhe o código.\nNa mesma rede, use o endereço IPv4 deste computador.\nMantenha esta janela aberta. Ctrl+C encerra o servidor.\n');
  });
  server.on('error',error=>{console.error(`Não foi possível iniciar: ${error.message}`);process.exitCode=1;});
  for (const signal of ['SIGINT','SIGTERM']) process.on(signal,()=>server.stop().then(()=>process.exit()));
}
