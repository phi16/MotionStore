"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0/* $fFromAnyCanvas_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(e){return e.getContext(\'2d\');})");
}),
_1/* $fFromAnyCanvas_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(e){return !!e.getContext;})");
}),
_2/* ++ */ = function(_3/* s3hJ */, _4/* s3hK */){
  var _5/* s3hL */ = E(_3/* s3hJ */);
  return (_5/* s3hL */._==0) ? E(_4/* s3hK */) : new T2(1,_5/* s3hL */.a,new T(function(){
    return B(_2/* GHC.Base.++ */(_5/* s3hL */.b, _4/* s3hK */));
  }));
},
_6/* [] */ = __Z/* EXTERNAL */,
_7/* () */ = 0,
_8/* a1 */ = function(_9/* srQf */, _/* EXTERNAL */){
  while(1){
    var _a/* srQh */ = E(_9/* srQf */);
    if(!_a/* srQh */._){
      return _7/* GHC.Tuple.() */;
    }else{
      var _b/* srQj */ = _a/* srQh */.b,
      _c/* srQk */ = E(_a/* srQh */.a);
      switch(_c/* srQk */._){
        case 0:
          var _d/* srQm */ = B(A1(_c/* srQk */.a,_/* EXTERNAL */));
          _9/* srQf */ = B(_2/* GHC.Base.++ */(_b/* srQj */, new T2(1,_d/* srQm */,_6/* GHC.Types.[] */)));
          continue;
        case 1:
          _9/* srQf */ = B(_2/* GHC.Base.++ */(_b/* srQj */, _c/* srQk */.a));
          continue;
        default:
          _9/* srQf */ = _b/* srQj */;
          continue;
      }
    }
  }
},
_e/* $fMonadEventCIO_$sa */ = function(_f/* srQ3 */, _g/* srQ4 */, _/* EXTERNAL */){
  var _h/* srQ6 */ = E(_f/* srQ3 */);
  switch(_h/* srQ6 */._){
    case 0:
      var _i/* srQ8 */ = B(A1(_h/* srQ6 */.a,_/* EXTERNAL */));
      return new F(function(){return _8/* Haste.Concurrent.Monad.a1 */(B(_2/* GHC.Base.++ */(_g/* srQ4 */, new T2(1,_i/* srQ8 */,_6/* GHC.Types.[] */))), _/* EXTERNAL */);});
      break;
    case 1:
      return new F(function(){return _8/* Haste.Concurrent.Monad.a1 */(B(_2/* GHC.Base.++ */(_g/* srQ4 */, _h/* srQ6 */.a)), _/* EXTERNAL */);});
      break;
    default:
      return new F(function(){return _8/* Haste.Concurrent.Monad.a1 */(_g/* srQ4 */, _/* EXTERNAL */);});
  }
},
_j/* $fApplicativeIO1 */ = function(_k/* s3hg */, _l/* s3hh */, _/* EXTERNAL */){
  var _m/* s3hj */ = B(A1(_k/* s3hg */,_/* EXTERNAL */)),
  _n/* s3hm */ = B(A1(_l/* s3hh */,_/* EXTERNAL */));
  return _m/* s3hj */;
},
_o/* $fApplicativeIO2 */ = function(_p/* s3gu */, _q/* s3gv */, _/* EXTERNAL */){
  var _r/* s3gx */ = B(A1(_p/* s3gu */,_/* EXTERNAL */)),
  _s/* s3gA */ = B(A1(_q/* s3gv */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_r/* s3gx */,_s/* s3gA */));
  });
},
_t/* $fFunctorIO1 */ = function(_u/* s3gZ */, _v/* s3h0 */, _/* EXTERNAL */){
  var _w/* s3h2 */ = B(A1(_v/* s3h0 */,_/* EXTERNAL */));
  return _u/* s3gZ */;
},
_x/* $fFunctorIO2 */ = function(_y/* s3gS */, _z/* s3gT */, _/* EXTERNAL */){
  var _A/* s3gV */ = B(A1(_z/* s3gT */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_y/* s3gS */,_A/* s3gV */));
  });
},
_B/* $fFunctorIO */ = new T2(0,_x/* GHC.Base.$fFunctorIO2 */,_t/* GHC.Base.$fFunctorIO1 */),
_C/* returnIO1 */ = function(_D/* s3g7 */, _/* EXTERNAL */){
  return _D/* s3g7 */;
},
_E/* thenIO1 */ = function(_F/* s3g1 */, _G/* s3g2 */, _/* EXTERNAL */){
  var _H/* s3g4 */ = B(A1(_F/* s3g1 */,_/* EXTERNAL */));
  return new F(function(){return A1(_G/* s3g2 */,_/* EXTERNAL */);});
},
_I/* $fApplicativeIO */ = new T5(0,_B/* GHC.Base.$fFunctorIO */,_C/* GHC.Base.returnIO1 */,_o/* GHC.Base.$fApplicativeIO2 */,_E/* GHC.Base.thenIO1 */,_j/* GHC.Base.$fApplicativeIO1 */),
_J/* $fExceptionAllocationLimitExceeded_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_K/* $fExceptionAllocationLimitExceeded_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.IO.Exception"));
}),
_L/* $fExceptionIOException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IOException"));
}),
_M/* $fExceptionIOException_wild */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_J/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww2 */,_K/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww4 */,_L/* GHC.IO.Exception.$fExceptionIOException_ww4 */),
_N/* $fExceptionIOException4 */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_M/* GHC.IO.Exception.$fExceptionIOException_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_O/* $fExceptionIOException3 */ = function(_P/* s3JMf */){
  return E(_N/* GHC.IO.Exception.$fExceptionIOException4 */);
},
_Q/* $p1Exception */ = function(_R/* s2S1H */){
  return E(E(_R/* s2S1H */).a);
},
_S/* cast */ = function(_T/* s25Vy */, _U/* s25Vz */, _V/* s25VA */){
  var _W/* s25VB */ = B(A1(_T/* s25Vy */,_/* EXTERNAL */)),
  _X/* s25VH */ = B(A1(_U/* s25Vz */,_/* EXTERNAL */)),
  _Y/* s25VO */ = hs_eqWord64/* EXTERNAL */(_W/* s25VB */.a, _X/* s25VH */.a);
  if(!_Y/* s25VO */){
    return __Z/* EXTERNAL */;
  }else{
    var _Z/* s25VT */ = hs_eqWord64/* EXTERNAL */(_W/* s25VB */.b, _X/* s25VH */.b);
    return (!_Z/* s25VT */) ? __Z/* EXTERNAL */ : new T1(1,_V/* s25VA */);
  }
},
_10/* $fExceptionIOException_$cfromException */ = function(_11/* s3JQ0 */){
  var _12/* s3JQ1 */ = E(_11/* s3JQ0 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_12/* s3JQ1 */.a)), _O/* GHC.IO.Exception.$fExceptionIOException3 */, _12/* s3JQ1 */.b);});
},
_13/* $fExceptionArrayException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": "));
}),
_14/* $fExceptionIOException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_15/* $fExceptionIOException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" ("));
}),
_16/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("interrupted"));
}),
_17/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("system error"));
}),
_18/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsatisified constraints"));
}),
_19/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("user error"));
}),
_1a/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("permission denied"));
}),
_1b/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("illegal operation"));
}),
_1c/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("end of file"));
}),
_1d/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource exhausted"));
}),
_1e/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource busy"));
}),
_1f/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("does not exist"));
}),
_1g/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("already exists"));
}),
_1h/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource vanished"));
}),
_1i/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("timeout"));
}),
_1j/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsupported operation"));
}),
_1k/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hardware fault"));
}),
_1l/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inappropriate type"));
}),
_1m/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid argument"));
}),
_1n/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("failed"));
}),
_1o/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("protocol error"));
}),
_1p/* $w$cshowsPrec3 */ = function(_1q/* s3JRF */, _1r/* s3JRG */){
  switch(E(_1q/* s3JRF */)){
    case 0:
      return new F(function(){return _2/* GHC.Base.++ */(_1g/* GHC.IO.Exception.lvl19 */, _1r/* s3JRG */);});
      break;
    case 1:
      return new F(function(){return _2/* GHC.Base.++ */(_1f/* GHC.IO.Exception.lvl18 */, _1r/* s3JRG */);});
      break;
    case 2:
      return new F(function(){return _2/* GHC.Base.++ */(_1e/* GHC.IO.Exception.lvl17 */, _1r/* s3JRG */);});
      break;
    case 3:
      return new F(function(){return _2/* GHC.Base.++ */(_1d/* GHC.IO.Exception.lvl16 */, _1r/* s3JRG */);});
      break;
    case 4:
      return new F(function(){return _2/* GHC.Base.++ */(_1c/* GHC.IO.Exception.lvl15 */, _1r/* s3JRG */);});
      break;
    case 5:
      return new F(function(){return _2/* GHC.Base.++ */(_1b/* GHC.IO.Exception.lvl14 */, _1r/* s3JRG */);});
      break;
    case 6:
      return new F(function(){return _2/* GHC.Base.++ */(_1a/* GHC.IO.Exception.lvl13 */, _1r/* s3JRG */);});
      break;
    case 7:
      return new F(function(){return _2/* GHC.Base.++ */(_19/* GHC.IO.Exception.lvl12 */, _1r/* s3JRG */);});
      break;
    case 8:
      return new F(function(){return _2/* GHC.Base.++ */(_18/* GHC.IO.Exception.lvl11 */, _1r/* s3JRG */);});
      break;
    case 9:
      return new F(function(){return _2/* GHC.Base.++ */(_17/* GHC.IO.Exception.lvl10 */, _1r/* s3JRG */);});
      break;
    case 10:
      return new F(function(){return _2/* GHC.Base.++ */(_1o/* GHC.IO.Exception.lvl9 */, _1r/* s3JRG */);});
      break;
    case 11:
      return new F(function(){return _2/* GHC.Base.++ */(_1n/* GHC.IO.Exception.lvl8 */, _1r/* s3JRG */);});
      break;
    case 12:
      return new F(function(){return _2/* GHC.Base.++ */(_1m/* GHC.IO.Exception.lvl7 */, _1r/* s3JRG */);});
      break;
    case 13:
      return new F(function(){return _2/* GHC.Base.++ */(_1l/* GHC.IO.Exception.lvl6 */, _1r/* s3JRG */);});
      break;
    case 14:
      return new F(function(){return _2/* GHC.Base.++ */(_1k/* GHC.IO.Exception.lvl5 */, _1r/* s3JRG */);});
      break;
    case 15:
      return new F(function(){return _2/* GHC.Base.++ */(_1j/* GHC.IO.Exception.lvl4 */, _1r/* s3JRG */);});
      break;
    case 16:
      return new F(function(){return _2/* GHC.Base.++ */(_1i/* GHC.IO.Exception.lvl3 */, _1r/* s3JRG */);});
      break;
    case 17:
      return new F(function(){return _2/* GHC.Base.++ */(_1h/* GHC.IO.Exception.lvl2 */, _1r/* s3JRG */);});
      break;
    default:
      return new F(function(){return _2/* GHC.Base.++ */(_16/* GHC.IO.Exception.lvl1 */, _1r/* s3JRG */);});
  }
},
_1s/* showHandle1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}"));
}),
_1t/* showHandle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("{handle: "));
}),
_1u/* $w$cshowsPrec2 */ = function(_1v/* s3JRO */, _1w/* s3JRP */, _1x/* s3JRQ */, _1y/* s3JRR */, _1z/* s3JRS */, _1A/* s3JRT */){
  var _1B/* s3JRU */ = new T(function(){
    var _1C/* s3JRV */ = new T(function(){
      var _1D/* s3JS1 */ = new T(function(){
        var _1E/* s3JRW */ = E(_1y/* s3JRR */);
        if(!_1E/* s3JRW */._){
          return E(_1A/* s3JRT */);
        }else{
          var _1F/* s3JS0 */ = new T(function(){
            return B(_2/* GHC.Base.++ */(_1E/* s3JRW */, new T(function(){
              return B(_2/* GHC.Base.++ */(_14/* GHC.IO.Exception.$fExceptionIOException1 */, _1A/* s3JRT */));
            },1)));
          },1);
          return B(_2/* GHC.Base.++ */(_15/* GHC.IO.Exception.$fExceptionIOException2 */, _1F/* s3JS0 */));
        }
      },1);
      return B(_1p/* GHC.IO.Exception.$w$cshowsPrec3 */(_1w/* s3JRP */, _1D/* s3JS1 */));
    }),
    _1G/* s3JS2 */ = E(_1x/* s3JRQ */);
    if(!_1G/* s3JS2 */._){
      return E(_1C/* s3JRV */);
    }else{
      return B(_2/* GHC.Base.++ */(_1G/* s3JS2 */, new T(function(){
        return B(_2/* GHC.Base.++ */(_13/* GHC.IO.Exception.$fExceptionArrayException2 */, _1C/* s3JRV */));
      },1)));
    }
  }),
  _1H/* s3JS6 */ = E(_1z/* s3JRS */);
  if(!_1H/* s3JS6 */._){
    var _1I/* s3JS7 */ = E(_1v/* s3JRO */);
    if(!_1I/* s3JS7 */._){
      return E(_1B/* s3JRU */);
    }else{
      var _1J/* s3JS9 */ = E(_1I/* s3JS7 */.a);
      if(!_1J/* s3JS9 */._){
        var _1K/* s3JSe */ = new T(function(){
          var _1L/* s3JSd */ = new T(function(){
            return B(_2/* GHC.Base.++ */(_1s/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_2/* GHC.Base.++ */(_13/* GHC.IO.Exception.$fExceptionArrayException2 */, _1B/* s3JRU */));
            },1)));
          },1);
          return B(_2/* GHC.Base.++ */(_1J/* s3JS9 */.a, _1L/* s3JSd */));
        },1);
        return new F(function(){return _2/* GHC.Base.++ */(_1t/* GHC.IO.Handle.Types.showHandle2 */, _1K/* s3JSe */);});
      }else{
        var _1M/* s3JSk */ = new T(function(){
          var _1N/* s3JSj */ = new T(function(){
            return B(_2/* GHC.Base.++ */(_1s/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_2/* GHC.Base.++ */(_13/* GHC.IO.Exception.$fExceptionArrayException2 */, _1B/* s3JRU */));
            },1)));
          },1);
          return B(_2/* GHC.Base.++ */(_1J/* s3JS9 */.a, _1N/* s3JSj */));
        },1);
        return new F(function(){return _2/* GHC.Base.++ */(_1t/* GHC.IO.Handle.Types.showHandle2 */, _1M/* s3JSk */);});
      }
    }
  }else{
    return new F(function(){return _2/* GHC.Base.++ */(_1H/* s3JS6 */.a, new T(function(){
      return B(_2/* GHC.Base.++ */(_13/* GHC.IO.Exception.$fExceptionArrayException2 */, _1B/* s3JRU */));
    },1));});
  }
},
_1O/* $fExceptionIOException_$cshow */ = function(_1P/* s3JSx */){
  var _1Q/* s3JSy */ = E(_1P/* s3JSx */);
  return new F(function(){return _1u/* GHC.IO.Exception.$w$cshowsPrec2 */(_1Q/* s3JSy */.a, _1Q/* s3JSy */.b, _1Q/* s3JSy */.c, _1Q/* s3JSy */.d, _1Q/* s3JSy */.f, _6/* GHC.Types.[] */);});
},
_1R/* $fExceptionIOException_$ctoException */ = function(_1S/* B1 */){
  return new T2(0,_1T/* GHC.IO.Exception.$fExceptionIOException */,_1S/* B1 */);
},
_1U/* $fExceptionIOException_$cshowsPrec */ = function(_1V/* s3JSn */, _1W/* s3JSo */, _1X/* s3JSp */){
  var _1Y/* s3JSq */ = E(_1W/* s3JSo */);
  return new F(function(){return _1u/* GHC.IO.Exception.$w$cshowsPrec2 */(_1Y/* s3JSq */.a, _1Y/* s3JSq */.b, _1Y/* s3JSq */.c, _1Y/* s3JSq */.d, _1Y/* s3JSq */.f, _1X/* s3JSp */);});
},
_1Z/* $s$dmshow9 */ = function(_20/* s3JSF */, _21/* s3JSG */){
  var _22/* s3JSH */ = E(_20/* s3JSF */);
  return new F(function(){return _1u/* GHC.IO.Exception.$w$cshowsPrec2 */(_22/* s3JSH */.a, _22/* s3JSH */.b, _22/* s3JSH */.c, _22/* s3JSH */.d, _22/* s3JSH */.f, _21/* s3JSG */);});
},
_23/* showList__1 */ = 44,
_24/* showList__2 */ = 93,
_25/* showList__3 */ = 91,
_26/* showList__ */ = function(_27/* sfc7 */, _28/* sfc8 */, _29/* sfc9 */){
  var _2a/* sfca */ = E(_28/* sfc8 */);
  if(!_2a/* sfca */._){
    return new F(function(){return unAppCStr/* EXTERNAL */("[]", _29/* sfc9 */);});
  }else{
    var _2b/* sfcm */ = new T(function(){
      var _2c/* sfcl */ = new T(function(){
        var _2d/* sfce */ = function(_2e/* sfcf */){
          var _2f/* sfcg */ = E(_2e/* sfcf */);
          if(!_2f/* sfcg */._){
            return E(new T2(1,_24/* GHC.Show.showList__2 */,_29/* sfc9 */));
          }else{
            var _2g/* sfck */ = new T(function(){
              return B(A2(_27/* sfc7 */,_2f/* sfcg */.a, new T(function(){
                return B(_2d/* sfce */(_2f/* sfcg */.b));
              })));
            });
            return new T2(1,_23/* GHC.Show.showList__1 */,_2g/* sfck */);
          }
        };
        return B(_2d/* sfce */(_2a/* sfca */.b));
      });
      return B(A2(_27/* sfc7 */,_2a/* sfca */.a, _2c/* sfcl */));
    });
    return new T2(1,_25/* GHC.Show.showList__3 */,_2b/* sfcm */);
  }
},
_2h/* $fShowIOException_$cshowList */ = function(_2i/* s3JSO */, _2j/* s3JSP */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_1Z/* GHC.IO.Exception.$s$dmshow9 */, _2i/* s3JSO */, _2j/* s3JSP */);});
},
_2k/* $fShowIOException */ = new T3(0,_1U/* GHC.IO.Exception.$fExceptionIOException_$cshowsPrec */,_1O/* GHC.IO.Exception.$fExceptionIOException_$cshow */,_2h/* GHC.IO.Exception.$fShowIOException_$cshowList */),
_1T/* $fExceptionIOException */ = new T(function(){
  return new T5(0,_O/* GHC.IO.Exception.$fExceptionIOException3 */,_2k/* GHC.IO.Exception.$fShowIOException */,_1R/* GHC.IO.Exception.$fExceptionIOException_$ctoException */,_10/* GHC.IO.Exception.$fExceptionIOException_$cfromException */,_1O/* GHC.IO.Exception.$fExceptionIOException_$cshow */);
}),
_2l/* $fxExceptionIOException */ = new T(function(){
  return E(_1T/* GHC.IO.Exception.$fExceptionIOException */);
}),
_2m/* toException */ = function(_2n/* s2S1V */){
  return E(E(_2n/* s2S1V */).c);
},
_2o/* Nothing */ = __Z/* EXTERNAL */,
_2p/* UserError */ = 7,
_2q/* userError */ = function(_2r/* s3JMe */){
  return new T6(0,_2o/* GHC.Base.Nothing */,_2p/* GHC.IO.Exception.UserError */,_6/* GHC.Types.[] */,_2r/* s3JMe */,_2o/* GHC.Base.Nothing */,_2o/* GHC.Base.Nothing */);
},
_2s/* failIO1 */ = function(_2t/* s2VEc */, _/* EXTERNAL */){
  var _2u/* s2VEf */ = new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_2l/* GHC.IO.Exception.$fxExceptionIOException */, new T(function(){
      return B(A1(_2q/* GHC.IO.Exception.userError */,_2t/* s2VEc */));
    })));
  });
  return new F(function(){return die/* EXTERNAL */(_2u/* s2VEf */);});
},
_2v/* failIO */ = function(_2w/* B2 */, _/* EXTERNAL */){
  return new F(function(){return _2s/* GHC.IO.failIO1 */(_2w/* B2 */, _/* EXTERNAL */);});
},
_2x/* $fMonadIO_$cfail */ = function(_2y/* s3ek */){
  return new F(function(){return A1(_2v/* GHC.IO.failIO */,_2y/* s3ek */);});
},
_2z/* bindIO1 */ = function(_2A/* s3g9 */, _2B/* s3ga */, _/* EXTERNAL */){
  var _2C/* s3gc */ = B(A1(_2A/* s3g9 */,_/* EXTERNAL */));
  return new F(function(){return A2(_2B/* s3ga */,_2C/* s3gc */, _/* EXTERNAL */);});
},
_2D/* $fMonadIO */ = new T5(0,_I/* GHC.Base.$fApplicativeIO */,_2z/* GHC.Base.bindIO1 */,_E/* GHC.Base.thenIO1 */,_C/* GHC.Base.returnIO1 */,_2x/* GHC.Base.$fMonadIO_$cfail */),
_2E/* id */ = function(_2F/* s3aI */){
  return E(_2F/* s3aI */);
},
_2G/* $fMonadIOIO */ = new T2(0,_2D/* GHC.Base.$fMonadIO */,_2E/* GHC.Base.id */),
_2H/* Stop */ = new T0(2),
_2I/* forkIO1 */ = function(_2J/* srPX */){
  return new T0(2);
},
_2K/* $wa1 */ = function(_2L/* srSf */, _2M/* srSg */, _2N/* srSh */){
  return function(_/* EXTERNAL */){
    var _2O/* srSj */ = E(_2L/* srSf */),
    _2P/* srSl */ = rMV/* EXTERNAL */(_2O/* srSj */),
    _2Q/* srSo */ = E(_2P/* srSl */);
    if(!_2Q/* srSo */._){
      var _2R/* srSw */ = new T(function(){
        var _2S/* srSr */ = new T(function(){
          return B(A1(_2N/* srSh */,_7/* GHC.Tuple.() */));
        });
        return B(_2/* GHC.Base.++ */(_2Q/* srSo */.b, new T2(1,new T2(0,_2M/* srSg */,function(_2T/* srSs */){
          return E(_2S/* srSr */);
        }),_6/* GHC.Types.[] */)));
      }),
      _/* EXTERNAL */ = wMV/* EXTERNAL */(_2O/* srSj */, new T2(0,_2Q/* srSo */.a,_2R/* srSw */));
      return _2H/* Haste.Concurrent.Monad.Stop */;
    }else{
      var _2U/* srSA */ = E(_2Q/* srSo */.a);
      if(!_2U/* srSA */._){
        var _/* EXTERNAL */ = wMV/* EXTERNAL */(_2O/* srSj */, new T2(0,_2M/* srSg */,_6/* GHC.Types.[] */));
        return new T(function(){
          return B(A1(_2N/* srSh */,_7/* GHC.Tuple.() */));
        });
      }else{
        var _/* EXTERNAL */ = wMV/* EXTERNAL */(_2O/* srSj */, new T1(1,_2U/* srSA */.b));
        return new T1(1,new T2(1,new T(function(){
          return B(A1(_2N/* srSh */,_7/* GHC.Tuple.() */));
        }),new T2(1,new T(function(){
          return B(A2(_2U/* srSA */.a,_2M/* srSg */, _2I/* Haste.Concurrent.Monad.forkIO1 */));
        }),_6/* GHC.Types.[] */)));
      }
    }
  };
},
_2V/* liftConc */ = function(_2W/* srPq */){
  return E(E(_2W/* srPq */).b);
},
_2X/* ! */ = function(_2Y/* sJtq */, _2Z/* sJtr */, _30/* sJts */){
  var _31/* sJtt */ = new T(function(){
    return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_2Z/* sJtr */, _30/* sJts */, _2I/* Haste.Concurrent.Monad.forkIO1 */)));
  }),
  _32/* sJtA */ = function(_33/* sJtx */){
    return new T1(1,new T2(1,new T(function(){
      return B(A1(_33/* sJtx */,_7/* GHC.Tuple.() */));
    }),new T2(1,_31/* sJtt */,_6/* GHC.Types.[] */)));
  };
  return new F(function(){return A2(_2V/* Haste.Concurrent.Monad.liftConc */,_2Y/* sJtq */, _32/* sJtA */);});
},
_34/* $fEventMouseEvent2 */ = "deltaZ",
_35/* $fEventMouseEvent3 */ = "deltaY",
_36/* $fEventMouseEvent4 */ = "deltaX",
_37/* itos */ = function(_38/* sfbn */, _39/* sfbo */){
  var _3a/* sfbq */ = jsShowI/* EXTERNAL */(_38/* sfbn */);
  return new F(function(){return _2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_3a/* sfbq */), _39/* sfbo */);});
},
_3b/* shows7 */ = 41,
_3c/* shows8 */ = 40,
_3d/* $wshowSignedInt */ = function(_3e/* sfbv */, _3f/* sfbw */, _3g/* sfbx */){
  if(_3f/* sfbw */>=0){
    return new F(function(){return _37/* GHC.Show.itos */(_3f/* sfbw */, _3g/* sfbx */);});
  }else{
    if(_3e/* sfbv */<=6){
      return new F(function(){return _37/* GHC.Show.itos */(_3f/* sfbw */, _3g/* sfbx */);});
    }else{
      return new T2(1,_3c/* GHC.Show.shows8 */,new T(function(){
        var _3h/* sfbD */ = jsShowI/* EXTERNAL */(_3f/* sfbw */);
        return B(_2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_3h/* sfbD */), new T2(1,_3b/* GHC.Show.shows7 */,_3g/* sfbx */)));
      }));
    }
  }
},
_3i/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_3j/* lvl3 */ = new T(function(){
  return B(_3d/* GHC.Show.$wshowSignedInt */(0, 2, _3i/* Haste.Events.MouseEvents.lvl2 */));
}),
_3k/* lvl4 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */(") is outside of enumeration\'s range (0,", _3j/* Haste.Events.MouseEvents.lvl3 */));
}),
_3l/* $fEnumMouseButton1 */ = function(_3m/* sARK */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("toEnum{MouseButton}: tag (", new T(function(){
    return B(_3d/* GHC.Show.$wshowSignedInt */(0, _3m/* sARK */, _3k/* Haste.Events.MouseEvents.lvl4 */));
  }))));});
},
_3n/* $fEventMouseEvent5 */ = function(_3o/* sAUj */, _/* EXTERNAL */){
  return new T(function(){
    var _3p/* sAUo */ = Number/* EXTERNAL */(E(_3o/* sAUj */)),
    _3q/* sAUs */ = jsTrunc/* EXTERNAL */(_3p/* sAUo */);
    if(_3q/* sAUs */<0){
      return B(_3l/* Haste.Events.MouseEvents.$fEnumMouseButton1 */(_3q/* sAUs */));
    }else{
      if(_3q/* sAUs */>2){
        return B(_3l/* Haste.Events.MouseEvents.$fEnumMouseButton1 */(_3q/* sAUs */));
      }else{
        return _3q/* sAUs */;
      }
    }
  });
},
_3r/* $fEventMouseEvent7 */ = 0,
_3s/* $fEventMouseEvent6 */ = new T3(0,_3r/* Haste.Events.MouseEvents.$fEventMouseEvent7 */,_3r/* Haste.Events.MouseEvents.$fEventMouseEvent7 */,_3r/* Haste.Events.MouseEvents.$fEventMouseEvent7 */),
_3t/* $fEventMouseEvent8 */ = "button",
_3u/* $fEventMouseEvent_f1 */ = new T(function(){
  return eval/* EXTERNAL */("jsGetMouseCoords");
}),
_3v/* $fFromAnyInt2 */ = function(_3w/* sc1d */, _/* EXTERNAL */){
  var _3x/* sc1f */ = E(_3w/* sc1d */);
  if(!_3x/* sc1f */._){
    return _6/* GHC.Types.[] */;
  }else{
    var _3y/* sc1i */ = B(_3v/* Haste.Prim.Any.$fFromAnyInt2 */(_3x/* sc1f */.b, _/* EXTERNAL */));
    return new T2(1,new T(function(){
      var _3z/* sc1o */ = Number/* EXTERNAL */(E(_3x/* sc1f */.a));
      return jsTrunc/* EXTERNAL */(_3z/* sc1o */);
    }),_3y/* sc1i */);
  }
},
_3A/* $wa22 */ = function(_3B/* sc1x */, _/* EXTERNAL */){
  var _3C/* sc1A */ = __arr2lst/* EXTERNAL */(0, _3B/* sc1x */);
  return new F(function(){return _3v/* Haste.Prim.Any.$fFromAnyInt2 */(_3C/* sc1A */, _/* EXTERNAL */);});
},
_3D/* $fFromAnyInt1 */ = function(_3E/* sc1E */, _/* EXTERNAL */){
  return new F(function(){return _3A/* Haste.Prim.Any.$wa22 */(E(_3E/* sc1E */), _/* EXTERNAL */);});
},
_3F/* $fFromAnyInt3 */ = function(_3G/* sbRn */, _/* EXTERNAL */){
  return new T(function(){
    var _3H/* sbRs */ = Number/* EXTERNAL */(E(_3G/* sbRn */));
    return jsTrunc/* EXTERNAL */(_3H/* sbRs */);
  });
},
_3I/* $fFromAnyInt */ = new T2(0,_3F/* Haste.Prim.Any.$fFromAnyInt3 */,_3D/* Haste.Prim.Any.$fFromAnyInt1 */),
_3J/* $fFromAny(,)2 */ = function(_3K/* scdS */, _/* EXTERNAL */){
  var _3L/* scdU */ = E(_3K/* scdS */);
  if(!_3L/* scdU */._){
    return _6/* GHC.Types.[] */;
  }else{
    var _3M/* scdX */ = B(_3J/* Haste.Prim.Any.$fFromAny(,)2 */(_3L/* scdU */.b, _/* EXTERNAL */));
    return new T2(1,_3L/* scdU */.a,_3M/* scdX */);
  }
},
_3N/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));
}),
_3O/* lvl26 */ = new T6(0,_2o/* GHC.Base.Nothing */,_2p/* GHC.IO.Exception.UserError */,_6/* GHC.Types.[] */,_3N/* Haste.Prim.Any.lvl25 */,_2o/* GHC.Base.Nothing */,_2o/* GHC.Base.Nothing */),
_3P/* lvl27 */ = new T(function(){
  return B(_1R/* GHC.IO.Exception.$fExceptionIOException_$ctoException */(_3O/* Haste.Prim.Any.lvl26 */));
}),
_3Q/* $wa3 */ = function(_/* EXTERNAL */){
  return new F(function(){return die/* EXTERNAL */(_3P/* Haste.Prim.Any.lvl27 */);});
},
_3R/* fromAny */ = function(_3S/* sbAf */){
  return E(E(_3S/* sbAf */).a);
},
_3T/* $wa2 */ = function(_3U/* sce1 */, _3V/* sce2 */, _3W/* sce3 */, _/* EXTERNAL */){
  var _3X/* sce6 */ = __arr2lst/* EXTERNAL */(0, _3W/* sce3 */),
  _3Y/* scea */ = B(_3J/* Haste.Prim.Any.$fFromAny(,)2 */(_3X/* sce6 */, _/* EXTERNAL */)),
  _3Z/* sced */ = E(_3Y/* scea */);
  if(!_3Z/* sced */._){
    return new F(function(){return _3Q/* Haste.Prim.Any.$wa3 */(_/* EXTERNAL */);});
  }else{
    var _40/* sceg */ = E(_3Z/* sced */.b);
    if(!_40/* sceg */._){
      return new F(function(){return _3Q/* Haste.Prim.Any.$wa3 */(_/* EXTERNAL */);});
    }else{
      if(!E(_40/* sceg */.b)._){
        var _41/* scek */ = B(A3(_3R/* Haste.Prim.Any.fromAny */,_3U/* sce1 */, _3Z/* sced */.a, _/* EXTERNAL */)),
        _42/* scen */ = B(A3(_3R/* Haste.Prim.Any.fromAny */,_3V/* sce2 */, _40/* sceg */.a, _/* EXTERNAL */));
        return new T2(0,_41/* scek */,_42/* scen */);
      }else{
        return new F(function(){return _3Q/* Haste.Prim.Any.$wa3 */(_/* EXTERNAL */);});
      }
    }
  }
},
_43/* lvl2 */ = function(_/* EXTERNAL */){
  return new F(function(){return __jsNull/* EXTERNAL */();});
},
_44/* unsafeDupablePerformIO */ = function(_45/* s2VGr */){
  var _46/* s2VGs */ = B(A1(_45/* s2VGr */,_/* EXTERNAL */));
  return E(_46/* s2VGs */);
},
_47/* nullValue */ = new T(function(){
  return B(_44/* GHC.IO.unsafeDupablePerformIO */(_43/* Haste.Prim.Any.lvl2 */));
}),
_48/* jsNull */ = new T(function(){
  return E(_47/* Haste.Prim.Any.nullValue */);
}),
_49/* $wa */ = function(_4a/* sAV4 */, _4b/* sAV5 */, _/* EXTERNAL */){
  if(E(_4a/* sAV4 */)==7){
    var _4c/* sAVK */ = __app1/* EXTERNAL */(E(_3u/* Haste.Events.MouseEvents.$fEventMouseEvent_f1 */), _4b/* sAV5 */),
    _4d/* sAVN */ = B(_3T/* Haste.Prim.Any.$wa2 */(_3I/* Haste.Prim.Any.$fFromAnyInt */, _3I/* Haste.Prim.Any.$fFromAnyInt */, _4c/* sAVK */, _/* EXTERNAL */)),
    _4e/* sAVT */ = __get/* EXTERNAL */(_4b/* sAV5 */, E(_36/* Haste.Events.MouseEvents.$fEventMouseEvent4 */)),
    _4f/* sAVZ */ = __get/* EXTERNAL */(_4b/* sAV5 */, E(_35/* Haste.Events.MouseEvents.$fEventMouseEvent3 */)),
    _4g/* sAW5 */ = __get/* EXTERNAL */(_4b/* sAV5 */, E(_34/* Haste.Events.MouseEvents.$fEventMouseEvent2 */));
    return new T(function(){
      return new T3(0,E(_4d/* sAVN */),E(_2o/* GHC.Base.Nothing */),E(new T3(0,_4e/* sAVT */,_4f/* sAVZ */,_4g/* sAW5 */)));
    });
  }else{
    var _4h/* sAVb */ = __app1/* EXTERNAL */(E(_3u/* Haste.Events.MouseEvents.$fEventMouseEvent_f1 */), _4b/* sAV5 */),
    _4i/* sAVe */ = B(_3T/* Haste.Prim.Any.$wa2 */(_3I/* Haste.Prim.Any.$fFromAnyInt */, _3I/* Haste.Prim.Any.$fFromAnyInt */, _4h/* sAVb */, _/* EXTERNAL */)),
    _4j/* sAVk */ = __get/* EXTERNAL */(_4b/* sAV5 */, E(_3t/* Haste.Events.MouseEvents.$fEventMouseEvent8 */)),
    _4k/* sAVq */ = __eq/* EXTERNAL */(_4j/* sAVk */, E(_48/* Haste.Prim.Any.jsNull */));
    if(!E(_4k/* sAVq */)){
      var _4l/* sAVz */ = B(_3n/* Haste.Events.MouseEvents.$fEventMouseEvent5 */(_4j/* sAVk */, _/* EXTERNAL */));
      return new T(function(){
        return new T3(0,E(_4i/* sAVe */),E(new T1(1,_4l/* sAVz */)),E(_3s/* Haste.Events.MouseEvents.$fEventMouseEvent6 */));
      });
    }else{
      return new T(function(){
        return new T3(0,E(_4i/* sAVe */),E(_2o/* GHC.Base.Nothing */),E(_3s/* Haste.Events.MouseEvents.$fEventMouseEvent6 */));
      });
    }
  }
},
_4m/* $fEventMouseEvent1 */ = function(_4n/* sAWg */, _4o/* sAWh */, _/* EXTERNAL */){
  return new F(function(){return _49/* Haste.Events.MouseEvents.$wa */(_4n/* sAWg */, E(_4o/* sAWh */), _/* EXTERNAL */);});
},
_4p/* $fEventMouseEvent10 */ = "mouseout",
_4q/* $fEventMouseEvent11 */ = "mouseover",
_4r/* $fEventMouseEvent12 */ = "mousemove",
_4s/* $fEventMouseEvent13 */ = "mouseup",
_4t/* $fEventMouseEvent14 */ = "mousedown",
_4u/* $fEventMouseEvent15 */ = "dblclick",
_4v/* $fEventMouseEvent16 */ = "click",
_4w/* $fEventMouseEvent9 */ = "wheel",
_4x/* $fEventMouseEvent_$ceventName */ = function(_4y/* sASB */){
  switch(E(_4y/* sASB */)){
    case 0:
      return E(_4v/* Haste.Events.MouseEvents.$fEventMouseEvent16 */);
    case 1:
      return E(_4u/* Haste.Events.MouseEvents.$fEventMouseEvent15 */);
    case 2:
      return E(_4t/* Haste.Events.MouseEvents.$fEventMouseEvent14 */);
    case 3:
      return E(_4s/* Haste.Events.MouseEvents.$fEventMouseEvent13 */);
    case 4:
      return E(_4r/* Haste.Events.MouseEvents.$fEventMouseEvent12 */);
    case 5:
      return E(_4q/* Haste.Events.MouseEvents.$fEventMouseEvent11 */);
    case 6:
      return E(_4p/* Haste.Events.MouseEvents.$fEventMouseEvent10 */);
    default:
      return E(_4w/* Haste.Events.MouseEvents.$fEventMouseEvent9 */);
  }
},
_4z/* $fEventMouseEvent */ = new T2(0,_4x/* Haste.Events.MouseEvents.$fEventMouseEvent_$ceventName */,_4m/* Haste.Events.MouseEvents.$fEventMouseEvent1 */),
_4A/* $fIsElemElem1 */ = function(_4B/* sets */, _/* EXTERNAL */){
  return new T1(1,_4B/* sets */);
},
_4C/* $fIsElemElem */ = new T2(0,_2E/* GHC.Base.id */,_4A/* Haste.DOM.Core.$fIsElemElem1 */),
_4D/* $fMonadEventWorld2 */ = function(_4E/* sbYh */){
  var _4F/* sbYi */ = E(_4E/* sbYh */);
  return new T0(2);
},
_4G/* $fMonadConcWorld1 */ = function(_4H/* sbYl */, _4I/* sbYm */, _4J/* sbYn */){
  return new T1(1,new T2(1,new T(function(){
    return B(A1(_4J/* sbYn */,new T2(0,_7/* GHC.Tuple.() */,_4I/* sbYm */)));
  }),new T2(1,new T(function(){
    return B(A2(_4H/* sbYl */,_4I/* sbYm */, _4D/* Core.World.Internal.$fMonadEventWorld2 */));
  }),_6/* GHC.Types.[] */)));
},
_4K/* $fApplicativeWorld1 */ = function(_4L/* sbRQ */, _4M/* sbRR */, _4N/* sbRS */){
  var _4O/* sbRT */ = new T(function(){
    return B(A1(_4L/* sbRQ */,_4N/* sbRS */));
  }),
  _4P/* sbS6 */ = function(_4Q/* sbRU */){
    var _4R/* sbS5 */ = function(_4S/* sbRV */){
      var _4T/* sbRW */ = E(_4S/* sbRV */);
      return new F(function(){return A2(_4M/* sbRR */,_4T/* sbRW */.b, function(_4U/* sbRZ */){
        return new F(function(){return A1(_4Q/* sbRU */,new T2(0,_4T/* sbRW */.a,E(_4U/* sbRZ */).b));});
      });});
    };
    return new F(function(){return A1(_4O/* sbRT */,_4R/* sbS5 */);});
  };
  return E(_4P/* sbS6 */);
},
_4V/* $fApplicativeWorld2 */ = function(_4W/* sbS7 */, _4X/* sbS8 */, _4Y/* sbS9 */){
  var _4Z/* sbSa */ = new T(function(){
    return B(A1(_4W/* sbS7 */,_4Y/* sbS9 */));
  }),
  _50/* sbSm */ = function(_51/* sbSb */){
    var _52/* sbSc */ = function(_53/* sbSd */){
      return new F(function(){return A1(_51/* sbSb */,E(_53/* sbSd */));});
    };
    return new F(function(){return A1(_4Z/* sbSa */,function(_54/* sbSh */){
      return new F(function(){return A2(_4X/* sbS8 */,E(_54/* sbSh */).b, _52/* sbSc */);});
    });});
  };
  return E(_50/* sbSm */);
},
_55/* $fApplicativeWorld3 */ = function(_56/* sbSn */, _57/* sbSo */, _58/* sbSp */){
  var _59/* sbSq */ = new T(function(){
    return B(A1(_56/* sbSn */,_58/* sbSp */));
  }),
  _5a/* sbSE */ = function(_5b/* sbSr */){
    var _5c/* sbSD */ = function(_5d/* sbSs */){
      var _5e/* sbSt */ = E(_5d/* sbSs */),
      _5f/* sbSC */ = function(_5g/* sbSw */){
        var _5h/* sbSx */ = E(_5g/* sbSw */);
        return new F(function(){return A1(_5b/* sbSr */,new T2(0,new T(function(){
          return B(A1(_5e/* sbSt */.a,_5h/* sbSx */.a));
        }),_5h/* sbSx */.b));});
      };
      return new F(function(){return A2(_57/* sbSo */,_5e/* sbSt */.b, _5f/* sbSC */);});
    };
    return new F(function(){return A1(_59/* sbSq */,_5c/* sbSD */);});
  };
  return E(_5a/* sbSE */);
},
_5i/* $fFunctorWorld1 */ = function(_5j/* sbUu */, _5k/* sbUv */, _5l/* sbUw */){
  var _5m/* sbUx */ = new T(function(){
    return B(A1(_5k/* sbUv */,_5l/* sbUw */));
  }),
  _5n/* sbUF */ = function(_5o/* sbUy */){
    var _5p/* sbUE */ = function(_5q/* sbUz */){
      return new F(function(){return A1(_5o/* sbUy */,new T(function(){
        return new T2(0,_5j/* sbUu */,E(_5q/* sbUz */).b);
      }));});
    };
    return new F(function(){return A1(_5m/* sbUx */,_5p/* sbUE */);});
  };
  return E(_5n/* sbUF */);
},
_5r/* $fFunctorWorld2 */ = function(_5s/* sbUh */, _5t/* sbUi */, _5u/* sbUj */){
  var _5v/* sbUk */ = new T(function(){
    return B(A1(_5t/* sbUi */,_5u/* sbUj */));
  }),
  _5w/* sbUt */ = function(_5x/* sbUl */){
    var _5y/* sbUs */ = function(_5z/* sbUm */){
      var _5A/* sbUr */ = new T(function(){
        var _5B/* sbUn */ = E(_5z/* sbUm */);
        return new T2(0,new T(function(){
          return B(A1(_5s/* sbUh */,_5B/* sbUn */.a));
        }),_5B/* sbUn */.b);
      });
      return new F(function(){return A1(_5x/* sbUl */,_5A/* sbUr */);});
    };
    return new F(function(){return A1(_5v/* sbUk */,_5y/* sbUs */);});
  };
  return E(_5w/* sbUt */);
},
_5C/* $fFunctorWorld */ = new T2(0,_5r/* Core.World.Internal.$fFunctorWorld2 */,_5i/* Core.World.Internal.$fFunctorWorld1 */),
_5D/* $fMonadWorld2 */ = function(_5E/* sbQW */, _5F/* sbQX */, _5G/* sbQY */){
  return new F(function(){return A1(_5G/* sbQY */,new T2(0,_5E/* sbQW */,_5F/* sbQX */));});
},
_5H/* $fApplicativeWorld */ = new T5(0,_5C/* Core.World.Internal.$fFunctorWorld */,_5D/* Core.World.Internal.$fMonadWorld2 */,_55/* Core.World.Internal.$fApplicativeWorld3 */,_4V/* Core.World.Internal.$fApplicativeWorld2 */,_4K/* Core.World.Internal.$fApplicativeWorld1 */),
_5I/* $fMonadWorld1 */ = function(_5J/* sbRO */, _5K/* sbRP */){
  return new F(function(){return err/* EXTERNAL */(_5J/* sbRO */);});
},
_5L/* $c>>=1 */ = function(_5M/* srPQ */, _5N/* srPR */, _5O/* srPS */){
  return new F(function(){return A1(_5M/* srPQ */,function(_5P/* srPT */){
    return new F(function(){return A2(_5N/* srPR */,_5P/* srPT */, _5O/* srPS */);});
  });});
},
_5Q/* $fApplicativeCIO1 */ = function(_5R/* srTS */, _5S/* srTT */, _5T/* srTU */){
  var _5U/* srTZ */ = function(_5V/* srTV */){
    var _5W/* srTW */ = new T(function(){
      return B(A1(_5T/* srTU */,_5V/* srTV */));
    });
    return new F(function(){return A1(_5S/* srTT */,function(_5X/* srTX */){
      return E(_5W/* srTW */);
    });});
  };
  return new F(function(){return A1(_5R/* srTS */,_5U/* srTZ */);});
},
_5Y/* $fApplicativeCIO2 */ = function(_5Z/* srTK */, _60/* srTL */, _61/* srTM */){
  var _62/* srTN */ = new T(function(){
    return B(A1(_60/* srTL */,function(_63/* srTO */){
      return new F(function(){return A1(_61/* srTM */,_63/* srTO */);});
    }));
  });
  return new F(function(){return A1(_5Z/* srTK */,function(_64/* srTQ */){
    return E(_62/* srTN */);
  });});
},
_65/* $fApplicativeCIO3 */ = function(_66/* srQt */, _67/* srQu */, _68/* srQv */){
  var _69/* srQA */ = function(_6a/* srQw */){
    var _6b/* srQz */ = function(_6c/* srQx */){
      return new F(function(){return A1(_68/* srQv */,new T(function(){
        return B(A1(_6a/* srQw */,_6c/* srQx */));
      }));});
    };
    return new F(function(){return A1(_67/* srQu */,_6b/* srQz */);});
  };
  return new F(function(){return A1(_66/* srQt */,_69/* srQA */);});
},
_6d/* $fApplicativeCIO4 */ = function(_6e/* srPV */, _6f/* srPW */){
  return new F(function(){return A1(_6f/* srPW */,_6e/* srPV */);});
},
_6g/* $fFunctorCIO1 */ = function(_6h/* srTE */, _6i/* srTF */, _6j/* srTG */){
  var _6k/* srTH */ = new T(function(){
    return B(A1(_6j/* srTG */,_6h/* srTE */));
  });
  return new F(function(){return A1(_6i/* srTF */,function(_6l/* srTI */){
    return E(_6k/* srTH */);
  });});
},
_6m/* $fFunctorCIO2 */ = function(_6n/* srPK */, _6o/* srPL */, _6p/* srPM */){
  var _6q/* srPP */ = function(_6r/* srPN */){
    return new F(function(){return A1(_6p/* srPM */,new T(function(){
      return B(A1(_6n/* srPK */,_6r/* srPN */));
    }));});
  };
  return new F(function(){return A1(_6o/* srPL */,_6q/* srPP */);});
},
_6s/* $fFunctorCIO */ = new T2(0,_6m/* Haste.Concurrent.Monad.$fFunctorCIO2 */,_6g/* Haste.Concurrent.Monad.$fFunctorCIO1 */),
_6t/* $fApplicativeCIO */ = new T5(0,_6s/* Haste.Concurrent.Monad.$fFunctorCIO */,_6d/* Haste.Concurrent.Monad.$fApplicativeCIO4 */,_65/* Haste.Concurrent.Monad.$fApplicativeCIO3 */,_5Y/* Haste.Concurrent.Monad.$fApplicativeCIO2 */,_5Q/* Haste.Concurrent.Monad.$fApplicativeCIO1 */),
_6u/* >>= */ = function(_6v/* s34V */){
  return E(E(_6v/* s34V */).b);
},
_6w/* $fMonadCIO_$c>> */ = function(_6x/* srU1 */, _6y/* srU2 */){
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_6z/* Haste.Concurrent.Monad.$fMonadCIO */, _6x/* srU1 */, function(_6A/* srU3 */){
    return E(_6y/* srU2 */);
  });});
},
_6B/* a5 */ = function(_6C/* srU0 */){
  return new F(function(){return err/* EXTERNAL */(_6C/* srU0 */);});
},
_6z/* $fMonadCIO */ = new T(function(){
  return new T5(0,_6t/* Haste.Concurrent.Monad.$fApplicativeCIO */,_5L/* Haste.Concurrent.Monad.$c>>=1 */,_6w/* Haste.Concurrent.Monad.$fMonadCIO_$c>> */,_6d/* Haste.Concurrent.Monad.$fApplicativeCIO4 */,_6B/* Haste.Concurrent.Monad.a5 */);
}),
_6D/* $fMonadStateT2 */ = function(_6E/* s9IC */, _6F/* s9ID */, _6G/* s9IE */, _6H/* s9IF */, _6I/* s9IG */){
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_6F/* s9ID */, new T(function(){
    return B(A1(_6G/* s9IE */,_6I/* s9IG */));
  }), function(_6J/* s9II */){
    var _6K/* s9IJ */ = E(_6J/* s9II */);
    return new F(function(){return A2(_6H/* s9IF */,_6K/* s9IJ */.a, _6K/* s9IJ */.b);});
  });});
},
_6L/* fail */ = function(_6M/* s35g */){
  return E(E(_6M/* s35g */).e);
},
_6N/* $fMonadStateT_$cfail */ = function(_6O/* s9Ir */, _6P/* s9Is */, _6Q/* s9It */){
  var _6R/* s9Iu */ = new T(function(){
    return B(A2(_6L/* GHC.Base.fail */,_6P/* s9Is */, _6Q/* s9It */));
  });
  return function(_6S/* s9Iv */){
    return E(_6R/* s9Iu */);
  };
},
_6T/* return */ = function(_6U/* s359 */){
  return E(E(_6U/* s359 */).d);
},
_6V/* $fMonadStateT */ = function(_6W/* s9IU */, _6X/* s9IV */){
  return new T5(0,_6W/* s9IU */,function(_6Y/* B3 */, _6Z/* B2 */, _70/* B1 */){
    return new F(function(){return _6D/* Control.Monad.Trans.State.Strict.$fMonadStateT2 */(_6W/* s9IU */, _6X/* s9IV */, _6Y/* B3 */, _6Z/* B2 */, _70/* B1 */);});
  },function(_6Z/* B2 */, _70/* B1 */){
    return new F(function(){return _71/* Control.Monad.Trans.State.Strict.$fMonadStateT_$c>> */(_6W/* s9IU */, _6X/* s9IV */, _6Z/* B2 */, _70/* B1 */);});
  },function(_72/* s9IY */, _73/* s9IZ */){
    return new F(function(){return A2(_6T/* GHC.Base.return */,_6X/* s9IV */, new T2(0,_72/* s9IY */,_73/* s9IZ */));});
  },function(_70/* B1 */){
    return new F(function(){return _6N/* Control.Monad.Trans.State.Strict.$fMonadStateT_$cfail */(_6W/* s9IU */, _6X/* s9IV */, _70/* B1 */);});
  });
},
_71/* $fMonadStateT_$c>> */ = function(_74/* s9IN */, _75/* s9IO */, _76/* s9IP */, _77/* s9IQ */){
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,B(_6V/* Control.Monad.Trans.State.Strict.$fMonadStateT */(_74/* s9IN */, _75/* s9IO */)), _76/* s9IP */, function(_78/* s9IS */){
    return E(_77/* s9IQ */);
  });});
},
_79/* a17 */ = function(_7a/* sbRp */, _7b/* sbRq */, _7c/* sbRr */){
  var _7d/* sbRs */ = new T(function(){
    return B(A1(_7b/* sbRq */,_7c/* sbRr */));
  }),
  _7e/* sbRA */ = function(_7f/* sbRt */){
    var _7g/* sbRz */ = function(_7h/* sbRu */){
      return new F(function(){return A1(_7f/* sbRt */,new T(function(){
        return new T2(0,_7a/* sbRp */,E(_7h/* sbRu */).b);
      }));});
    };
    return new F(function(){return A1(_7d/* sbRs */,_7g/* sbRz */);});
  };
  return E(_7e/* sbRA */);
},
_7i/* a18 */ = function(_7j/* sbRB */, _7k/* sbRC */, _7l/* sbRD */){
  var _7m/* sbRE */ = new T(function(){
    return B(A1(_7k/* sbRC */,_7l/* sbRD */));
  }),
  _7n/* sbRN */ = function(_7o/* sbRF */){
    var _7p/* sbRM */ = function(_7q/* sbRG */){
      var _7r/* sbRL */ = new T(function(){
        var _7s/* sbRH */ = E(_7q/* sbRG */);
        return new T2(0,new T(function(){
          return B(A1(_7j/* sbRB */,_7s/* sbRH */.a));
        }),_7s/* sbRH */.b);
      });
      return new F(function(){return A1(_7o/* sbRF */,_7r/* sbRL */);});
    };
    return new F(function(){return A1(_7m/* sbRE */,_7p/* sbRM */);});
  };
  return E(_7n/* sbRN */);
},
_7t/* $fMonadWorld_$s$fFunctorStateT */ = new T2(0,_7i/* Core.World.Internal.a18 */,_79/* Core.World.Internal.a17 */),
_7u/* a22 */ = function(_7v/* sbSF */, _7w/* sbSG */, _7x/* sbSH */){
  var _7y/* sbSI */ = new T(function(){
    return B(A1(_7v/* sbSF */,_7x/* sbSH */));
  }),
  _7z/* sbSW */ = function(_7A/* sbSJ */){
    var _7B/* sbSV */ = function(_7C/* sbSK */){
      var _7D/* sbSL */ = E(_7C/* sbSK */),
      _7E/* sbSU */ = function(_7F/* sbSO */){
        var _7G/* sbSP */ = E(_7F/* sbSO */);
        return new F(function(){return A1(_7A/* sbSJ */,new T2(0,new T(function(){
          return B(A1(_7D/* sbSL */.a,_7G/* sbSP */.a));
        }),_7G/* sbSP */.b));});
      };
      return new F(function(){return A2(_7w/* sbSG */,_7D/* sbSL */.b, _7E/* sbSU */);});
    };
    return new F(function(){return A1(_7y/* sbSI */,_7B/* sbSV */);});
  };
  return E(_7z/* sbSW */);
},
_7H/* a23 */ = function(_7I/* sbSX */, _7J/* sbSY */, _7K/* sbSZ */){
  var _7L/* sbT0 */ = new T(function(){
    return B(A1(_7I/* sbSX */,_7K/* sbSZ */));
  }),
  _7M/* sbTc */ = function(_7N/* sbT1 */){
    var _7O/* sbT2 */ = function(_7P/* sbT3 */){
      return new F(function(){return A1(_7N/* sbT1 */,E(_7P/* sbT3 */));});
    };
    return new F(function(){return A1(_7L/* sbT0 */,function(_7Q/* sbT7 */){
      return new F(function(){return A2(_7J/* sbSY */,E(_7Q/* sbT7 */).b, _7O/* sbT2 */);});
    });});
  };
  return E(_7M/* sbTc */);
},
_7R/* a24 */ = function(_7S/* sbTd */, _7T/* sbTe */, _7U/* sbTf */){
  var _7V/* sbTg */ = new T(function(){
    return B(A1(_7S/* sbTd */,_7U/* sbTf */));
  }),
  _7W/* sbTt */ = function(_7X/* sbTh */){
    var _7Y/* sbTs */ = function(_7Z/* sbTi */){
      var _80/* sbTj */ = E(_7Z/* sbTi */);
      return new F(function(){return A2(_7T/* sbTe */,_80/* sbTj */.b, function(_81/* sbTm */){
        return new F(function(){return A1(_7X/* sbTh */,new T2(0,_80/* sbTj */.a,E(_81/* sbTm */).b));});
      });});
    };
    return new F(function(){return A1(_7V/* sbTg */,_7Y/* sbTs */);});
  };
  return E(_7W/* sbTt */);
},
_82/* $fMonadWorld_$s$fApplicativeStateT */ = new T5(0,_7t/* Core.World.Internal.$fMonadWorld_$s$fFunctorStateT */,_5D/* Core.World.Internal.$fMonadWorld2 */,_7u/* Core.World.Internal.a22 */,_7H/* Core.World.Internal.a23 */,_7R/* Core.World.Internal.a24 */),
_83/* $fMonadWorld3 */ = function(_84/* B2 */, _85/* B1 */){
  return new F(function(){return _71/* Control.Monad.Trans.State.Strict.$fMonadStateT_$c>> */(_82/* Core.World.Internal.$fMonadWorld_$s$fApplicativeStateT */, _6z/* Haste.Concurrent.Monad.$fMonadCIO */, _84/* B2 */, _85/* B1 */);});
},
_86/* $fMonadWorld5 */ = function(_87/* sbR0 */, _88/* sbR1 */, _89/* sbR2 */){
  var _8a/* sbR3 */ = new T(function(){
    return B(A1(_87/* sbR0 */,_89/* sbR2 */));
  }),
  _8b/* sbRa */ = function(_8c/* sbR4 */){
    return new F(function(){return A1(_8a/* sbR3 */,function(_8d/* sbR5 */){
      var _8e/* sbR6 */ = E(_8d/* sbR5 */);
      return new F(function(){return A3(_88/* sbR1 */,_8e/* sbR6 */.a, _8e/* sbR6 */.b, _8c/* sbR4 */);});
    });});
  };
  return E(_8b/* sbRa */);
},
_8f/* $fMonadWorld */ = new T5(0,_5H/* Core.World.Internal.$fApplicativeWorld */,_86/* Core.World.Internal.$fMonadWorld5 */,_83/* Core.World.Internal.$fMonadWorld3 */,_5D/* Core.World.Internal.$fMonadWorld2 */,_5I/* Core.World.Internal.$fMonadWorld1 */),
_8g/* liftW1 */ = function(_8h/* sbRb */, _8i/* sbRc */, _8j/* sbRd */){
  return new F(function(){return A1(_8h/* sbRb */,function(_8k/* sbRe */){
    return new F(function(){return A1(_8j/* sbRd */,new T2(0,_8k/* sbRe */,_8i/* sbRc */));});
  });});
},
_8l/* $fMonadConcWorld */ = new T3(0,_8f/* Core.World.Internal.$fMonadWorld */,_8g/* Core.World.Internal.liftW1 */,_4G/* Core.World.Internal.$fMonadConcWorld1 */),
_8m/* $fMonadEventWorld1 */ = function(_8n/* sbYN */, _8o/* sbYO */, _8p/* sbYP */){
  var _8q/* sbYT */ = function(_8r/* sbYQ */, _/* EXTERNAL */){
    return new F(function(){return _e/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(new T(function(){
      return B(A3(_8n/* sbYN */,_8r/* sbYQ */, _8o/* sbYO */, _4D/* Core.World.Internal.$fMonadEventWorld2 */));
    }), _6/* GHC.Types.[] */, _/* EXTERNAL */);});
  };
  return new F(function(){return A1(_8p/* sbYP */,new T2(0,_8q/* sbYT */,_8o/* sbYO */));});
},
_8s/* $fMonadIOWorld1 */ = function(_8t/* sbTu */, _8u/* sbTv */, _8v/* sbTw */){
  var _8w/* sbTD */ = function(_/* EXTERNAL */){
    var _8x/* sbTy */ = B(A1(_8t/* sbTu */,_/* EXTERNAL */));
    return new T(function(){
      return B(A1(_8v/* sbTw */,new T2(0,_8x/* sbTy */,_8u/* sbTv */)));
    });
  };
  return new T1(0,_8w/* sbTD */);
},
_8y/* $fMonadIOWorld */ = new T2(0,_8f/* Core.World.Internal.$fMonadWorld */,_8s/* Core.World.Internal.$fMonadIOWorld1 */),
_8z/* $fMonadEventWorld */ = new T2(0,_8y/* Core.World.Internal.$fMonadIOWorld */,_8m/* Core.World.Internal.$fMonadEventWorld1 */),
_8A/* modifyMVarIO2 */ = new T1(1,_6/* GHC.Types.[] */),
_8B/* $wa2 */ = function(_8C/* srQU */, _8D/* srQV */){
  return function(_/* EXTERNAL */){
    var _8E/* srQX */ = E(_8C/* srQU */),
    _8F/* srQZ */ = rMV/* EXTERNAL */(_8E/* srQX */),
    _8G/* srR2 */ = E(_8F/* srQZ */);
    if(!_8G/* srR2 */._){
      var _8H/* srR3 */ = _8G/* srR2 */.a,
      _8I/* srR5 */ = E(_8G/* srR2 */.b);
      if(!_8I/* srR5 */._){
        var _/* EXTERNAL */ = wMV/* EXTERNAL */(_8E/* srQX */, _8A/* Haste.Concurrent.Monad.modifyMVarIO2 */);
        return new T(function(){
          return B(A1(_8D/* srQV */,_8H/* srR3 */));
        });
      }else{
        var _8J/* srRa */ = E(_8I/* srR5 */.a),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_8E/* srQX */, new T2(0,_8J/* srRa */.a,_8I/* srR5 */.b));
        return new T1(1,new T2(1,new T(function(){
          return B(A1(_8D/* srQV */,_8H/* srR3 */));
        }),new T2(1,new T(function(){
          return B(A1(_8J/* srRa */.b,_2I/* Haste.Concurrent.Monad.forkIO1 */));
        }),_6/* GHC.Types.[] */)));
      }
    }else{
      var _8K/* srRr */ = new T(function(){
        var _8L/* srRp */ = function(_8M/* srRl */){
          var _8N/* srRm */ = new T(function(){
            return B(A1(_8D/* srQV */,_8M/* srRl */));
          });
          return function(_8O/* srRn */){
            return E(_8N/* srRm */);
          };
        };
        return B(_2/* GHC.Base.++ */(_8G/* srR2 */.a, new T2(1,_8L/* srRp */,_6/* GHC.Types.[] */)));
      }),
      _/* EXTERNAL */ = wMV/* EXTERNAL */(_8E/* srQX */, new T1(1,_8K/* srRr */));
      return _2H/* Haste.Concurrent.Monad.Stop */;
    }
  };
},
_8P/* $fMonadEventIO */ = new T2(0,_2G/* Control.Monad.IO.Class.$fMonadIOIO */,_C/* GHC.Base.returnIO1 */),
_8Q/* $p1MonadEvent */ = function(_8R/* sppX */){
  return E(E(_8R/* sppX */).a);
},
_8S/* $p1MonadIO */ = function(_8T/* srP */){
  return E(E(_8T/* srP */).a);
},
_8U/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(t,f){window.setInterval(f,t);})");
}),
_8V/* f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(t,f){window.setTimeout(f,t);})");
}),
_8W/* liftIO */ = function(_8X/* srT */){
  return E(E(_8X/* srT */).b);
},
_8Y/* mkHandler */ = function(_8Z/* spq1 */){
  return E(E(_8Z/* spq1 */).b);
},
_90/* setTimer */ = function(_91/* sIX2 */, _92/* sIX3 */, _93/* sIX4 */){
  var _94/* sIX5 */ = B(_8Q/* Haste.Events.Core.$p1MonadEvent */(_91/* sIX2 */)),
  _95/* sIX6 */ = new T(function(){
    return B(_8W/* Control.Monad.IO.Class.liftIO */(_94/* sIX5 */));
  }),
  _96/* sIYd */ = function(_97/* sIXb */){
    var _98/* sIYc */ = function(_/* EXTERNAL */){
      var _99/* sIXd */ = E(_92/* sIX3 */);
      if(!_99/* sIXd */._){
        var _9a/* sIXh */ = B(A1(_97/* sIXb */,_7/* GHC.Tuple.() */)),
        _9b/* sIXq */ = __createJSFunc/* EXTERNAL */(0, function(_/* EXTERNAL */){
          var _9c/* sIXj */ = B(A1(_9a/* sIXh */,_/* EXTERNAL */));
          return _48/* Haste.Prim.Any.jsNull */;
        }),
        _9d/* sIXw */ = __app2/* EXTERNAL */(E(_8V/* Haste.Timer.f2 */), _99/* sIXd */.a, _9b/* sIXq */);
        return new T(function(){
          var _9e/* sIXA */ = Number/* EXTERNAL */(_9d/* sIXw */),
          _9f/* sIXE */ = jsTrunc/* EXTERNAL */(_9e/* sIXA */);
          return new T2(0,_9f/* sIXE */,E(_99/* sIXd */));
        });
      }else{
        var _9g/* sIXL */ = B(A1(_97/* sIXb */,_7/* GHC.Tuple.() */)),
        _9h/* sIXU */ = __createJSFunc/* EXTERNAL */(0, function(_/* EXTERNAL */){
          var _9i/* sIXN */ = B(A1(_9g/* sIXL */,_/* EXTERNAL */));
          return _48/* Haste.Prim.Any.jsNull */;
        }),
        _9j/* sIY0 */ = __app2/* EXTERNAL */(E(_8U/* Haste.Timer.f1 */), _99/* sIXd */.a, _9h/* sIXU */);
        return new T(function(){
          var _9k/* sIY4 */ = Number/* EXTERNAL */(_9j/* sIY0 */),
          _9l/* sIY8 */ = jsTrunc/* EXTERNAL */(_9k/* sIY4 */);
          return new T2(0,_9l/* sIY8 */,E(_99/* sIXd */));
        });
      }
    };
    return new F(function(){return A1(_95/* sIX6 */,_98/* sIYc */);});
  },
  _9m/* sIXa */ = new T(function(){
    return B(A2(_8Y/* Haste.Events.Core.mkHandler */,_91/* sIX2 */, function(_9n/* sIX8 */){
      return E(_93/* sIX4 */);
    }));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,B(_8S/* Control.Monad.IO.Class.$p1MonadIO */(_94/* sIX5 */)), _9m/* sIXa */, _96/* sIYd */);});
},
_9o/* wait2 */ = new T1(1,_6/* GHC.Types.[] */),
_9p/* $wa */ = function(_9q/* sJub */, _9r/* sJuc */){
  return function(_/* EXTERNAL */){
    var _9s/* sJue */ = nMV/* EXTERNAL */(_9o/* Haste.Concurrent.wait2 */),
    _9t/* sJug */ = _9s/* sJue */,
    _9u/* sJux */ = function(_/* EXTERNAL */){
      var _9v/* sJuq */ = function(_/* EXTERNAL */){
        return new F(function(){return _e/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(new T(function(){
          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_9t/* sJug */, _7/* GHC.Tuple.() */, _2I/* Haste.Concurrent.Monad.forkIO1 */)));
        }), _6/* GHC.Types.[] */, _/* EXTERNAL */);});
      },
      _9w/* sJur */ = B(A(_90/* Haste.Timer.setTimer */,[_8P/* Haste.Events.Core.$fMonadEventIO */, new T(function(){
        return new T1(0,E(_9q/* sJub */));
      }), _9v/* sJuq */, _/* EXTERNAL */]));
      return new T(function(){
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_9t/* sJug */, _9r/* sJuc */)));
      });
    };
    return new T1(0,_9u/* sJux */);
  };
},
_9x/* $p1MonadConc */ = function(_9y/* srPl */){
  return E(E(_9y/* srPl */).a);
},
_9z/* >> */ = function(_9A/* s352 */){
  return E(E(_9A/* s352 */).c);
},
_9B/* putMVar1 */ = function(_9C/* srSO */, _9D/* srSP */, _9E/* srSQ */){
  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_9C/* srSO */, _9D/* srSP */, _9E/* srSQ */)));
},
_9F/* takeMVar1 */ = function(_9G/* srRv */, _9H/* srRw */){
  return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_9G/* srRv */, _9H/* srRw */)));
},
_9I/* $wwithMVar */ = function(_9J/* s6e0 */, _9K/* s6e1 */, _9L/* s6e2 */){
  var _9M/* s6e3 */ = new T(function(){
    return B(_2V/* Haste.Concurrent.Monad.liftConc */(_9J/* s6e0 */));
  }),
  _9N/* s6e4 */ = B(_9x/* Haste.Concurrent.Monad.$p1MonadConc */(_9J/* s6e0 */)),
  _9O/* s6e5 */ = function(_9P/* s6e6 */, _9Q/* s6e7 */){
    var _9R/* s6e9 */ = new T(function(){
      return B(A1(_9M/* s6e3 */,function(_9S/* B1 */){
        return new F(function(){return _9B/* Haste.Concurrent.Monad.putMVar1 */(_9K/* s6e1 */, _9Q/* s6e7 */, _9S/* B1 */);});
      }));
    });
    return new F(function(){return A3(_9z/* GHC.Base.>> */,_9N/* s6e4 */, _9R/* s6e9 */, new T(function(){
      return B(A2(_6T/* GHC.Base.return */,_9N/* s6e4 */, _9P/* s6e6 */));
    }));});
  },
  _9T/* s6eb */ = function(_9U/* s6ec */){
    var _9V/* s6ed */ = E(_9U/* s6ec */);
    return new F(function(){return _9O/* s6e5 */(_9V/* s6ed */.a, _9V/* s6ed */.b);});
  },
  _9W/* s6ek */ = function(_9X/* s6ei */){
    return new F(function(){return A3(_6u/* GHC.Base.>>= */,_9N/* s6e4 */, new T(function(){
      return B(A1(_9L/* s6e2 */,_9X/* s6ei */));
    }), _9T/* s6eb */);});
  },
  _9Y/* s6eh */ = new T(function(){
    return B(A2(_2V/* Haste.Concurrent.Monad.liftConc */,_9J/* s6e0 */, function(_9S/* B1 */){
      return new F(function(){return _9F/* Haste.Concurrent.Monad.takeMVar1 */(_9K/* s6e1 */, _9S/* B1 */);});
    }));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_9N/* s6e4 */, _9Y/* s6eh */, _9W/* s6ek */);});
},
_9Z/* a36 */ = function(_a0/* sc3n */, _a1/* sc3o */, _a2/* sc3p */){
  return new F(function(){return A1(_a2/* sc3p */,new T2(0,new T2(0,new T(function(){
    return E(E(_a0/* sc3n */).a);
  }),_a0/* sc3n */),_a1/* sc3o */));});
},
_a3/* a37 */ = 16,
_a4/* a38 */ = function(_a5/* sc3y */, _a6/* sc3z */, _a7/* sc3A */){
  var _a8/* sc3B */ = E(_a5/* sc3y */);
  if(!_a8/* sc3B */._){
    return new F(function(){return A1(_a7/* sc3A */,new T2(0,_6/* GHC.Types.[] */,_a6/* sc3z */));});
  }else{
    var _a9/* sc3T */ = function(_aa/* sc3I */){
      var _ab/* sc3J */ = E(_aa/* sc3I */);
      return new F(function(){return _a4/* Core.World.Internal.a38 */(_a8/* sc3B */.b, _ab/* sc3J */.b, function(_ac/* sc3M */){
        var _ad/* sc3N */ = E(_ac/* sc3M */);
        return new F(function(){return A1(_a7/* sc3A */,new T2(0,new T2(1,_ab/* sc3J */.a,_ad/* sc3N */.a),_ad/* sc3N */.b));});
      });});
    };
    return new F(function(){return A2(E(_a8/* sc3B */.a).a,_a6/* sc3z */, _a9/* sc3T */);});
  }
},
_ae/* a39 */ = function(_af/* sc3U */, _ag/* sc3V */, _ah/* sc3W */){
  var _ai/* sc3X */ = E(_af/* sc3U */);
  if(!_ai/* sc3X */._){
    return new F(function(){return A1(_ah/* sc3W */,new T2(0,_6/* GHC.Types.[] */,_ag/* sc3V */));});
  }else{
    var _aj/* sc41 */ = E(_ai/* sc3X */.a),
    _ak/* sc4g */ = function(_al/* sc44 */){
      var _am/* sc45 */ = E(_al/* sc44 */),
      _an/* sc4f */ = function(_ao/* sc48 */){
        var _ap/* sc49 */ = E(_ao/* sc48 */),
        _aq/* sc4a */ = _ap/* sc49 */.a;
        return new F(function(){return A1(_ah/* sc3W */,new T2(0,new T(function(){
          if(!E(_am/* sc45 */.a)){
            return E(_aq/* sc4a */);
          }else{
            return new T2(1,_aj/* sc41 */,_aq/* sc4a */);
          }
        }),_ap/* sc49 */.b));});
      };
      return new F(function(){return _ae/* Core.World.Internal.a39 */(_ai/* sc3X */.b, _am/* sc45 */.b, _an/* sc4f */);});
    };
    return new F(function(){return A2(_aj/* sc41 */.b,_ag/* sc3V */, _ak/* sc4g */);});
  }
},
_ar/* a */ = function(_as/* sbPN */, _at/* sbPO */, _au/* sbPP */){
  return new F(function(){return A1(_au/* sbPP */,new T2(0,new T2(0,new T(function(){
    return E(_as/* sbPN */).b;
  }),_as/* sbPN */),_at/* sbPO */));});
},
_av/* False */ = false,
_aw/* True */ = true,
_ax/* Nil */ = __Z/* EXTERNAL */,
_ay/* $wincr */ = function(_az/* shjl */, _aA/* shjm */, _aB/* shjn */, _aC/* shjo */){
  var _aD/* shjp */ = E(_aC/* shjo */);
  switch(_aD/* shjp */._){
    case 0:
      return new T3(2,_aA/* shjm */,_aB/* shjn */,_ax/* Data.PQueue.Internals.Nil */);
    case 1:
      return new T3(2,_aA/* shjm */,_aB/* shjn */,_aD/* shjp */.a);
    default:
      var _aE/* shjr */ = _aD/* shjp */.a,
      _aF/* shjs */ = _aD/* shjp */.b,
      _aG/* shjt */ = _aD/* shjp */.c;
      return new T1(1,new T(function(){
        if(!B(A2(_az/* shjl */,_aA/* shjm */, _aE/* shjr */))){
          return B(_ay/* Data.PQueue.Internals.$wincr */(_az/* shjl */, _aE/* shjr */, new T3(0,_aA/* shjm */,_aB/* shjn */,_aF/* shjs */), _aG/* shjt */));
        }else{
          return B(_ay/* Data.PQueue.Internals.$wincr */(_az/* shjl */, _aA/* shjm */, new T3(0,_aE/* shjr */,_aF/* shjs */,_aB/* shjn */), _aG/* shjt */));
        }
      }));
  }
},
_aH/* extractBin */ = function(_aI/* shkM */, _aJ/* shkN */){
  var _aK/* shkO */ = E(_aJ/* shkN */);
  switch(_aK/* shkO */._){
    case 0:
      return __Z/* EXTERNAL */;
    case 1:
      var _aL/* shkQ */ = B(_aH/* Data.PQueue.Internals.extractBin */(_aI/* shkM */, _aK/* shkO */.a));
      if(!_aL/* shkQ */._){
        return __Z/* EXTERNAL */;
      }else{
        var _aM/* shkU */ = E(_aL/* shkQ */.b);
        return new T3(1,_aL/* shkQ */.a,_aM/* shkU */.c,new T3(2,_aM/* shkU */.a,_aM/* shkU */.b,_aL/* shkQ */.c));
      }
      break;
    default:
      var _aN/* shkZ */ = _aK/* shkO */.a,
      _aO/* shl0 */ = _aK/* shkO */.b,
      _aP/* shl1 */ = _aK/* shkO */.c,
      _aQ/* shl2 */ = B(_aH/* Data.PQueue.Internals.extractBin */(_aI/* shkM */, _aP/* shl1 */));
      if(!_aQ/* shl2 */._){
        return new T3(1,_aN/* shkZ */,_aO/* shl0 */,new T1(1,_aP/* shl1 */));
      }else{
        var _aR/* shl4 */ = _aQ/* shl2 */.a,
        _aS/* shl6 */ = _aQ/* shl2 */.c;
        if(!B(A2(_aI/* shkM */,_aN/* shkZ */, _aR/* shl4 */))){
          var _aT/* shl8 */ = E(_aQ/* shl2 */.b),
          _aU/* shl9 */ = _aT/* shl8 */.a,
          _aV/* shla */ = _aT/* shl8 */.b;
          return new T3(1,_aR/* shl4 */,_aT/* shl8 */.c,new T1(1,new T(function(){
            if(!B(A2(_aI/* shkM */,_aN/* shkZ */, _aU/* shl9 */))){
              return B(_ay/* Data.PQueue.Internals.$wincr */(_aI/* shkM */, _aU/* shl9 */, new T3(0,_aN/* shkZ */,_aO/* shl0 */,_aV/* shla */), _aS/* shl6 */));
            }else{
              return B(_ay/* Data.PQueue.Internals.$wincr */(_aI/* shkM */, _aN/* shkZ */, new T3(0,_aU/* shl9 */,_aV/* shla */,_aO/* shl0 */), _aS/* shl6 */));
            }
          })));
        }else{
          return new T3(1,_aN/* shkZ */,_aO/* shl0 */,new T1(1,_aP/* shl1 */));
        }
      }
  }
},
_aW/* a26 */ = function(_aX/* sbTE */){
  var _aY/* sbTF */ = new T(function(){
    var _aZ/* sbTG */ = E(_aX/* sbTE */),
    _b0/* sbTL */ = E(_aZ/* sbTG */.c);
    if(!_b0/* sbTL */._){
      var _b1/* sbTL#result */ = __Z/* EXTERNAL */;
    }else{
      var _b2/* sbU5 */ = B(_aH/* Data.PQueue.Internals.extractBin */(function(_b3/* sbTP */, _b4/* sbTQ */){
        var _b5/* sbTX */ = E(E(_b3/* sbTP */).a),
        _b6/* sbTZ */ = E(E(_b4/* sbTQ */).a);
        return (_b5/* sbTX */>=_b6/* sbTZ */) ? _b5/* sbTX */==_b6/* sbTZ */ : true;
      }, _b0/* sbTL */.c));
      if(!_b2/* sbU5 */._){
        var _b7/* sbU5#result */ = __Z/* EXTERNAL */;
      }else{
        var _b7/* sbU5#result */ = new T3(1,_b0/* sbTL */.a-1|0,_b2/* sbU5 */.a,E(_b2/* sbU5 */.c));
      }
      var _b1/* sbTL#result */ = _b7/* sbU5#result */;
    }
    return new T4(0,E(_aZ/* sbTG */.a),_aZ/* sbTG */.b,E(_b1/* sbTL#result */),E(_aZ/* sbTG */.d));
  });
  return function(_b8/* sbUd */, _b9/* sbUe */){
    return new F(function(){return A1(_b9/* sbUe */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,_aY/* sbTF */),_b8/* sbUd */));});
  };
},
_ba/* a3 */ = function(_bb/* sbQo */, _bc/* sbQp */, _bd/* sbQq */){
  return new F(function(){return A1(_bd/* sbQq */,new T2(0,new T2(0,new T(function(){
    var _be/* sbQw */ = E(E(_bb/* sbQo */).c);
    if(!_be/* sbQw */._){
      return __Z/* EXTERNAL */;
    }else{
      return new T1(1,_be/* sbQw */.b);
    }
  }),_bb/* sbQo */),_bc/* sbQp */));});
},
_bf/* a2 */ = function(_bg/* sbQc */, _bh/* sbQd */, _bi/* sbQe */){
  return new F(function(){return A1(_bi/* sbQe */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
    var _bj/* sbQf */ = E(_bg/* sbQc */);
    return new T4(0,E(_bj/* sbQf */.a),_bj/* sbQf */.b+1|0,E(_bj/* sbQf */.c),E(_bj/* sbQf */.d));
  })),_bh/* sbQd */));});
},
_bk/* a40 */ = function(_bl/* sc4h */, _bm/* sc4i */){
  return new T1(0,B(_bn/* Core.World.Internal.$wa7 */(_bl/* sc4h */)));
},
_bo/* absentError */ = function(_bp/* s4nFP */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Oops!  Entered absent arg ", new T(function(){
    return B(unCStr/* EXTERNAL */(_bp/* s4nFP */));
  }))));});
},
_bq/* eta */ = new T(function(){
  return B(_bo/* Control.Exception.Base.absentError */("w_saPJ ((), MVar WorldState) -> Action"));
}),
_br/* eta1 */ = function(_bs/* sc4l */){
  return new F(function(){return _bk/* Core.World.Internal.a40 */(E(_bs/* sc4l */).b, _bq/* Core.World.Internal.eta */);});
},
_bt/* lvl6 */ = function(_bu/* sc4p */){
  var _bv/* sc4s */ = E(_bu/* sc4p */).b;
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bv/* sc4s */, _bf/* Core.World.Internal.a2 */, _bv/* sc4s */, _br/* Core.World.Internal.eta1 */]);});
},
_bw/* while */ = function(_bx/* s6dH */, _by/* s6dI */){
  var _bz/* s6dJ */ = new T(function(){
    return B(A2(_6T/* GHC.Base.return */,_bx/* s6dH */, _7/* GHC.Tuple.() */));
  }),
  _bA/* s6dK */ = new T(function(){
    return B(_bw/* Core.Util.while */(_bx/* s6dH */, _by/* s6dI */));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_bx/* s6dH */, _by/* s6dI */, function(_bB/* s6dL */){
    return (!E(_bB/* s6dL */)) ? E(_bz/* s6dJ */) : E(_bA/* s6dK */);
  });});
},
_bC/* lvl7 */ = function(_bD/* sc4t */){
  var _bE/* sc4u */ = E(_bD/* sc4t */),
  _bF/* sc52 */ = function(_bG/* sc4x */, _bH/* sc4y */){
    var _bI/* sc4z */ = function(_bJ/* sc4A */){
      return new F(function(){return A1(_bH/* sc4y */,new T2(0,_aw/* GHC.Types.True */,E(_bJ/* sc4A */).b));});
    },
    _bK/* sc51 */ = function(_bL/* sc4F */){
      var _bM/* sc4G */ = E(_bL/* sc4F */),
      _bN/* sc4I */ = _bM/* sc4G */.b,
      _bO/* sc4J */ = E(_bM/* sc4G */.a);
      if(!_bO/* sc4J */._){
        return new F(function(){return A1(_bH/* sc4y */,new T2(0,_av/* GHC.Types.False */,_bN/* sc4I */));});
      }else{
        var _bP/* sc4M */ = E(_bO/* sc4J */.a);
        if(E(_bP/* sc4M */.a)<=E(_bE/* sc4u */.a)){
          var _bQ/* sc4V */ = new T(function(){
            return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bN/* sc4I */, _aW/* Core.World.Internal.a26 */, _bN/* sc4I */, _bI/* sc4z */]));
          });
          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_bP/* sc4M */.b, _7/* GHC.Tuple.() */, function(_bR/* sc4W */){
            return E(_bQ/* sc4V */);
          })));
        }else{
          return new F(function(){return A1(_bH/* sc4y */,new T2(0,_av/* GHC.Types.False */,_bN/* sc4I */));});
        }
      }
    };
    return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bG/* sc4x */, _ba/* Core.World.Internal.a3 */, _bG/* sc4x */, _bK/* sc51 */]);});
  };
  return new F(function(){return A(_bw/* Core.Util.while */,[_8f/* Core.World.Internal.$fMonadWorld */, _bF/* sc52 */, _bE/* sc4u */.b, _bt/* Core.World.Internal.lvl6 */]);});
},
_bS/* lvl8 */ = function(_bT/* sc53 */){
  var _bU/* sc56 */ = E(_bT/* sc53 */).b;
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bU/* sc56 */, _ar/* Core.World.Internal.a */, _bU/* sc56 */, _bC/* Core.World.Internal.lvl7 */]);});
},
_bV/* lvl9 */ = function(_bW/* sc57 */){
  var _bX/* sc58 */ = E(_bW/* sc57 */),
  _bY/* sc5a */ = _bX/* sc58 */.b,
  _bZ/* sc5n */ = function(_c0/* sc5b */, _c1/* sc5c */, _c2/* sc5d */){
    return new F(function(){return A1(_c2/* sc5d */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
      var _c3/* sc5e */ = E(_c0/* sc5b */);
      return new T4(0,E(_bX/* sc58 */.a),_c3/* sc5e */.b,E(_c3/* sc5e */.c),E(_c3/* sc5e */.d));
    })),_c1/* sc5c */));});
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bY/* sc5a */, _bZ/* sc5n */, _bY/* sc5a */, _bS/* Core.World.Internal.lvl8 */]);});
},
_c4/* lvl10 */ = function(_c5/* sc5o */){
  var _c6/* sc5p */ = E(_c5/* sc5o */),
  _c7/* sc5q */ = _c6/* sc5p */.a;
  return new F(function(){return _a4/* Core.World.Internal.a38 */(_c7/* sc5q */, _c6/* sc5p */.b, function(_c8/* sc5s */){
    return new F(function(){return _ae/* Core.World.Internal.a39 */(_c7/* sc5q */, E(_c8/* sc5s */).b, _bV/* Core.World.Internal.lvl9 */);});
  });});
},
_bn/* $wa7 */ = function(_c9/* sc5x */){
  var _ca/* sc5y */ = new T(function(){
    return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _c9/* sc5x */, _9Z/* Core.World.Internal.a36 */, _c9/* sc5x */, _c4/* Core.World.Internal.lvl10 */]));
  });
  return new F(function(){return _9p/* Haste.Concurrent.$wa */(_a3/* Core.World.Internal.a37 */, function(_cb/* sc5z */){
    return E(_ca/* sc5y */);
  });});
},
_cc/* MouseDown */ = 2,
_cd/* MouseMove */ = 4,
_ce/* MouseUp */ = 3,
_cf/* a1 */ = function(_cg/* sbPY */, _ch/* sbPZ */, _ci/* sbQ0 */){
  return new F(function(){return A1(_ci/* sbQ0 */,new T2(0,new T2(0,new T(function(){
    return E(E(E(_cg/* sbPY */).d).b);
  }),_cg/* sbPY */),_ch/* sbPZ */));});
},
_cj/* document1 */ = new T(function(){
  return eval/* EXTERNAL */("document");
}),
_ck/* lvl */ = new T1(0,_av/* GHC.Types.False */),
_cl/* lvl1 */ = new T1(0,_aw/* GHC.Types.True */),
_cm/* lvl11 */ = new T1(1,_6/* GHC.Types.[] */),
_cn/* Empty */ = __Z/* EXTERNAL */,
_co/* Nil */ = new T0(2),
_cp/* switch2 */ = 0,
_cq/* lvl12 */ = new T2(0,_cp/* Core.World.Internal.switch2 */,_co/* Data.IntMap.Base.Nil */),
_cr/* lvl13 */ = new T4(0,E(_6/* GHC.Types.[] */),0,E(_cn/* Data.PQueue.Internals.Empty */),E(_cq/* Core.World.Internal.lvl12 */)),
_cs/* lvl14 */ = new T2(0,_cr/* Core.World.Internal.lvl13 */,_6/* GHC.Types.[] */),
_ct/* elemOf */ = function(_cu/* set4 */){
  return E(E(_cu/* set4 */).a);
},
_cv/* eventData */ = function(_cw/* sppT */){
  return E(E(_cw/* sppT */).b);
},
_cx/* eventName */ = function(_cy/* sppP */){
  return E(E(_cy/* sppP */).a);
},
_cz/* lvl3 */ = function(_/* EXTERNAL */){
  return new F(function(){return nMV/* EXTERNAL */(_2o/* GHC.Base.Nothing */);});
},
_cA/* evtRef */ = new T(function(){
  return B(_44/* GHC.IO.unsafeDupablePerformIO */(_cz/* Haste.Events.Core.lvl3 */));
}),
_cB/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");
}),
_cC/* onEvent */ = function(_cD/* spqw */, _cE/* spqx */, _cF/* spqy */, _cG/* spqz */, _cH/* spqA */, _cI/* spqB */){
  var _cJ/* spqC */ = B(_8Q/* Haste.Events.Core.$p1MonadEvent */(_cD/* spqw */)),
  _cK/* spqD */ = B(_8S/* Control.Monad.IO.Class.$p1MonadIO */(_cJ/* spqC */)),
  _cL/* spqE */ = new T(function(){
    return B(_8W/* Control.Monad.IO.Class.liftIO */(_cJ/* spqC */));
  }),
  _cM/* spqF */ = new T(function(){
    return B(_6T/* GHC.Base.return */(_cK/* spqD */));
  }),
  _cN/* spqG */ = new T(function(){
    return B(A2(_ct/* Haste.DOM.Core.elemOf */,_cE/* spqx */, _cG/* spqz */));
  }),
  _cO/* spqH */ = new T(function(){
    return B(A2(_cx/* Haste.Events.Core.eventName */,_cF/* spqy */, _cH/* spqA */));
  }),
  _cP/* spqI */ = function(_cQ/* spqJ */){
    return new F(function(){return A1(_cM/* spqF */,new T3(0,_cO/* spqH */,_cN/* spqG */,_cQ/* spqJ */));});
  },
  _cR/* sprp */ = function(_cS/* spqW */){
    var _cT/* spro */ = new T(function(){
      var _cU/* sprn */ = new T(function(){
        var _cV/* sprb */ = __createJSFunc/* EXTERNAL */(2, function(_cW/* spr2 */, _/* EXTERNAL */){
          var _cX/* spr4 */ = B(A2(E(_cS/* spqW */),_cW/* spr2 */, _/* EXTERNAL */));
          return _48/* Haste.Prim.Any.jsNull */;
        }),
        _cY/* sprd */ = _cV/* sprb */;
        return function(_/* EXTERNAL */){
          return new F(function(){return __app3/* EXTERNAL */(E(_cB/* Haste.Events.Core.f1 */), E(_cN/* spqG */), E(_cO/* spqH */), _cY/* sprd */);});
        };
      });
      return B(A1(_cL/* spqE */,_cU/* sprn */));
    });
    return new F(function(){return A3(_6u/* GHC.Base.>>= */,_cK/* spqD */, _cT/* spro */, _cP/* spqI */);});
  },
  _cZ/* spqV */ = new T(function(){
    var _d0/* spqL */ = new T(function(){
      return B(_8W/* Control.Monad.IO.Class.liftIO */(_cJ/* spqC */));
    }),
    _d1/* spqU */ = function(_d2/* spqM */){
      var _d3/* spqT */ = new T(function(){
        return B(A1(_d0/* spqL */,function(_/* EXTERNAL */){
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(E(_cA/* Haste.Events.Core.evtRef */), new T1(1,_d2/* spqM */));
          return new F(function(){return A(_cv/* Haste.Events.Core.eventData */,[_cF/* spqy */, _cH/* spqA */, _d2/* spqM */, _/* EXTERNAL */]);});
        }));
      });
      return new F(function(){return A3(_6u/* GHC.Base.>>= */,_cK/* spqD */, _d3/* spqT */, _cI/* spqB */);});
    };
    return B(A2(_8Y/* Haste.Events.Core.mkHandler */,_cD/* spqw */, _d1/* spqU */));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_cK/* spqD */, _cZ/* spqV */, _cR/* sprp */);});
},
_d4/* oneway2 */ = function(_d5/* sbPJ */, _d6/* sbPK */){
  return new F(function(){return A1(_d6/* sbPK */,new T2(0,_7/* GHC.Tuple.() */,_d5/* sbPJ */));});
},
_d7/* $wa5 */ = function(_d8/* sc5B */, _d9/* sc5C */){
  return function(_/* EXTERNAL */){
    var _da/* sc5E */ = nMV/* EXTERNAL */(_cs/* Core.World.Internal.lvl14 */),
    _db/* sc5G */ = _da/* sc5E */,
    _dc/* sc5I */ = function(_dd/* sc5J */){
      return new F(function(){return A1(_d9/* sc5C */,E(_dd/* sc5J */).a);});
    },
    _de/* sc5N */ = function(_df/* sc5O */){
      return new F(function(){return A2(_d8/* sc5B */,E(_df/* sc5O */).b, _dc/* sc5I */);});
    },
    _dg/* sc7E */ = function(_/* EXTERNAL */){
      var _dh/* sc5T */ = nMV/* EXTERNAL */(_cm/* Core.World.Internal.lvl11 */),
      _di/* sc5V */ = _dh/* sc5T */,
      _dj/* sc7A */ = new T(function(){
        var _dk/* sc6k */ = function(_dl/* sc6o */){
          return new F(function(){return _dm/* sc6l */(E(_dl/* sc6o */).b);});
        },
        _dm/* sc6l */ = function(_dn/* sc6s */){
          var _do/* sc7x */ = function(_dp/* sc6t */){
            var _dq/* sc7w */ = function(_dr/* sc6u */){
              var _ds/* sc6v */ = E(_dr/* sc6u */),
              _dt/* sc6x */ = _ds/* sc6v */.b,
              _du/* sc6y */ = E(_dp/* sc6t */),
              _dv/* sc6B */ = function(_dw/* sc6C */, _dx/* sc6D */, _dy/* sc6E */){
                var _dz/* sc6F */ = function(_dA/*  sc6G */, _dB/*  sc6H */){
                  while(1){
                    var _dC/*  sc6F */ = B((function(_dD/* sc6G */, _dE/* sc6H */){
                      var _dF/* sc6I */ = E(_dE/* sc6H */);
                      switch(_dF/* sc6I */._){
                        case 0:
                          _dA/*  sc6G */ = new T(function(){
                            return B(_dz/* sc6F */(_dD/* sc6G */, _dF/* sc6I */.d));
                          });
                          _dB/*  sc6H */ = _dF/* sc6I */.c;
                          return __continue/* EXTERNAL */;
                        case 1:
                          var _dG/* sc6Q */ = new T(function(){
                            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _dF/* sc6I */.b, _dw/* sc6C */));
                          }),
                          _dH/* sc70 */ = function(_dI/* sc6R */){
                            var _dJ/* sc6S */ = new T(function(){
                              return B(A1(_dG/* sc6Q */,_dI/* sc6R */));
                            }),
                            _dK/* sc6Z */ = function(_dL/* sc6T */){
                              return new F(function(){return A1(_dJ/* sc6S */,function(_dM/* sc6U */){
                                return new F(function(){return A2(_dD/* sc6G */,E(_dM/* sc6U */).b, _dL/* sc6T */);});
                              });});
                            };
                            return E(_dK/* sc6Z */);
                          };
                          return E(_dH/* sc70 */);
                        default:
                          return E(_dD/* sc6G */);
                      }
                    })(_dA/*  sc6G */, _dB/*  sc6H */));
                    if(_dC/*  sc6F */!=__continue/* EXTERNAL */){
                      return _dC/*  sc6F */;
                    }
                  }
                },
                _dN/* sc71 */ = E(_ds/* sc6v */.a);
                if(!_dN/* sc71 */._){
                  var _dO/* sc74 */ = _dN/* sc71 */.c,
                  _dP/* sc75 */ = _dN/* sc71 */.d;
                  if(_dN/* sc71 */.b>=0){
                    return new F(function(){return A(_dz/* sc6F */,[new T(function(){
                      return B(_dz/* sc6F */(_d4/* Core.World.Internal.oneway2 */, _dP/* sc75 */));
                    }), _dO/* sc74 */, _dx/* sc6D */, _dy/* sc6E */]);});
                  }else{
                    return new F(function(){return A(_dz/* sc6F */,[new T(function(){
                      return B(_dz/* sc6F */(_d4/* Core.World.Internal.oneway2 */, _dO/* sc74 */));
                    }), _dP/* sc75 */, _dx/* sc6D */, _dy/* sc6E */]);});
                  }
                }else{
                  return new F(function(){return A(_dz/* sc6F */,[_d4/* Core.World.Internal.oneway2 */, _dN/* sc71 */, _dx/* sc6D */, _dy/* sc6E */]);});
                }
              };
              switch(E(_du/* sc6y */.a)){
                case 2:
                  return new F(function(){return _dv/* sc6B */(_cl/* Core.World.Internal.lvl1 */, _dt/* sc6x */, _dk/* sc6k */);});
                  break;
                case 3:
                  return new F(function(){return _dv/* sc6B */(_ck/* Core.World.Internal.lvl */, _dt/* sc6x */, _dk/* sc6k */);});
                  break;
                case 4:
                  var _dQ/* sc7b */ = new T(function(){
                    return E(E(_du/* sc6y */.b).a);
                  });
                  return new F(function(){return _dv/* sc6B */(new T1(1,new T2(0,new T(function(){
                    return E(E(_dQ/* sc7b */).a);
                  }),new T(function(){
                    return E(E(_dQ/* sc7b */).b);
                  }))), _dt/* sc6x */, _dk/* sc6k */);});
                  break;
                default:
                  return new F(function(){return _dm/* sc6l */(_dt/* sc6x */);});
              }
            };
            return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _dn/* sc6s */, _cf/* Core.World.Internal.a1 */, _dn/* sc6s */, _dq/* sc7w */]);});
          };
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_di/* sc5V */, _do/* sc7x */)));
        };
        return B(_dm/* sc6l */(_db/* sc5G */));
      }),
      _dR/* sc6i */ = new T(function(){
        var _dS/* sc5X */ = new T(function(){
          return B(_cC/* Haste.Events.Core.onEvent */(_8z/* Core.World.Internal.$fMonadEventWorld */, _4C/* Haste.DOM.Core.$fIsElemElem */, _4z/* Haste.Events.MouseEvents.$fEventMouseEvent */, _cj/* Haste.DOM.Core.document1 */, _cd/* Haste.Events.MouseEvents.MouseMove */, function(_dT/* sc5Y */){
            return new F(function(){return _2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _di/* sc5V */, new T2(0,_cd/* Haste.Events.MouseEvents.MouseMove */,_dT/* sc5Y */));});
          }));
        }),
        _dU/* sc61 */ = new T(function(){
          return B(_cC/* Haste.Events.Core.onEvent */(_8z/* Core.World.Internal.$fMonadEventWorld */, _4C/* Haste.DOM.Core.$fIsElemElem */, _4z/* Haste.Events.MouseEvents.$fEventMouseEvent */, _cj/* Haste.DOM.Core.document1 */, _ce/* Haste.Events.MouseEvents.MouseUp */, function(_dV/* sc62 */){
            return new F(function(){return _2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _di/* sc5V */, new T2(0,_ce/* Haste.Events.MouseEvents.MouseUp */,_dV/* sc62 */));});
          }));
        }),
        _dW/* sc65 */ = function(_dX/* sc66 */){
          return new F(function(){return A2(_dU/* sc61 */,E(_dX/* sc66 */).b, _de/* sc5N */);});
        };
        return B(A(_cC/* Haste.Events.Core.onEvent */,[_8z/* Core.World.Internal.$fMonadEventWorld */, _4C/* Haste.DOM.Core.$fIsElemElem */, _4z/* Haste.Events.MouseEvents.$fEventMouseEvent */, _cj/* Haste.DOM.Core.document1 */, _cc/* Haste.Events.MouseEvents.MouseDown */, function(_dY/* sc6a */){
          return new F(function(){return _2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _di/* sc5V */, new T2(0,_cc/* Haste.Events.MouseEvents.MouseDown */,_dY/* sc6a */));});
        }, _db/* sc5G */, function(_dZ/* sc6d */){
          return new F(function(){return A2(_dS/* sc5X */,E(_dZ/* sc6d */).b, _dW/* sc65 */);});
        }]));
      });
      return new T1(1,new T2(1,_dR/* sc6i */,new T2(1,_dj/* sc7A */,_6/* GHC.Types.[] */)));
    };
    return new T1(1,new T2(1,new T1(0,_dg/* sc7E */),new T2(1,new T(function(){
      return new T1(0,B(_bn/* Core.World.Internal.$wa7 */(_db/* sc5G */)));
    }),_6/* GHC.Types.[] */)));
  };
},
_e0/* elemById_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(id){return document.getElementById(id);})");
}),
_e1/* elemById */ = function(_e2/* sivv */, _e3/* sivw */){
  var _e4/* sivQ */ = function(_/* EXTERNAL */){
    var _e5/* sivD */ = __app1/* EXTERNAL */(E(_e0/* Haste.DOM.JSString.elemById_f1 */), E(_e3/* sivw */)),
    _e6/* sivJ */ = __eq/* EXTERNAL */(_e5/* sivD */, E(_48/* Haste.Prim.Any.jsNull */));
    return (E(_e6/* sivJ */)==0) ? new T1(1,_e5/* sivD */) : _2o/* GHC.Base.Nothing */;
  };
  return new F(function(){return A2(_8W/* Control.Monad.IO.Class.liftIO */,_e2/* sivv */, _e4/* sivQ */);});
},
_e7/* requestAnimationFrame_f1 */ = new T(function(){
  return eval/* EXTERNAL */("window.requestAnimationFrame");
}),
_e8/* $wa */ = function(_e9/* sfBL */, _ea/* sfBM */, _eb/* sfBN */, _ec/* sfBO */){
  return function(_/* EXTERNAL */){
    var _ed/* sfBQ */ = E(_e9/* sfBL */),
    _ee/* sfBS */ = rMV/* EXTERNAL */(_ed/* sfBQ */),
    _ef/* sfBV */ = E(_ee/* sfBS */);
    if(!_ef/* sfBV */._){
      var _eg/* sfBY */ = B(A2(_ea/* sfBM */,_ef/* sfBV */.a, _/* EXTERNAL */)),
      _eh/* sfCK */ = function(_ei/* sfC1 */, _/* EXTERNAL */){
        var _ej/* sfC3 */ = function(_/* EXTERNAL */){
          var _ek/* sfC6 */ = rMV/* EXTERNAL */(_ed/* sfBQ */),
          _el/* sfC9 */ = function(_/* EXTERNAL */, _em/* sfCb */){
            var _en/* sfCc */ = function(_/* EXTERNAL */){
              var _eo/* sfCn */ = __createJSFunc/* EXTERNAL */(2, function(_ep/* sfCe */, _/* EXTERNAL */){
                var _eq/* sfCg */ = B(_er/* sfC4 */(_/* EXTERNAL */, _/* EXTERNAL */));
                return _48/* Haste.Prim.Any.jsNull */;
              }),
              _es/* sfCt */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _eo/* sfCn */);
              return _7/* GHC.Tuple.() */;
            },
            _et/* sfCw */ = E(_em/* sfCb */);
            if(!_et/* sfCw */._){
              return new F(function(){return _en/* sfCc */(_/* EXTERNAL */);});
            }else{
              var _eu/* sfCy */ = B(A2(_ea/* sfBM */,_et/* sfCw */.a, _/* EXTERNAL */));
              return new F(function(){return _en/* sfCc */(_/* EXTERNAL */);});
            }
          },
          _ev/* sfCB */ = E(_ek/* sfC6 */);
          if(!_ev/* sfCB */._){
            return new F(function(){return _el/* sfC9 */(_/* EXTERNAL */, new T1(1,_ev/* sfCB */.a));});
          }else{
            return new F(function(){return _el/* sfC9 */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
        },
        _er/* sfC4 */ = function(_ew/* sfCG */, _/* EXTERNAL */){
          return new F(function(){return _ej/* sfC3 */(_/* EXTERNAL */);});
        },
        _ex/* sfCH */ = B(_er/* sfC4 */(_/* EXTERNAL */, _/* EXTERNAL */));
        return _48/* Haste.Prim.Any.jsNull */;
      },
      _ey/* sfCO */ = __createJSFunc/* EXTERNAL */(2, E(_eh/* sfCK */)),
      _ez/* sfCU */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _ey/* sfCO */);
      return new T(function(){
        return B(A1(_ec/* sfBO */,new T2(0,_7/* GHC.Tuple.() */,_eb/* sfBN */)));
      });
    }else{
      var _eA/* sfDJ */ = function(_eB/* sfD0 */, _/* EXTERNAL */){
        var _eC/* sfD2 */ = function(_/* EXTERNAL */){
          var _eD/* sfD5 */ = rMV/* EXTERNAL */(_ed/* sfBQ */),
          _eE/* sfD8 */ = function(_/* EXTERNAL */, _eF/* sfDa */){
            var _eG/* sfDb */ = function(_/* EXTERNAL */){
              var _eH/* sfDm */ = __createJSFunc/* EXTERNAL */(2, function(_eI/* sfDd */, _/* EXTERNAL */){
                var _eJ/* sfDf */ = B(_eK/* sfD3 */(_/* EXTERNAL */, _/* EXTERNAL */));
                return _48/* Haste.Prim.Any.jsNull */;
              }),
              _eL/* sfDs */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _eH/* sfDm */);
              return _7/* GHC.Tuple.() */;
            },
            _eM/* sfDv */ = E(_eF/* sfDa */);
            if(!_eM/* sfDv */._){
              return new F(function(){return _eG/* sfDb */(_/* EXTERNAL */);});
            }else{
              var _eN/* sfDx */ = B(A2(_ea/* sfBM */,_eM/* sfDv */.a, _/* EXTERNAL */));
              return new F(function(){return _eG/* sfDb */(_/* EXTERNAL */);});
            }
          },
          _eO/* sfDA */ = E(_eD/* sfD5 */);
          if(!_eO/* sfDA */._){
            return new F(function(){return _eE/* sfD8 */(_/* EXTERNAL */, new T1(1,_eO/* sfDA */.a));});
          }else{
            return new F(function(){return _eE/* sfD8 */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
        },
        _eK/* sfD3 */ = function(_eP/* sfDF */, _/* EXTERNAL */){
          return new F(function(){return _eC/* sfD2 */(_/* EXTERNAL */);});
        },
        _eQ/* sfDG */ = B(_eK/* sfD3 */(_/* EXTERNAL */, _/* EXTERNAL */));
        return _48/* Haste.Prim.Any.jsNull */;
      },
      _eR/* sfDN */ = __createJSFunc/* EXTERNAL */(2, E(_eA/* sfDJ */)),
      _eS/* sfDT */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _eR/* sfDN */);
      return new T(function(){
        return B(A1(_ec/* sfBO */,new T2(0,_7/* GHC.Tuple.() */,_eb/* sfBN */)));
      });
    }
  };
},
_eT/* $wlenAcc */ = function(_eU/* s9BT */, _eV/* s9BU */){
  while(1){
    var _eW/* s9BV */ = E(_eU/* s9BT */);
    if(!_eW/* s9BV */._){
      return E(_eV/* s9BU */);
    }else{
      var _eX/*  s9BU */ = _eV/* s9BU */+1|0;
      _eU/* s9BT */ = _eW/* s9BV */.b;
      _eV/* s9BU */ = _eX/*  s9BU */;
      continue;
    }
  }
},
_eY/* a24 */ = function(_eZ/* s7L8 */, _f0/* s7L9 */, _f1/* s7La */){
  return new F(function(){return A1(_f1/* s7La */,new T2(0,new T2(0,_eZ/* s7L8 */,_eZ/* s7L8 */),_f0/* s7L9 */));});
},
_f2/* applyTransform1 */ = 0,
_f3/* applyTransform2 */ = 1,
_f4/* $WEmpty */ = new T1(0,_/* EXTERNAL */),
_f5/* viewL */ = function(_f6/*  sEU */, _f7/*  sEV */, _f8/*  sEW */){
  while(1){
    var _f9/*  viewL */ = B((function(_fa/* sEU */, _fb/* sEV */, _fc/* sEW */){
      var _fd/* sEX */ = E(_fa/* sEU */);
      switch(_fd/* sEX */._){
        case 0:
          return new F(function(){return A1(_fb/* sEV */,_/* EXTERNAL */);});
          break;
        case 1:
          return new F(function(){return A2(_fc/* sEW */,_fd/* sEX */.a, _f4/* Control.Monad.Skeleton.Internal.$WEmpty */);});
          break;
        default:
          var _fe/* sF1 */ = _fd/* sEX */.b,
          _ff/* sFa */ = function(_fg/* sF2 */){
            var _fh/* sF7 */ = function(_fi/* sF3 */){
              return new F(function(){return A1(_fb/* sEV */,new T(function(){
                var _fj/* dBQ */ = E(_fg/* sF2 */),
                _fk/* dBR */ = E(_fi/* sF3 */);
                return _/* EXTERNAL */;
              }));});
            };
            return new F(function(){return _f5/* Control.Monad.Skeleton.Internal.viewL */(_fe/* sF1 */, _fh/* sF7 */, new T(function(){
              var _fl/* dBT */ = E(_fg/* sF2 */);
              return E(_fc/* sEW */);
            }));});
          };
          _f6/*  sEU */ = _fd/* sEX */.a;
          _f7/*  sEV */ = _ff/* sFa */;
          _f8/*  sEW */ = function(_fm/* sFb */, _fn/* sFc */){
            return new F(function(){return A2(_fc/* sEW */,_fm/* sFb */, new T2(2,_fn/* sFc */,_fe/* sF1 */));});
          };
          return __continue/* EXTERNAL */;
      }
    })(_f6/*  sEU */, _f7/*  sEV */, _f8/*  sEW */));
    if(_f9/*  viewL */!=__continue/* EXTERNAL */){
      return _f9/*  viewL */;
    }
  }
},
_fo/* debone */ = function(_fp/* s1Cs */){
  var _fq/* s1Ct */ = E(_fp/* s1Cs */),
  _fr/* s1Cv */ = _fq/* s1Ct */.b,
  _fs/* s1Cw */ = E(_fq/* s1Ct */.a);
  if(!_fs/* s1Cw */._){
    var _ft/* s1Cx */ = _fs/* s1Cw */.a;
    return new F(function(){return _f5/* Control.Monad.Skeleton.Internal.viewL */(_fr/* s1Cv */, function(_fu/* s1Cy */){
      var _fv/* d1o7 */ = E(_fu/* s1Cy */);
      return new T1(0,_ft/* s1Cx */);
    }, function(_fw/* s1CB */, _fx/* s1CC */){
      var _fy/* s1CD */ = B(A1(_fw/* s1CB */,_ft/* s1Cx */));
      return new F(function(){return _fo/* Control.Monad.Skeleton.debone */(new T2(0,E(_fy/* s1CD */.a),E(new T2(2,_fy/* s1CD */.b,_fx/* s1CC */))));});
    });});
  }else{
    return new T2(1,_fs/* s1Cw */.a,function(_fz/* s1CL */){
      var _fA/* s1CM */ = B(A1(_fs/* s1Cw */.b,_fz/* s1CL */));
      return new T2(0,E(_fA/* s1CM */.a),E(new T2(2,_fA/* s1CM */.b,_fr/* s1Cv */)));
    });
  }
},
_fB/* fst */ = function(_fC/* s72P */){
  return E(E(_fC/* s72P */).a);
},
_fD/* valueOf1 */ = function(_fE/* sb3R */, _fF/* sb3S */, _fG/* sb3T */){
  var _fH/* sb3U */ = E(_fE/* sb3R */);
  switch(_fH/* sb3U */._){
    case 0:
      return new F(function(){return _5D/* Core.World.Internal.$fMonadWorld2 */(_fH/* sb3U */.a, _fF/* sb3S */, _fG/* sb3T */);});
      break;
    case 1:
      return new F(function(){return _8s/* Core.World.Internal.$fMonadIOWorld1 */(_fH/* sb3U */.a, _fF/* sb3S */, _fG/* sb3T */);});
      break;
    case 2:
      var _fI/* sb42 */ = E(_fH/* sb3U */.a).c,
      _fJ/* sb4c */ = function(_fK/* sb43 */){
        var _fL/* sb44 */ = new T(function(){
          var _fM/* sb46 */ = new T(function(){
            return B(A1(_fH/* sb3U */.b,new T(function(){
              return B(_fB/* Data.Tuple.fst */(_fK/* sb43 */));
            })));
          });
          return B(A1(_fG/* sb3T */,new T2(0,_fM/* sb46 */,_fF/* sb3S */)));
        });
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_fI/* sb42 */, _fK/* sb43 */, function(_fN/* sb48 */){
          return E(_fL/* sb44 */);
        })));
      };
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_fI/* sb42 */, _fJ/* sb4c */)));
    default:
      var _fO/* sb4k */ = E(_fH/* sb3U */.a).c,
      _fP/* sb4z */ = function(_fQ/* sb4l */){
        var _fR/* sb4m */ = function(_/* EXTERNAL */){
          var _fS/* sb4p */ = B(A2(_fH/* sb3U */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_fQ/* sb4l */));
          }), _/* EXTERNAL */));
          return new T(function(){
            return B(A1(_fG/* sb3T */,new T2(0,_fS/* sb4p */,_fF/* sb3S */)));
          });
        };
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_fO/* sb4k */, _fQ/* sb4l */, function(_fT/* sb4v */){
          return E(new T1(0,_fR/* sb4m */));
        })));
      };
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_fO/* sb4k */, _fP/* sb4z */)));
  }
},
_fU/* applyTransform_world */ = function(_fV/*  sFlZ */, _fW/*  sFm0 */, _fX/*  sFm1 */, _fY/*  sFm2 */, _fZ/*  sFm3 */, _g0/*  sFm4 */, _g1/*  sFm5 */){
  while(1){
    var _g2/*  applyTransform_world */ = B((function(_g3/* sFlZ */, _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */){
      var _ga/* sFm6 */ = new T(function(){
        return 0*E(_g4/* sFm0 */)+0*E(_g5/* sFm1 */)+E(_g6/* sFm2 */);
      }),
      _gb/* sFmh */ = new T(function(){
        return 0*E(_g7/* sFm3 */)+0*E(_g8/* sFm4 */)+E(_g9/* sFm5 */);
      }),
      _gc/* sFms */ = B(_fo/* Control.Monad.Skeleton.debone */(_g3/* sFlZ */));
      if(!_gc/* sFms */._){
        return function(_gd/* _fa_1 */, _ge/* _fa_2 */){
          return new F(function(){return _5D/* Core.World.Internal.$fMonadWorld2 */(_gc/* sFms */.a, _gd/* _fa_1 */, _ge/* _fa_2 */);});
        };
      }else{
        var _gf/* sFmv */ = _gc/* sFms */.b,
        _gg/* sFmw */ = E(_gc/* sFms */.a);
        switch(_gg/* sFmw */._){
          case 0:
            var _gh/*   sFm0 */ = _g4/* sFm0 */,
            _gi/*   sFm1 */ = _g5/* sFm1 */,
            _gj/*   sFm2 */ = _g6/* sFm2 */,
            _gk/*   sFm3 */ = _g7/* sFm3 */,
            _gl/*   sFm4 */ = _g8/* sFm4 */,
            _gm/*   sFm5 */ = _g9/* sFm5 */;
            _fV/*  sFlZ */ = B(A1(_gf/* sFmv */,_gg/* sFmw */.b));
            _fW/*  sFm0 */ = _gh/*   sFm0 */;
            _fX/*  sFm1 */ = _gi/*   sFm1 */;
            _fY/*  sFm2 */ = _gj/*   sFm2 */;
            _fZ/*  sFm3 */ = _gk/*   sFm3 */;
            _g0/*  sFm4 */ = _gl/*   sFm4 */;
            _g1/*  sFm5 */ = _gm/*   sFm5 */;
            return __continue/* EXTERNAL */;
          case 1:
            var _gn/* sFmK */ = function(_go/* sFmB */, _gp/* sFmC */){
              var _gq/* sFmJ */ = function(_/* EXTERNAL */){
                var _gr/* sFmE */ = B(A1(_gg/* sFmw */.a,_/* EXTERNAL */));
                return new T(function(){
                  return B(A(_fU/* Core.Render.Internal.applyTransform_world */,[B(A1(_gf/* sFmv */,_gr/* sFmE */)), _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */, _go/* sFmB */, _gp/* sFmC */]));
                });
              };
              return new T1(0,_gq/* sFmJ */);
            };
            return E(_gn/* sFmK */);
          case 2:
            var _gs/* sFmN */ = new T(function(){
              return B(A(_gg/* sFmw */.a,[_g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */]));
            }),
            _gt/* sFmO */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmv */,_gg/* sFmw */.b)), _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */));
            }),
            _gu/* sFmZ */ = function(_gv/* sFmQ */){
              var _gw/* sFmR */ = new T(function(){
                return B(A1(_gs/* sFmN */,_gv/* sFmQ */));
              }),
              _gx/* sFmY */ = function(_gy/* sFmS */){
                return new F(function(){return A1(_gw/* sFmR */,function(_gz/* sFmT */){
                  return new F(function(){return A2(_gt/* sFmO */,E(_gz/* sFmT */).b, _gy/* sFmS */);});
                });});
              };
              return E(_gx/* sFmY */);
            };
            return E(_gu/* sFmZ */);
          case 3:
            var _gA/* sFn3 */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(_gg/* sFmw */.b, _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */));
            }),
            _gB/* sFn4 */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmv */,_gg/* sFmw */.c)), _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */));
            }),
            _gC/* sFnf */ = function(_gD/* sFn6 */){
              var _gE/* sFn7 */ = new T(function(){
                return B(A1(_gA/* sFn3 */,_gD/* sFn6 */));
              }),
              _gF/* sFne */ = function(_gG/* sFn8 */){
                return new F(function(){return A1(_gE/* sFn7 */,function(_gH/* sFn9 */){
                  return new F(function(){return A2(_gB/* sFn4 */,E(_gH/* sFn9 */).b, _gG/* sFn8 */);});
                });});
              };
              return E(_gF/* sFne */);
            };
            return E(_gC/* sFnf */);
          case 4:
            var _gI/* sFno */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmv */,_gg/* sFmw */.h)), _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */));
            }),
            _gJ/* sFph */ = function(_gK/* sFnq */, _gL/* sFnr */){
              var _gM/* sFns */ = function(_gN/* sFnt */){
                return new F(function(){return A2(_gI/* sFno */,E(_gN/* sFnt */).b, _gL/* sFnr */);});
              },
              _gO/* sFpg */ = function(_gP/* sFnx */){
                var _gQ/* sFny */ = E(_gP/* sFnx */),
                _gR/* sFnz */ = _gQ/* sFny */.a,
                _gS/* sFpf */ = function(_gT/* sFnB */){
                  var _gU/* sFnC */ = E(_gT/* sFnB */),
                  _gV/* sFnD */ = _gU/* sFnC */.a,
                  _gW/* sFpe */ = function(_gX/* sFnF */){
                    var _gY/* sFnG */ = E(_gX/* sFnF */),
                    _gZ/* sFnH */ = _gY/* sFnG */.a,
                    _h0/* sFpd */ = function(_h1/* sFnJ */){
                      var _h2/* sFnK */ = E(_h1/* sFnJ */),
                      _h3/* sFnL */ = _h2/* sFnK */.a,
                      _h4/* sFnN */ = new T(function(){
                        return E(_gR/* sFnz */)*E(_g7/* sFm3 */)+E(_h3/* sFnL */)*E(_g8/* sFm4 */);
                      }),
                      _h5/* sFnZ */ = new T(function(){
                        return E(_gR/* sFnz */)*E(_g4/* sFm0 */)+E(_h3/* sFnL */)*E(_g5/* sFm1 */);
                      }),
                      _h6/* sFpc */ = function(_h7/* sFob */){
                        var _h8/* sFoc */ = E(_h7/* sFob */),
                        _h9/* sFod */ = _h8/* sFoc */.a,
                        _ha/* sFof */ = new T(function(){
                          return E(_gV/* sFnD */)*E(_g7/* sFm3 */)+E(_h9/* sFod */)*E(_g8/* sFm4 */);
                        }),
                        _hb/* sFor */ = new T(function(){
                          return E(_gV/* sFnD */)*E(_g4/* sFm0 */)+E(_h9/* sFod */)*E(_g5/* sFm1 */);
                        }),
                        _hc/* sFpb */ = function(_hd/* sFoD */){
                          var _he/* sFoE */ = E(_hd/* sFoD */),
                          _hf/* sFoF */ = _he/* sFoE */.a;
                          return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sFmw */.g, _h5/* sFnZ */, _hb/* sFor */, new T(function(){
                            return E(_gZ/* sFnH */)*E(_g4/* sFm0 */)+E(_hf/* sFoF */)*E(_g5/* sFm1 */)+E(_g6/* sFm2 */);
                          }), _h4/* sFnN */, _ha/* sFof */, new T(function(){
                            return E(_gZ/* sFnH */)*E(_g7/* sFm3 */)+E(_hf/* sFoF */)*E(_g8/* sFm4 */)+E(_g9/* sFm5 */);
                          }), _he/* sFoE */.b, _gM/* sFns */]);});
                        };
                        return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmw */.f, _h8/* sFoc */.b, _hc/* sFpb */);});
                      };
                      return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmw */.e, _h2/* sFnK */.b, _h6/* sFpc */);});
                    };
                    return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmw */.d, _gY/* sFnG */.b, _h0/* sFpd */);});
                  };
                  return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmw */.c, _gU/* sFnC */.b, _gW/* sFpe */);});
                };
                return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmw */.b, _gQ/* sFny */.b, _gS/* sFpf */);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmw */.a, _gK/* sFnq */, _gO/* sFpg */);});
            };
            return E(_gJ/* sFph */);
          case 5:
            var _hg/* sFpl */ = E(_gg/* sFmw */.a),
            _hh/* sFpo */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmv */,_gg/* sFmw */.c)), _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */));
            }),
            _hi/* sFpq */ = new T(function(){
              return 0*E(_g7/* sFm3 */)+E(_g8/* sFm4 */);
            }),
            _hj/* sFpx */ = new T(function(){
              return E(_g7/* sFm3 */)+0*E(_g8/* sFm4 */);
            }),
            _hk/* sFpE */ = new T(function(){
              return 0*E(_g4/* sFm0 */)+E(_g5/* sFm1 */);
            }),
            _hl/* sFpL */ = new T(function(){
              return E(_g4/* sFm0 */)+0*E(_g5/* sFm1 */);
            }),
            _hm/* sFqD */ = function(_hn/* sFpS */, _ho/* sFpT */){
              var _hp/* sFpU */ = function(_hq/* sFpV */){
                return new F(function(){return A2(_hh/* sFpo */,E(_hq/* sFpV */).b, _ho/* sFpT */);});
              },
              _hr/* sFqC */ = function(_hs/* sFpZ */){
                var _ht/* sFq0 */ = E(_hs/* sFpZ */),
                _hu/* sFq1 */ = _ht/* sFq0 */.a,
                _hv/* sFqB */ = function(_hw/* sFq3 */){
                  var _hx/* sFq4 */ = E(_hw/* sFq3 */),
                  _hy/* sFq5 */ = _hx/* sFq4 */.a;
                  return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sFmw */.b, _hl/* sFpL */, _hk/* sFpE */, new T(function(){
                    return E(_hu/* sFq1 */)*E(_g4/* sFm0 */)+E(_hy/* sFq5 */)*E(_g5/* sFm1 */)+E(_g6/* sFm2 */);
                  }), _hj/* sFpx */, _hi/* sFpq */, new T(function(){
                    return E(_hu/* sFq1 */)*E(_g7/* sFm3 */)+E(_hy/* sFq5 */)*E(_g8/* sFm4 */)+E(_g9/* sFm5 */);
                  }), _hx/* sFq4 */.b, _hp/* sFpU */]);});
                };
                return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hg/* sFpl */.b, _ht/* sFq0 */.b, _hv/* sFqB */);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hg/* sFpl */.a, _hn/* sFpS */, _hr/* sFqC */);});
            };
            return E(_hm/* sFqD */);
          case 6:
            var _hz/* sFqH */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmv */,_gg/* sFmw */.c)), _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */));
            }),
            _hA/* sFrT */ = function(_hB/* sFqJ */, _hC/* sFqK */){
              var _hD/* sFqL */ = function(_hE/* sFqM */){
                return new F(function(){return A2(_hz/* sFqH */,E(_hE/* sFqM */).b, _hC/* sFqK */);});
              },
              _hF/* sFrS */ = function(_hG/* sFqQ */){
                var _hH/* sFqR */ = E(_hG/* sFqQ */),
                _hI/* sFqS */ = _hH/* sFqR */.a,
                _hJ/* sFqU */ = new T(function(){
                  return Math.cos/* EXTERNAL */(E(_hI/* sFqS */));
                }),
                _hK/* sFqY */ = new T(function(){
                  return Math.sin/* EXTERNAL */(E(_hI/* sFqS */));
                }),
                _hL/* sFr2 */ = new T(function(){
                  return  -E(_hK/* sFqY */);
                });
                return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sFmw */.b, new T(function(){
                  return E(_hJ/* sFqU */)*E(_g4/* sFm0 */)+E(_hK/* sFqY */)*E(_g5/* sFm1 */);
                }), new T(function(){
                  return E(_hL/* sFr2 */)*E(_g4/* sFm0 */)+E(_hJ/* sFqU */)*E(_g5/* sFm1 */);
                }), _ga/* sFm6 */, new T(function(){
                  return E(_hJ/* sFqU */)*E(_g7/* sFm3 */)+E(_hK/* sFqY */)*E(_g8/* sFm4 */);
                }), new T(function(){
                  return E(_hL/* sFr2 */)*E(_g7/* sFm3 */)+E(_hJ/* sFqU */)*E(_g8/* sFm4 */);
                }), _gb/* sFmh */, _hH/* sFqR */.b, _hD/* sFqL */]);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmw */.a, _hB/* sFqJ */, _hF/* sFrS */);});
            };
            return E(_hA/* sFrT */);
          case 7:
            var _hM/* sFrX */ = E(_gg/* sFmw */.a),
            _hN/* sFs0 */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmv */,_gg/* sFmw */.c)), _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */));
            }),
            _hO/* sFsX */ = function(_hP/* sFs2 */, _hQ/* sFs3 */){
              var _hR/* sFs4 */ = function(_hS/* sFs5 */){
                return new F(function(){return A2(_hN/* sFs0 */,E(_hS/* sFs5 */).b, _hQ/* sFs3 */);});
              },
              _hT/* sFsW */ = function(_hU/* sFs9 */){
                var _hV/* sFsa */ = E(_hU/* sFs9 */),
                _hW/* sFsb */ = _hV/* sFsa */.a,
                _hX/* sFsd */ = new T(function(){
                  return E(_hW/* sFsb */)*E(_g7/* sFm3 */)+0*E(_g8/* sFm4 */);
                }),
                _hY/* sFsn */ = new T(function(){
                  return E(_hW/* sFsb */)*E(_g4/* sFm0 */)+0*E(_g5/* sFm1 */);
                }),
                _hZ/* sFsV */ = function(_i0/* sFsx */){
                  var _i1/* sFsy */ = E(_i0/* sFsx */),
                  _i2/* sFsz */ = _i1/* sFsy */.a;
                  return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sFmw */.b, _hY/* sFsn */, new T(function(){
                    return 0*E(_g4/* sFm0 */)+E(_i2/* sFsz */)*E(_g5/* sFm1 */);
                  }), _ga/* sFm6 */, _hX/* sFsd */, new T(function(){
                    return 0*E(_g7/* sFm3 */)+E(_i2/* sFsz */)*E(_g8/* sFm4 */);
                  }), _gb/* sFmh */, _i1/* sFsy */.b, _hR/* sFs4 */]);});
                };
                return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hM/* sFrX */.b, _hV/* sFsa */.b, _hZ/* sFsV */);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hM/* sFrX */.a, _hP/* sFs2 */, _hT/* sFsW */);});
            };
            return E(_hO/* sFsX */);
          default:
            var _i3/* sFt1 */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(_gg/* sFmw */.b, _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */));
            }),
            _i4/* sFt2 */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmv */,_gg/* sFmw */.c)), _g4/* sFm0 */, _g5/* sFm1 */, _g6/* sFm2 */, _g7/* sFm3 */, _g8/* sFm4 */, _g9/* sFm5 */));
            }),
            _i5/* sFtd */ = function(_i6/* sFt4 */){
              var _i7/* sFt5 */ = new T(function(){
                return B(A1(_i3/* sFt1 */,_i6/* sFt4 */));
              }),
              _i8/* sFtc */ = function(_i9/* sFt6 */){
                return new F(function(){return A1(_i7/* sFt5 */,function(_ia/* sFt7 */){
                  return new F(function(){return A2(_i4/* sFt2 */,E(_ia/* sFt7 */).b, _i9/* sFt6 */);});
                });});
              };
              return E(_i8/* sFtc */);
            };
            return E(_i5/* sFtd */);
        }
      }
    })(_fV/*  sFlZ */, _fW/*  sFm0 */, _fX/*  sFm1 */, _fY/*  sFm2 */, _fZ/*  sFm3 */, _g0/*  sFm4 */, _g1/*  sFm5 */));
    if(_g2/*  applyTransform_world */!=__continue/* EXTERNAL */){
      return _g2/*  applyTransform_world */;
    }
  }
},
_ib/* buffer_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(e){e.width = e.width;})");
}),
_ic/* jsSet_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(e,p,v){e[p] = v;})");
}),
_id/* $fMorphDouble_$clerp */ = function(_ie/* sbeF */, _if/* sbeG */, _ig/* sbeH */){
  var _ih/* sbeK */ = E(_ie/* sbeF */);
  return E(_if/* sbeG */)*(1-_ih/* sbeK */)+E(_ig/* sbeH */)*_ih/* sbeK */;
},
_ii/* waitUntil2 */ = new T1(1,_6/* GHC.Types.[] */),
_ij/* $wa6 */ = function(_ik/* sbVv */, _il/* sbVw */, _im/* sbVx */){
  return function(_/* EXTERNAL */){
    var _in/* sbVz */ = nMV/* EXTERNAL */(_ii/* Core.World.Internal.waitUntil2 */),
    _io/* sbVB */ = _in/* sbVz */;
    return new T(function(){
      var _ip/* sbVZ */ = function(_iq/* sbVL */){
        var _ir/* sbVP */ = new T(function(){
          return B(A1(_im/* sbVx */,new T2(0,_7/* GHC.Tuple.() */,E(_iq/* sbVL */).b)));
        }),
        _is/* sbVR */ = function(_it/* sbVS */){
          return E(_ir/* sbVP */);
        };
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_io/* sbVB */, function(_iu/* sbVT */){
          return new T1(0,B(_9p/* Haste.Concurrent.$wa */(_cp/* Core.World.Internal.switch2 */, _is/* sbVR */)));
        })));
      },
      _iv/* sbVK */ = function(_iw/* sbVD */, _ix/* sbVE */){
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_io/* sbVB */, _7/* GHC.Tuple.() */, function(_iy/* sbVF */){
          return new F(function(){return A1(_ix/* sbVE */,new T2(0,_iy/* sbVF */,_iw/* sbVD */));});
        })));
      };
      return B(A3(_ik/* sbVv */,_iv/* sbVK */, _il/* sbVw */, _ip/* sbVZ */));
    });
  };
},
_iz/* a7 */ = function(_iA/* sbfA */, _iB/* sbfB */, _iC/* sbfC */){
  var _iD/* sbfD */ = new T(function(){
    return E(E(_iA/* sbfA */).b);
  });
  return new F(function(){return A1(_iC/* sbfC */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,new T(function(){
    return E(E(_iA/* sbfA */).a);
  }),new T4(0,new T(function(){
    return E(E(_iD/* sbfD */).a);
  }),new T(function(){
    return E(E(_iD/* sbfD */).b);
  }),new T(function(){
    return E(E(_iD/* sbfD */).c);
  }),_av/* GHC.Types.False */))),_iB/* sbfB */));});
},
_iE/* divideDouble */ = function(_iF/* s18yD */, _iG/* s18yE */){
  return E(_iF/* s18yD */)/E(_iG/* s18yE */);
},
_iH/* ease2 */ = 0,
_iI/* easeRegister1 */ = function(_iJ/* sc35 */, _iK/* sc36 */, _iL/* sc37 */, _iM/* sc38 */){
  var _iN/* sc3m */ = function(_iO/* sc3a */, _iP/* sc3b */, _iQ/* sc3c */){
    return new F(function(){return A1(_iQ/* sc3c */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
      var _iR/* sc3d */ = E(_iO/* sc3a */);
      return new T4(0,E(new T2(1,new T2(0,_iJ/* sc35 */,_iK/* sc36 */),_iR/* sc3d */.a)),_iR/* sc3d */.b,E(_iR/* sc3d */.c),E(_iR/* sc3d */.d));
    })),_iP/* sc3b */));});
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _iL/* sc37 */, _iN/* sc3m */, _iL/* sc37 */, _iM/* sc38 */]);});
},
_iS/* $weaseHandle */ = function(_iT/* sbg7 */, _iU/* sbg8 */, _iV/* sbg9 */, _iW/* sbga */, _iX/* sbgb */, _iY/* sbgc */){
  var _iZ/* sbgd */ = new T(function(){
    var _j0/* sbge */ = new T(function(){
      return B(A1(_iV/* sbg9 */,_2E/* GHC.Base.id */));
    }),
    _j1/* sbgx */ = function(_j2/* sbgf */, _j3/* sbgg */, _j4/* sbgh */){
      var _j5/* sbgi */ = E(_j2/* sbgf */),
      _j6/* sbgl */ = E(_j5/* sbgi */.b),
      _j7/* sbgs */ = new T(function(){
        var _j8/* sbgr */ = new T(function(){
          return B(A1(_j0/* sbge */,new T(function(){
            return B(_iE/* GHC.Float.divideDouble */(_j6/* sbgl */.c, _iU/* sbg8 */));
          })));
        });
        return B(A3(_iT/* sbg7 */,_j8/* sbgr */, _j6/* sbgl */.a, _j6/* sbgl */.b));
      });
      return new F(function(){return A1(_j4/* sbgh */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_j5/* sbgi */.a,new T4(0,_j7/* sbgs */,_iX/* sbgb */,_iH/* Core.Ease.ease2 */,_j6/* sbgl */.d))),_j3/* sbgg */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iW/* sbga */, _j1/* sbgx */));
  }),
  _j9/* sbgy */ = new T(function(){
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iW/* sbga */, _iz/* Core.Ease.a7 */));
  }),
  _ja/* sbgz */ = new T(function(){
    var _jb/* sbgA */ = new T(function(){
      return B(A1(_iY/* sbgc */,_av/* GHC.Types.False */));
    }),
    _jc/* sbgB */ = new T(function(){
      return B(A1(_iY/* sbgc */,_aw/* GHC.Types.True */));
    }),
    _jd/* sbgC */ = new T(function(){
      return B(A1(_iV/* sbg9 */,_2E/* GHC.Base.id */));
    }),
    _je/* sbhp */ = function(_jf/* sbgD */, _jg/* sbgE */, _jh/* sbgF */){
      var _ji/* sbgG */ = E(_jf/* sbgD */),
      _jj/* sbgJ */ = E(_ji/* sbgG */.b),
      _jk/* sbgK */ = _jj/* sbgJ */.a,
      _jl/* sbgL */ = _jj/* sbgJ */.b;
      if(!E(_jj/* sbgJ */.d)){
        var _jm/* sbgP */ = E(_iU/* sbg8 */),
        _jn/* sbgT */ = E(_jj/* sbgJ */.c)+1,
        _jo/* sbgU */ = function(_jp/* sbgV */, _jq/* sbgW */){
          var _jr/* sbgX */ = new T(function(){
            var _js/* sbh0 */ = new T(function(){
              return B(A1(_jd/* sbgC */,new T(function(){
                return _jp/* sbgV *//_jm/* sbgP */;
              })));
            });
            return B(A3(_iT/* sbg7 */,_js/* sbh0 */, _jk/* sbgK */, _jl/* sbgL */));
          }),
          _jt/* sbh1 */ = new T4(0,_jk/* sbgK */,_jl/* sbgL */,_jq/* sbgW */,_aw/* GHC.Types.True */);
          if(_jp/* sbgV */>=_jm/* sbgP */){
            return new F(function(){return A2(_jc/* sbgB */,_jg/* sbgE */, function(_ju/* sbh6 */){
              return new F(function(){return A1(_jh/* sbgF */,new T2(0,new T2(0,_av/* GHC.Types.False */,new T2(0,_jr/* sbgX */,_jt/* sbh1 */)),E(_ju/* sbh6 */).b));});
            });});
          }else{
            return new F(function(){return A1(_jh/* sbgF */,new T2(0,new T2(0,_aw/* GHC.Types.True */,new T2(0,_jr/* sbgX */,_jt/* sbh1 */)),_jg/* sbgE */));});
          }
        };
        if(_jm/* sbgP */>_jn/* sbgT */){
          return new F(function(){return _jo/* sbgU */(_jn/* sbgT */, _jn/* sbgT */);});
        }else{
          return new F(function(){return _jo/* sbgU */(_jm/* sbgP */, _jm/* sbgP */);});
        }
      }else{
        return new F(function(){return A2(_jb/* sbgA */,_jg/* sbgE */, function(_jv/* sbhj */){
          return new F(function(){return A1(_jh/* sbgF */,new T2(0,new T2(0,_av/* GHC.Types.False */,_ji/* sbgG */),E(_jv/* sbhj */).b));});
        });});
      }
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iW/* sbga */, _je/* sbhp */));
  }),
  _jw/* sbhV */ = function(_jx/* sbhq */, _jy/* sbhr */){
    var _jz/* sbhs */ = new T(function(){
      return B(A2(_iZ/* sbgd */,_jx/* sbhq */, function(_jA/* sbht */){
        return new F(function(){return _iI/* Core.World.Internal.easeRegister1 */(_j9/* sbgy */, _ja/* sbgz */, E(_jA/* sbht */).b, _jy/* sbhr */);});
      }));
    }),
    _jB/* sbhS */ = function(_jC/* sbhy */){
      var _jD/* sbhz */ = new T(function(){
        var _jE/* sbhA */ = E(_jC/* sbhy */),
        _jF/* sbhD */ = E(_jE/* sbhA */.a),
        _jG/* sbhE */ = E(_jE/* sbhA */.b),
        _jH/* sbhJ */ = E(_jG/* sbhE */.a),
        _jI/* sbhK */ = E(_jG/* sbhE */.b),
        _jJ/* sbhM */ = E(_jG/* sbhE */.c),
        _jK/* sbhN */ = E(_jG/* sbhE */.d);
        return E(_jz/* sbhs */);
      });
      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_iW/* sbga */, _jC/* sbhy */, function(_jL/* sbhO */){
        return E(_jD/* sbhz */);
      })));
    };
    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_iW/* sbga */, _jB/* sbhS */)));
  };
  return E(_jw/* sbhV */);
},
_jM/* forceTo_b1 */ = 1,
_jN/* $wforceTo */ = function(_jO/* sb1r */, _jP/* sb1s */){
  var _jQ/* sb1t */ = new T(function(){
    var _jR/* sb1K */ = function(_jS/* sb1u */, _jT/* sb1v */, _jU/* sb1w */){
      return new F(function(){return A1(_jU/* sb1w */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_jP/* sb1s */,new T4(0,_jP/* sb1s */,_jP/* sb1s */,_jM/* Core.Ease.forceTo_b1 */,new T(function(){
        return E(E(E(_jS/* sb1u */).b).d);
      })))),_jT/* sb1v */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _jO/* sb1r */, _jR/* sb1K */));
  }),
  _jV/* sb2b */ = function(_jW/* sb1L */, _jX/* sb1M */){
    var _jY/* sb1N */ = new T(function(){
      return B(A2(_jQ/* sb1t */,_jW/* sb1L */, _jX/* sb1M */));
    }),
    _jZ/* sb28 */ = function(_k0/* sb1O */){
      var _k1/* sb1P */ = new T(function(){
        var _k2/* sb1Q */ = E(_k0/* sb1O */),
        _k3/* sb1T */ = E(_k2/* sb1Q */.a),
        _k4/* sb1U */ = E(_k2/* sb1Q */.b),
        _k5/* sb1Z */ = E(_k4/* sb1U */.a),
        _k6/* sb20 */ = E(_k4/* sb1U */.b),
        _k7/* sb22 */ = E(_k4/* sb1U */.c),
        _k8/* sb23 */ = E(_k4/* sb1U */.d);
        return E(_jY/* sb1N */);
      });
      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_jO/* sb1r */, _k0/* sb1O */, function(_k9/* sb24 */){
        return E(_k1/* sb1P */);
      })));
    };
    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_jO/* sb1r */, _jZ/* sb28 */)));
  };
  return E(_jV/* sb2b */);
},
_ka/* $fAffineShape2 */ = function(_kb/* stev */, _kc/* stew */, _kd/* stex */, _ke/* stey */, _/* EXTERNAL */){
  var _kf/* steA */ = E(_kb/* stev */);
  switch(_kf/* steA */._){
    case 0:
      return new F(function(){return A(_kc/* stew */,[_kf/* steA */.a, _kd/* stex */, _ke/* stey */, _/* EXTERNAL */]);});
      break;
    case 1:
      var _kg/* steD */ = B(A1(_kf/* steA */.a,_/* EXTERNAL */));
      return new F(function(){return A(_kc/* stew */,[_kg/* steD */, _kd/* stex */, _ke/* stey */, _/* EXTERNAL */]);});
      break;
    case 2:
      var _kh/* steO */ = rMV/* EXTERNAL */(E(E(_kf/* steA */.a).c)),
      _ki/* steR */ = E(_kh/* steO */);
      if(!_ki/* steR */._){
        var _kj/* steV */ = new T(function(){
          return B(A1(_kf/* steA */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_ki/* steR */.a));
          })));
        });
        return new F(function(){return A(_kc/* stew */,[_kj/* steV */, _kd/* stex */, _ke/* stey */, _/* EXTERNAL */]);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _kk/* stf5 */ = rMV/* EXTERNAL */(E(E(_kf/* steA */.a).c)),
      _kl/* stf8 */ = E(_kk/* stf5 */);
      if(!_kl/* stf8 */._){
        var _km/* stfe */ = B(A2(_kf/* steA */.b,E(_kl/* stf8 */.a).a, _/* EXTERNAL */));
        return new F(function(){return A(_kc/* stew */,[_km/* stfe */, _kd/* stex */, _ke/* stey */, _/* EXTERNAL */]);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
  }
},
_kn/* $fAffineShape3 */ = function(_ko/* stfi */, _kp/* stfj */, _/* EXTERNAL */){
  var _kq/* stfl */ = E(_ko/* stfi */);
  switch(_kq/* stfl */._){
    case 0:
      return new F(function(){return A2(_kp/* stfj */,_kq/* stfl */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _kr/* stfo */ = B(A1(_kq/* stfl */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_kp/* stfj */,_kr/* stfo */, _/* EXTERNAL */);});
      break;
    case 2:
      var _ks/* stfz */ = rMV/* EXTERNAL */(E(E(_kq/* stfl */.a).c)),
      _kt/* stfC */ = E(_ks/* stfz */);
      if(!_kt/* stfC */._){
        var _ku/* stfG */ = new T(function(){
          return B(A1(_kq/* stfl */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_kt/* stfC */.a));
          })));
        });
        return new F(function(){return A2(_kp/* stfj */,_ku/* stfG */, _/* EXTERNAL */);});
      }else{
        return _av/* GHC.Types.False */;
      }
      break;
    default:
      var _kv/* stfQ */ = rMV/* EXTERNAL */(E(E(_kq/* stfl */.a).c)),
      _kw/* stfT */ = E(_kv/* stfQ */);
      if(!_kw/* stfT */._){
        var _kx/* stfZ */ = B(A2(_kq/* stfl */.b,E(_kw/* stfT */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_kp/* stfj */,_kx/* stfZ */, _/* EXTERNAL */);});
      }else{
        return _av/* GHC.Types.False */;
      }
  }
},
_ky/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _7/* GHC.Tuple.() */;
},
_kz/* bezier_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.moveTo(x,y);})");
}),
_kA/* line_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.lineTo(x,y);})");
}),
_kB/* $wrect */ = function(_kC/* stAA */, _kD/* stAB */, _kE/* stAC */, _kF/* stAD */){
  var _kG/* stCF */ = function(_kH/* stBC */, _kI/* stBD */, _kJ/* stBE */, _/* EXTERNAL */){
    var _kK/* stCE */ = function(_kL/* stBG */, _kM/* stBH */, _kN/* stBI */, _/* EXTERNAL */){
      var _kO/* stCD */ = function(_kP/* stBK */, _kQ/* stBL */, _kR/* stBM */, _/* EXTERNAL */){
        return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_kF/* stAD */, function(_kS/* stBO */, _kT/* stBP */, _kU/* stBQ */, _/* EXTERNAL */){
          var _kV/* stBS */ = E(_kH/* stBC */),
          _kW/* stBW */ = E(_kL/* stBG */),
          _kX/* stC0 */ = E(_kT/* stBP */),
          _kY/* stC4 */ = E(_kU/* stBQ */),
          _kZ/* stC7 */ = __app4/* EXTERNAL */(E(_kz/* Core.Shape.Internal.bezier_f2 */), _kV/* stBS */, _kW/* stBW */, _kX/* stC0 */, _kY/* stC4 */),
          _l0/* stCc */ = _kV/* stBS */+E(_kP/* stBK */),
          _l1/* stCf */ = E(_kA/* Core.Shape.Internal.line_f1 */),
          _l2/* stCi */ = __app4/* EXTERNAL */(_l1/* stCf */, _l0/* stCc */, _kW/* stBW */, _kX/* stC0 */, _kY/* stC4 */),
          _l3/* stCn */ = _kW/* stBW */+E(_kS/* stBO */),
          _l4/* stCr */ = __app4/* EXTERNAL */(_l1/* stCf */, _l0/* stCc */, _l3/* stCn */, _kX/* stC0 */, _kY/* stC4 */),
          _l5/* stCv */ = __app4/* EXTERNAL */(_l1/* stCf */, _kV/* stBS */, _l3/* stCn */, _kX/* stC0 */, _kY/* stC4 */),
          _l6/* stCz */ = __app4/* EXTERNAL */(_l1/* stCf */, _kV/* stBS */, _kW/* stBW */, _kX/* stC0 */, _kY/* stC4 */);
          return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _kQ/* stBL */, _kR/* stBM */, _/* EXTERNAL */);});
      };
      return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_kE/* stAC */, _kO/* stCD */, _kM/* stBH */, _kN/* stBI */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_kD/* stAB */, _kK/* stCE */, _kI/* stBD */, _kJ/* stBE */, _/* EXTERNAL */);});
  },
  _l7/* stBB */ = function(_l8/* stAE */, _/* EXTERNAL */){
    var _l9/* stAG */ = E(_l8/* stAE */),
    _la/* stBA */ = function(_lb/* stAJ */, _/* EXTERNAL */){
      var _lc/* stBz */ = function(_ld/* stAL */, _/* EXTERNAL */){
        var _le/* stBy */ = function(_lf/* stAN */, _/* EXTERNAL */){
          var _lg/* stBx */ = function(_lh/* stAP */, _/* EXTERNAL */){
            return new T(function(){
              var _li/* stAV */ = E(_lf/* stAN */),
              _lj/* stAX */ = function(_lk/* stAY */){
                var _ll/* stB3 */ = E(_lh/* stAP */),
                _lm/* stB7 */ = E(_l9/* stAG */.b)-E(_ld/* stAL */)-_ll/* stB3 *//2;
                return (_lm/* stB7 */==0) ? 0<_ll/* stB3 *//2 : (_lm/* stB7 */<=0) ?  -_lm/* stB7 */<_ll/* stB3 *//2 : _lm/* stB7 */<_ll/* stB3 *//2;
              },
              _ln/* stBj */ = E(_l9/* stAG */.a)-E(_lb/* stAJ */)-_li/* stAV *//2;
              if(!_ln/* stBj */){
                if(0>=_li/* stAV *//2){
                  return false;
                }else{
                  return B(_lj/* stAX */(_/* EXTERNAL */));
                }
              }else{
                if(_ln/* stBj */<=0){
                  if( -_ln/* stBj */>=_li/* stAV *//2){
                    return false;
                  }else{
                    return B(_lj/* stAX */(_/* EXTERNAL */));
                  }
                }else{
                  if(_ln/* stBj */>=_li/* stAV *//2){
                    return false;
                  }else{
                    return B(_lj/* stAX */(_/* EXTERNAL */));
                  }
                }
              }
            });
          };
          return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_kF/* stAD */, _lg/* stBx */, _/* EXTERNAL */);});
        };
        return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_kE/* stAC */, _le/* stBy */, _/* EXTERNAL */);});
      };
      return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_kD/* stAB */, _lc/* stBz */, _/* EXTERNAL */);});
    };
    return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_kC/* stAA */, _la/* stBA */, _/* EXTERNAL */);});
  };
  return new T3(0,_l7/* stBB */,function(_lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_kC/* stAA */, _kG/* stCF */, _lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_lq/* a */ = 100,
_lr/* a4 */ = function(_ls/* sNux */, _lt/* sNuy */){
  var _lu/* sNuE */ = B(A1(_ls/* sNux */,new T(function(){
    return 1-(1-E(_lt/* sNuy */));
  })));
  return 1-(1-_lu/* sNuE */*_lu/* sNuE */);
},
_lv/* dur */ = 20,
_lw/* e */ = function(_lx/* sNun */, _ly/* sNuo */){
  var _lz/* sNut */ = B(A1(_lx/* sNun */,new T(function(){
    return 1-E(_ly/* sNuo */);
  })));
  return 1-_lz/* sNut */*_lz/* sNut */;
},
_lA/* easeIn */ = function(_lB/* sb1a */, _lC/* sb1b */){
  return new F(function(){return A1(_lB/* sb1a */,_lC/* sb1b */);});
},
_lD/* $wa */ = function(_lE/* sFyA */, _lF/* sFyB */, _lG/* sFyC */, _lH/* sFyD */, _/* EXTERNAL */){
  var _lI/* sFyF */ = function(_/* EXTERNAL */, _lJ/* sFyH */){
    var _lK/* sFyI */ = function(_/* EXTERNAL */, _lL/* sFyK */){
      var _lM/* sFyL */ = function(_/* EXTERNAL */, _lN/* sFyN */){
        var _lO/* sFyO */ = E(_lH/* sFyD */);
        switch(_lO/* sFyO */._){
          case 0:
            return new T(function(){
              var _lP/* sFyQ */ = function(_lQ/* sFyR */){
                var _lR/* sFyS */ = _lQ/* sFyR */*256,
                _lS/* sFyT */ = _lR/* sFyS */&4294967295,
                _lT/* sFyU */ = function(_lU/* sFyV */){
                  var _lV/* sFyY */ = E(_lL/* sFyK */)*256,
                  _lW/* sFyZ */ = _lV/* sFyY */&4294967295,
                  _lX/* sFz0 */ = function(_lY/* sFz1 */){
                    var _lZ/* sFz2 */ = function(_m0/* sFz3 */){
                      var _m1/* sFz4 */ = _m0/* sFz3 */*256,
                      _m2/* sFz5 */ = _m1/* sFz4 */&4294967295,
                      _m3/* sFz6 */ = function(_m4/* sFz7 */){
                        var _m5/* sFz8 */ = E(_lO/* sFyO */.a);
                        return (1>_m5/* sFz8 */) ? (0>_m5/* sFz8 */) ? new T4(1,_lU/* sFyV */,_lY/* sFz1 */,_m4/* sFz7 */,0) : new T4(1,_lU/* sFyV */,_lY/* sFz1 */,_m4/* sFz7 */,_m5/* sFz8 */) : new T4(1,_lU/* sFyV */,_lY/* sFz1 */,_m4/* sFz7 */,1);
                      };
                      if(_m1/* sFz4 */>=_m2/* sFz5 */){
                        if(255>_m2/* sFz5 */){
                          if(0>_m2/* sFz5 */){
                            return new F(function(){return _m3/* sFz6 */(0);});
                          }else{
                            return new F(function(){return _m3/* sFz6 */(_m2/* sFz5 */);});
                          }
                        }else{
                          return new F(function(){return _m3/* sFz6 */(255);});
                        }
                      }else{
                        var _m6/* sFzl */ = _m2/* sFz5 */-1|0;
                        if(255>_m6/* sFzl */){
                          if(0>_m6/* sFzl */){
                            return new F(function(){return _m3/* sFz6 */(0);});
                          }else{
                            return new F(function(){return _m3/* sFz6 */(_m6/* sFzl */);});
                          }
                        }else{
                          return new F(function(){return _m3/* sFz6 */(255);});
                        }
                      }
                    },
                    _m7/* sFzq */ = E(_lN/* sFyN */);
                    if(!_m7/* sFzq */._){
                      return new F(function(){return _lZ/* sFz2 */(0);});
                    }else{
                      return new F(function(){return _lZ/* sFz2 */(E(_m7/* sFzq */.a));});
                    }
                  };
                  if(_lV/* sFyY */>=_lW/* sFyZ */){
                    if(255>_lW/* sFyZ */){
                      if(0>_lW/* sFyZ */){
                        return new F(function(){return _lX/* sFz0 */(0);});
                      }else{
                        return new F(function(){return _lX/* sFz0 */(_lW/* sFyZ */);});
                      }
                    }else{
                      return new F(function(){return _lX/* sFz0 */(255);});
                    }
                  }else{
                    var _m8/* sFzB */ = _lW/* sFyZ */-1|0;
                    if(255>_m8/* sFzB */){
                      if(0>_m8/* sFzB */){
                        return new F(function(){return _lX/* sFz0 */(0);});
                      }else{
                        return new F(function(){return _lX/* sFz0 */(_m8/* sFzB */);});
                      }
                    }else{
                      return new F(function(){return _lX/* sFz0 */(255);});
                    }
                  }
                };
                if(_lR/* sFyS */>=_lS/* sFyT */){
                  if(255>_lS/* sFyT */){
                    if(0>_lS/* sFyT */){
                      return new F(function(){return _lT/* sFyU */(0);});
                    }else{
                      return new F(function(){return _lT/* sFyU */(_lS/* sFyT */);});
                    }
                  }else{
                    return new F(function(){return _lT/* sFyU */(255);});
                  }
                }else{
                  var _m9/* sFzN */ = _lS/* sFyT */-1|0;
                  if(255>_m9/* sFzN */){
                    if(0>_m9/* sFzN */){
                      return new F(function(){return _lT/* sFyU */(0);});
                    }else{
                      return new F(function(){return _lT/* sFyU */(_m9/* sFzN */);});
                    }
                  }else{
                    return new F(function(){return _lT/* sFyU */(255);});
                  }
                }
              },
              _ma/* sFzS */ = E(_lJ/* sFyH */);
              if(!_ma/* sFzS */._){
                return B(_lP/* sFyQ */(0));
              }else{
                return B(_lP/* sFyQ */(E(_ma/* sFzS */.a)));
              }
            });
          case 1:
            var _mb/* sFzY */ = B(A1(_lO/* sFyO */.a,_/* EXTERNAL */)),
            _mc/* sFA0 */ = _mb/* sFzY */;
            return new T(function(){
              var _md/* sFA1 */ = function(_me/* sFA2 */){
                var _mf/* sFA3 */ = _me/* sFA2 */*256,
                _mg/* sFA4 */ = _mf/* sFA3 */&4294967295,
                _mh/* sFA5 */ = function(_mi/* sFA6 */){
                  var _mj/* sFA9 */ = E(_lL/* sFyK */)*256,
                  _mk/* sFAa */ = _mj/* sFA9 */&4294967295,
                  _ml/* sFAb */ = function(_mm/* sFAc */){
                    var _mn/* sFAd */ = function(_mo/* sFAe */){
                      var _mp/* sFAf */ = _mo/* sFAe */*256,
                      _mq/* sFAg */ = _mp/* sFAf */&4294967295,
                      _mr/* sFAh */ = function(_ms/* sFAi */){
                        var _mt/* sFAj */ = E(_mc/* sFA0 */);
                        return (1>_mt/* sFAj */) ? (0>_mt/* sFAj */) ? new T4(1,_mi/* sFA6 */,_mm/* sFAc */,_ms/* sFAi */,0) : new T4(1,_mi/* sFA6 */,_mm/* sFAc */,_ms/* sFAi */,_mt/* sFAj */) : new T4(1,_mi/* sFA6 */,_mm/* sFAc */,_ms/* sFAi */,1);
                      };
                      if(_mp/* sFAf */>=_mq/* sFAg */){
                        if(255>_mq/* sFAg */){
                          if(0>_mq/* sFAg */){
                            return new F(function(){return _mr/* sFAh */(0);});
                          }else{
                            return new F(function(){return _mr/* sFAh */(_mq/* sFAg */);});
                          }
                        }else{
                          return new F(function(){return _mr/* sFAh */(255);});
                        }
                      }else{
                        var _mu/* sFAw */ = _mq/* sFAg */-1|0;
                        if(255>_mu/* sFAw */){
                          if(0>_mu/* sFAw */){
                            return new F(function(){return _mr/* sFAh */(0);});
                          }else{
                            return new F(function(){return _mr/* sFAh */(_mu/* sFAw */);});
                          }
                        }else{
                          return new F(function(){return _mr/* sFAh */(255);});
                        }
                      }
                    },
                    _mv/* sFAB */ = E(_lN/* sFyN */);
                    if(!_mv/* sFAB */._){
                      return new F(function(){return _mn/* sFAd */(0);});
                    }else{
                      return new F(function(){return _mn/* sFAd */(E(_mv/* sFAB */.a));});
                    }
                  };
                  if(_mj/* sFA9 */>=_mk/* sFAa */){
                    if(255>_mk/* sFAa */){
                      if(0>_mk/* sFAa */){
                        return new F(function(){return _ml/* sFAb */(0);});
                      }else{
                        return new F(function(){return _ml/* sFAb */(_mk/* sFAa */);});
                      }
                    }else{
                      return new F(function(){return _ml/* sFAb */(255);});
                    }
                  }else{
                    var _mw/* sFAM */ = _mk/* sFAa */-1|0;
                    if(255>_mw/* sFAM */){
                      if(0>_mw/* sFAM */){
                        return new F(function(){return _ml/* sFAb */(0);});
                      }else{
                        return new F(function(){return _ml/* sFAb */(_mw/* sFAM */);});
                      }
                    }else{
                      return new F(function(){return _ml/* sFAb */(255);});
                    }
                  }
                };
                if(_mf/* sFA3 */>=_mg/* sFA4 */){
                  if(255>_mg/* sFA4 */){
                    if(0>_mg/* sFA4 */){
                      return new F(function(){return _mh/* sFA5 */(0);});
                    }else{
                      return new F(function(){return _mh/* sFA5 */(_mg/* sFA4 */);});
                    }
                  }else{
                    return new F(function(){return _mh/* sFA5 */(255);});
                  }
                }else{
                  var _mx/* sFAY */ = _mg/* sFA4 */-1|0;
                  if(255>_mx/* sFAY */){
                    if(0>_mx/* sFAY */){
                      return new F(function(){return _mh/* sFA5 */(0);});
                    }else{
                      return new F(function(){return _mh/* sFA5 */(_mx/* sFAY */);});
                    }
                  }else{
                    return new F(function(){return _mh/* sFA5 */(255);});
                  }
                }
              },
              _my/* sFB3 */ = E(_lJ/* sFyH */);
              if(!_my/* sFB3 */._){
                return B(_md/* sFA1 */(0));
              }else{
                return B(_md/* sFA1 */(E(_my/* sFB3 */.a)));
              }
            });
          case 2:
            var _mz/* sFBg */ = rMV/* EXTERNAL */(E(E(_lO/* sFyO */.a).c)),
            _mA/* sFBj */ = E(_mz/* sFBg */);
            return (_mA/* sFBj */._==0) ? new T(function(){
              var _mB/* sFBm */ = function(_mC/* sFBn */){
                var _mD/* sFBo */ = _mC/* sFBn */*256,
                _mE/* sFBp */ = _mD/* sFBo */&4294967295,
                _mF/* sFBq */ = function(_mG/* sFBr */){
                  var _mH/* sFBu */ = E(_lL/* sFyK */)*256,
                  _mI/* sFBv */ = _mH/* sFBu */&4294967295,
                  _mJ/* sFBw */ = function(_mK/* sFBx */){
                    var _mL/* sFBy */ = function(_mM/* sFBz */){
                      var _mN/* sFBA */ = _mM/* sFBz */*256,
                      _mO/* sFBB */ = _mN/* sFBA */&4294967295,
                      _mP/* sFBC */ = function(_mQ/* sFBD */){
                        var _mR/* sFBF */ = B(A1(_lO/* sFyO */.b,new T(function(){
                          return B(_fB/* Data.Tuple.fst */(_mA/* sFBj */.a));
                        })));
                        return (1>_mR/* sFBF */) ? (0>_mR/* sFBF */) ? new T4(1,_mG/* sFBr */,_mK/* sFBx */,_mQ/* sFBD */,0) : new T4(1,_mG/* sFBr */,_mK/* sFBx */,_mQ/* sFBD */,_mR/* sFBF */) : new T4(1,_mG/* sFBr */,_mK/* sFBx */,_mQ/* sFBD */,1);
                      };
                      if(_mN/* sFBA */>=_mO/* sFBB */){
                        if(255>_mO/* sFBB */){
                          if(0>_mO/* sFBB */){
                            return new F(function(){return _mP/* sFBC */(0);});
                          }else{
                            return new F(function(){return _mP/* sFBC */(_mO/* sFBB */);});
                          }
                        }else{
                          return new F(function(){return _mP/* sFBC */(255);});
                        }
                      }else{
                        var _mS/* sFBS */ = _mO/* sFBB */-1|0;
                        if(255>_mS/* sFBS */){
                          if(0>_mS/* sFBS */){
                            return new F(function(){return _mP/* sFBC */(0);});
                          }else{
                            return new F(function(){return _mP/* sFBC */(_mS/* sFBS */);});
                          }
                        }else{
                          return new F(function(){return _mP/* sFBC */(255);});
                        }
                      }
                    },
                    _mT/* sFBX */ = E(_lN/* sFyN */);
                    if(!_mT/* sFBX */._){
                      return new F(function(){return _mL/* sFBy */(0);});
                    }else{
                      return new F(function(){return _mL/* sFBy */(E(_mT/* sFBX */.a));});
                    }
                  };
                  if(_mH/* sFBu */>=_mI/* sFBv */){
                    if(255>_mI/* sFBv */){
                      if(0>_mI/* sFBv */){
                        return new F(function(){return _mJ/* sFBw */(0);});
                      }else{
                        return new F(function(){return _mJ/* sFBw */(_mI/* sFBv */);});
                      }
                    }else{
                      return new F(function(){return _mJ/* sFBw */(255);});
                    }
                  }else{
                    var _mU/* sFC8 */ = _mI/* sFBv */-1|0;
                    if(255>_mU/* sFC8 */){
                      if(0>_mU/* sFC8 */){
                        return new F(function(){return _mJ/* sFBw */(0);});
                      }else{
                        return new F(function(){return _mJ/* sFBw */(_mU/* sFC8 */);});
                      }
                    }else{
                      return new F(function(){return _mJ/* sFBw */(255);});
                    }
                  }
                };
                if(_mD/* sFBo */>=_mE/* sFBp */){
                  if(255>_mE/* sFBp */){
                    if(0>_mE/* sFBp */){
                      return new F(function(){return _mF/* sFBq */(0);});
                    }else{
                      return new F(function(){return _mF/* sFBq */(_mE/* sFBp */);});
                    }
                  }else{
                    return new F(function(){return _mF/* sFBq */(255);});
                  }
                }else{
                  var _mV/* sFCk */ = _mE/* sFBp */-1|0;
                  if(255>_mV/* sFCk */){
                    if(0>_mV/* sFCk */){
                      return new F(function(){return _mF/* sFBq */(0);});
                    }else{
                      return new F(function(){return _mF/* sFBq */(_mV/* sFCk */);});
                    }
                  }else{
                    return new F(function(){return _mF/* sFBq */(255);});
                  }
                }
              },
              _mW/* sFCp */ = E(_lJ/* sFyH */);
              if(!_mW/* sFCp */._){
                return B(_mB/* sFBm */(0));
              }else{
                return B(_mB/* sFBm */(E(_mW/* sFCp */.a)));
              }
            }) : new T(function(){
              var _mX/* sFCv */ = function(_mY/* sFCw */){
                var _mZ/* sFCx */ = _mY/* sFCw */*256,
                _n0/* sFCy */ = _mZ/* sFCx */&4294967295,
                _n1/* sFCz */ = function(_n2/* sFCA */){
                  var _n3/* sFCD */ = E(_lL/* sFyK */)*256,
                  _n4/* sFCE */ = _n3/* sFCD */&4294967295,
                  _n5/* sFCF */ = function(_n6/* sFCG */){
                    var _n7/* sFCH */ = function(_n8/* sFCI */){
                      var _n9/* sFCJ */ = _n8/* sFCI */*256,
                      _na/* sFCK */ = _n9/* sFCJ */&4294967295;
                      if(_n9/* sFCJ */>=_na/* sFCK */){
                        return (255>_na/* sFCK */) ? (0>_na/* sFCK */) ? new T4(1,_n2/* sFCA */,_n6/* sFCG */,0,1) : new T4(1,_n2/* sFCA */,_n6/* sFCG */,_na/* sFCK */,1) : new T4(1,_n2/* sFCA */,_n6/* sFCG */,255,1);
                      }else{
                        var _nb/* sFCS */ = _na/* sFCK */-1|0;
                        return (255>_nb/* sFCS */) ? (0>_nb/* sFCS */) ? new T4(1,_n2/* sFCA */,_n6/* sFCG */,0,1) : new T4(1,_n2/* sFCA */,_n6/* sFCG */,_nb/* sFCS */,1) : new T4(1,_n2/* sFCA */,_n6/* sFCG */,255,1);
                      }
                    },
                    _nc/* sFCX */ = E(_lN/* sFyN */);
                    if(!_nc/* sFCX */._){
                      return new F(function(){return _n7/* sFCH */(0);});
                    }else{
                      return new F(function(){return _n7/* sFCH */(E(_nc/* sFCX */.a));});
                    }
                  };
                  if(_n3/* sFCD */>=_n4/* sFCE */){
                    if(255>_n4/* sFCE */){
                      if(0>_n4/* sFCE */){
                        return new F(function(){return _n5/* sFCF */(0);});
                      }else{
                        return new F(function(){return _n5/* sFCF */(_n4/* sFCE */);});
                      }
                    }else{
                      return new F(function(){return _n5/* sFCF */(255);});
                    }
                  }else{
                    var _nd/* sFD8 */ = _n4/* sFCE */-1|0;
                    if(255>_nd/* sFD8 */){
                      if(0>_nd/* sFD8 */){
                        return new F(function(){return _n5/* sFCF */(0);});
                      }else{
                        return new F(function(){return _n5/* sFCF */(_nd/* sFD8 */);});
                      }
                    }else{
                      return new F(function(){return _n5/* sFCF */(255);});
                    }
                  }
                };
                if(_mZ/* sFCx */>=_n0/* sFCy */){
                  if(255>_n0/* sFCy */){
                    if(0>_n0/* sFCy */){
                      return new F(function(){return _n1/* sFCz */(0);});
                    }else{
                      return new F(function(){return _n1/* sFCz */(_n0/* sFCy */);});
                    }
                  }else{
                    return new F(function(){return _n1/* sFCz */(255);});
                  }
                }else{
                  var _ne/* sFDk */ = _n0/* sFCy */-1|0;
                  if(255>_ne/* sFDk */){
                    if(0>_ne/* sFDk */){
                      return new F(function(){return _n1/* sFCz */(0);});
                    }else{
                      return new F(function(){return _n1/* sFCz */(_ne/* sFDk */);});
                    }
                  }else{
                    return new F(function(){return _n1/* sFCz */(255);});
                  }
                }
              },
              _nf/* sFDp */ = E(_lJ/* sFyH */);
              if(!_nf/* sFDp */._){
                return B(_mX/* sFCv */(0));
              }else{
                return B(_mX/* sFCv */(E(_nf/* sFDp */.a)));
              }
            });
          default:
            var _ng/* sFDC */ = rMV/* EXTERNAL */(E(E(_lO/* sFyO */.a).c)),
            _nh/* sFDF */ = E(_ng/* sFDC */);
            if(!_nh/* sFDF */._){
              var _ni/* sFDL */ = B(A2(_lO/* sFyO */.b,E(_nh/* sFDF */.a).a, _/* EXTERNAL */)),
              _nj/* sFDN */ = _ni/* sFDL */;
              return new T(function(){
                var _nk/* sFDO */ = function(_nl/* sFDP */){
                  var _nm/* sFDQ */ = _nl/* sFDP */*256,
                  _nn/* sFDR */ = _nm/* sFDQ */&4294967295,
                  _no/* sFDS */ = function(_np/* sFDT */){
                    var _nq/* sFDW */ = E(_lL/* sFyK */)*256,
                    _nr/* sFDX */ = _nq/* sFDW */&4294967295,
                    _ns/* sFDY */ = function(_nt/* sFDZ */){
                      var _nu/* sFE0 */ = function(_nv/* sFE1 */){
                        var _nw/* sFE2 */ = _nv/* sFE1 */*256,
                        _nx/* sFE3 */ = _nw/* sFE2 */&4294967295,
                        _ny/* sFE4 */ = function(_nz/* sFE5 */){
                          var _nA/* sFE6 */ = E(_nj/* sFDN */);
                          return (1>_nA/* sFE6 */) ? (0>_nA/* sFE6 */) ? new T4(1,_np/* sFDT */,_nt/* sFDZ */,_nz/* sFE5 */,0) : new T4(1,_np/* sFDT */,_nt/* sFDZ */,_nz/* sFE5 */,_nA/* sFE6 */) : new T4(1,_np/* sFDT */,_nt/* sFDZ */,_nz/* sFE5 */,1);
                        };
                        if(_nw/* sFE2 */>=_nx/* sFE3 */){
                          if(255>_nx/* sFE3 */){
                            if(0>_nx/* sFE3 */){
                              return new F(function(){return _ny/* sFE4 */(0);});
                            }else{
                              return new F(function(){return _ny/* sFE4 */(_nx/* sFE3 */);});
                            }
                          }else{
                            return new F(function(){return _ny/* sFE4 */(255);});
                          }
                        }else{
                          var _nB/* sFEj */ = _nx/* sFE3 */-1|0;
                          if(255>_nB/* sFEj */){
                            if(0>_nB/* sFEj */){
                              return new F(function(){return _ny/* sFE4 */(0);});
                            }else{
                              return new F(function(){return _ny/* sFE4 */(_nB/* sFEj */);});
                            }
                          }else{
                            return new F(function(){return _ny/* sFE4 */(255);});
                          }
                        }
                      },
                      _nC/* sFEo */ = E(_lN/* sFyN */);
                      if(!_nC/* sFEo */._){
                        return new F(function(){return _nu/* sFE0 */(0);});
                      }else{
                        return new F(function(){return _nu/* sFE0 */(E(_nC/* sFEo */.a));});
                      }
                    };
                    if(_nq/* sFDW */>=_nr/* sFDX */){
                      if(255>_nr/* sFDX */){
                        if(0>_nr/* sFDX */){
                          return new F(function(){return _ns/* sFDY */(0);});
                        }else{
                          return new F(function(){return _ns/* sFDY */(_nr/* sFDX */);});
                        }
                      }else{
                        return new F(function(){return _ns/* sFDY */(255);});
                      }
                    }else{
                      var _nD/* sFEz */ = _nr/* sFDX */-1|0;
                      if(255>_nD/* sFEz */){
                        if(0>_nD/* sFEz */){
                          return new F(function(){return _ns/* sFDY */(0);});
                        }else{
                          return new F(function(){return _ns/* sFDY */(_nD/* sFEz */);});
                        }
                      }else{
                        return new F(function(){return _ns/* sFDY */(255);});
                      }
                    }
                  };
                  if(_nm/* sFDQ */>=_nn/* sFDR */){
                    if(255>_nn/* sFDR */){
                      if(0>_nn/* sFDR */){
                        return new F(function(){return _no/* sFDS */(0);});
                      }else{
                        return new F(function(){return _no/* sFDS */(_nn/* sFDR */);});
                      }
                    }else{
                      return new F(function(){return _no/* sFDS */(255);});
                    }
                  }else{
                    var _nE/* sFEL */ = _nn/* sFDR */-1|0;
                    if(255>_nE/* sFEL */){
                      if(0>_nE/* sFEL */){
                        return new F(function(){return _no/* sFDS */(0);});
                      }else{
                        return new F(function(){return _no/* sFDS */(_nE/* sFEL */);});
                      }
                    }else{
                      return new F(function(){return _no/* sFDS */(255);});
                    }
                  }
                },
                _nF/* sFEQ */ = E(_lJ/* sFyH */);
                if(!_nF/* sFEQ */._){
                  return B(_nk/* sFDO */(0));
                }else{
                  return B(_nk/* sFDO */(E(_nF/* sFEQ */.a)));
                }
              });
            }else{
              return new T(function(){
                var _nG/* sFEW */ = function(_nH/* sFEX */){
                  var _nI/* sFEY */ = _nH/* sFEX */*256,
                  _nJ/* sFEZ */ = _nI/* sFEY */&4294967295,
                  _nK/* sFF0 */ = function(_nL/* sFF1 */){
                    var _nM/* sFF4 */ = E(_lL/* sFyK */)*256,
                    _nN/* sFF5 */ = _nM/* sFF4 */&4294967295,
                    _nO/* sFF6 */ = function(_nP/* sFF7 */){
                      var _nQ/* sFF8 */ = function(_nR/* sFF9 */){
                        var _nS/* sFFa */ = _nR/* sFF9 */*256,
                        _nT/* sFFb */ = _nS/* sFFa */&4294967295;
                        if(_nS/* sFFa */>=_nT/* sFFb */){
                          return (255>_nT/* sFFb */) ? (0>_nT/* sFFb */) ? new T4(1,_nL/* sFF1 */,_nP/* sFF7 */,0,1) : new T4(1,_nL/* sFF1 */,_nP/* sFF7 */,_nT/* sFFb */,1) : new T4(1,_nL/* sFF1 */,_nP/* sFF7 */,255,1);
                        }else{
                          var _nU/* sFFj */ = _nT/* sFFb */-1|0;
                          return (255>_nU/* sFFj */) ? (0>_nU/* sFFj */) ? new T4(1,_nL/* sFF1 */,_nP/* sFF7 */,0,1) : new T4(1,_nL/* sFF1 */,_nP/* sFF7 */,_nU/* sFFj */,1) : new T4(1,_nL/* sFF1 */,_nP/* sFF7 */,255,1);
                        }
                      },
                      _nV/* sFFo */ = E(_lN/* sFyN */);
                      if(!_nV/* sFFo */._){
                        return new F(function(){return _nQ/* sFF8 */(0);});
                      }else{
                        return new F(function(){return _nQ/* sFF8 */(E(_nV/* sFFo */.a));});
                      }
                    };
                    if(_nM/* sFF4 */>=_nN/* sFF5 */){
                      if(255>_nN/* sFF5 */){
                        if(0>_nN/* sFF5 */){
                          return new F(function(){return _nO/* sFF6 */(0);});
                        }else{
                          return new F(function(){return _nO/* sFF6 */(_nN/* sFF5 */);});
                        }
                      }else{
                        return new F(function(){return _nO/* sFF6 */(255);});
                      }
                    }else{
                      var _nW/* sFFz */ = _nN/* sFF5 */-1|0;
                      if(255>_nW/* sFFz */){
                        if(0>_nW/* sFFz */){
                          return new F(function(){return _nO/* sFF6 */(0);});
                        }else{
                          return new F(function(){return _nO/* sFF6 */(_nW/* sFFz */);});
                        }
                      }else{
                        return new F(function(){return _nO/* sFF6 */(255);});
                      }
                    }
                  };
                  if(_nI/* sFEY */>=_nJ/* sFEZ */){
                    if(255>_nJ/* sFEZ */){
                      if(0>_nJ/* sFEZ */){
                        return new F(function(){return _nK/* sFF0 */(0);});
                      }else{
                        return new F(function(){return _nK/* sFF0 */(_nJ/* sFEZ */);});
                      }
                    }else{
                      return new F(function(){return _nK/* sFF0 */(255);});
                    }
                  }else{
                    var _nX/* sFFL */ = _nJ/* sFEZ */-1|0;
                    if(255>_nX/* sFFL */){
                      if(0>_nX/* sFFL */){
                        return new F(function(){return _nK/* sFF0 */(0);});
                      }else{
                        return new F(function(){return _nK/* sFF0 */(_nX/* sFFL */);});
                      }
                    }else{
                      return new F(function(){return _nK/* sFF0 */(255);});
                    }
                  }
                },
                _nY/* sFFQ */ = E(_lJ/* sFyH */);
                if(!_nY/* sFFQ */._){
                  return B(_nG/* sFEW */(0));
                }else{
                  return B(_nG/* sFEW */(E(_nY/* sFFQ */.a)));
                }
              });
            }
        }
      },
      _nZ/* sFFV */ = E(_lG/* sFyC */);
      switch(_nZ/* sFFV */._){
        case 0:
          return new F(function(){return _lM/* sFyL */(_/* EXTERNAL */, new T1(1,_nZ/* sFFV */.a));});
          break;
        case 1:
          var _o0/* sFFZ */ = B(A1(_nZ/* sFFV */.a,_/* EXTERNAL */));
          return new F(function(){return _lM/* sFyL */(_/* EXTERNAL */, new T1(1,_o0/* sFFZ */));});
          break;
        case 2:
          var _o1/* sFGb */ = rMV/* EXTERNAL */(E(E(_nZ/* sFFV */.a).c)),
          _o2/* sFGe */ = E(_o1/* sFGb */);
          if(!_o2/* sFGe */._){
            var _o3/* sFGi */ = new T(function(){
              return B(A1(_nZ/* sFFV */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_o2/* sFGe */.a));
              })));
            });
            return new F(function(){return _lM/* sFyL */(_/* EXTERNAL */, new T1(1,_o3/* sFGi */));});
          }else{
            return new F(function(){return _lM/* sFyL */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _o4/* sFGt */ = rMV/* EXTERNAL */(E(E(_nZ/* sFFV */.a).c)),
          _o5/* sFGw */ = E(_o4/* sFGt */);
          if(!_o5/* sFGw */._){
            var _o6/* sFGC */ = B(A2(_nZ/* sFFV */.b,E(_o5/* sFGw */.a).a, _/* EXTERNAL */));
            return new F(function(){return _lM/* sFyL */(_/* EXTERNAL */, new T1(1,_o6/* sFGC */));});
          }else{
            return new F(function(){return _lM/* sFyL */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _o7/* sFGH */ = function(_/* EXTERNAL */){
      var _o8/* sFGJ */ = function(_/* EXTERNAL */, _o9/* sFGL */){
        var _oa/* sFGM */ = E(_lH/* sFyD */);
        switch(_oa/* sFGM */._){
          case 0:
            return new T(function(){
              var _ob/* sFGO */ = function(_oc/* sFGP */){
                var _od/* sFGQ */ = _oc/* sFGP */*256,
                _oe/* sFGR */ = _od/* sFGQ */&4294967295,
                _of/* sFGS */ = function(_og/* sFGT */){
                  var _oh/* sFGU */ = function(_oi/* sFGV */){
                    var _oj/* sFGW */ = _oi/* sFGV */*256,
                    _ok/* sFGX */ = _oj/* sFGW */&4294967295,
                    _ol/* sFGY */ = function(_om/* sFGZ */){
                      var _on/* sFH0 */ = E(_oa/* sFGM */.a);
                      return (1>_on/* sFH0 */) ? (0>_on/* sFH0 */) ? new T4(1,_og/* sFGT */,0,_om/* sFGZ */,0) : new T4(1,_og/* sFGT */,0,_om/* sFGZ */,_on/* sFH0 */) : new T4(1,_og/* sFGT */,0,_om/* sFGZ */,1);
                    };
                    if(_oj/* sFGW */>=_ok/* sFGX */){
                      if(255>_ok/* sFGX */){
                        if(0>_ok/* sFGX */){
                          return new F(function(){return _ol/* sFGY */(0);});
                        }else{
                          return new F(function(){return _ol/* sFGY */(_ok/* sFGX */);});
                        }
                      }else{
                        return new F(function(){return _ol/* sFGY */(255);});
                      }
                    }else{
                      var _oo/* sFHd */ = _ok/* sFGX */-1|0;
                      if(255>_oo/* sFHd */){
                        if(0>_oo/* sFHd */){
                          return new F(function(){return _ol/* sFGY */(0);});
                        }else{
                          return new F(function(){return _ol/* sFGY */(_oo/* sFHd */);});
                        }
                      }else{
                        return new F(function(){return _ol/* sFGY */(255);});
                      }
                    }
                  },
                  _op/* sFHi */ = E(_o9/* sFGL */);
                  if(!_op/* sFHi */._){
                    return new F(function(){return _oh/* sFGU */(0);});
                  }else{
                    return new F(function(){return _oh/* sFGU */(E(_op/* sFHi */.a));});
                  }
                };
                if(_od/* sFGQ */>=_oe/* sFGR */){
                  if(255>_oe/* sFGR */){
                    if(0>_oe/* sFGR */){
                      return new F(function(){return _of/* sFGS */(0);});
                    }else{
                      return new F(function(){return _of/* sFGS */(_oe/* sFGR */);});
                    }
                  }else{
                    return new F(function(){return _of/* sFGS */(255);});
                  }
                }else{
                  var _oq/* sFHt */ = _oe/* sFGR */-1|0;
                  if(255>_oq/* sFHt */){
                    if(0>_oq/* sFHt */){
                      return new F(function(){return _of/* sFGS */(0);});
                    }else{
                      return new F(function(){return _of/* sFGS */(_oq/* sFHt */);});
                    }
                  }else{
                    return new F(function(){return _of/* sFGS */(255);});
                  }
                }
              },
              _or/* sFHy */ = E(_lJ/* sFyH */);
              if(!_or/* sFHy */._){
                return B(_ob/* sFGO */(0));
              }else{
                return B(_ob/* sFGO */(E(_or/* sFHy */.a)));
              }
            });
          case 1:
            var _os/* sFHE */ = B(A1(_oa/* sFGM */.a,_/* EXTERNAL */)),
            _ot/* sFHG */ = _os/* sFHE */;
            return new T(function(){
              var _ou/* sFHH */ = function(_ov/* sFHI */){
                var _ow/* sFHJ */ = _ov/* sFHI */*256,
                _ox/* sFHK */ = _ow/* sFHJ */&4294967295,
                _oy/* sFHL */ = function(_oz/* sFHM */){
                  var _oA/* sFHN */ = function(_oB/* sFHO */){
                    var _oC/* sFHP */ = _oB/* sFHO */*256,
                    _oD/* sFHQ */ = _oC/* sFHP */&4294967295,
                    _oE/* sFHR */ = function(_oF/* sFHS */){
                      var _oG/* sFHT */ = E(_ot/* sFHG */);
                      return (1>_oG/* sFHT */) ? (0>_oG/* sFHT */) ? new T4(1,_oz/* sFHM */,0,_oF/* sFHS */,0) : new T4(1,_oz/* sFHM */,0,_oF/* sFHS */,_oG/* sFHT */) : new T4(1,_oz/* sFHM */,0,_oF/* sFHS */,1);
                    };
                    if(_oC/* sFHP */>=_oD/* sFHQ */){
                      if(255>_oD/* sFHQ */){
                        if(0>_oD/* sFHQ */){
                          return new F(function(){return _oE/* sFHR */(0);});
                        }else{
                          return new F(function(){return _oE/* sFHR */(_oD/* sFHQ */);});
                        }
                      }else{
                        return new F(function(){return _oE/* sFHR */(255);});
                      }
                    }else{
                      var _oH/* sFI6 */ = _oD/* sFHQ */-1|0;
                      if(255>_oH/* sFI6 */){
                        if(0>_oH/* sFI6 */){
                          return new F(function(){return _oE/* sFHR */(0);});
                        }else{
                          return new F(function(){return _oE/* sFHR */(_oH/* sFI6 */);});
                        }
                      }else{
                        return new F(function(){return _oE/* sFHR */(255);});
                      }
                    }
                  },
                  _oI/* sFIb */ = E(_o9/* sFGL */);
                  if(!_oI/* sFIb */._){
                    return new F(function(){return _oA/* sFHN */(0);});
                  }else{
                    return new F(function(){return _oA/* sFHN */(E(_oI/* sFIb */.a));});
                  }
                };
                if(_ow/* sFHJ */>=_ox/* sFHK */){
                  if(255>_ox/* sFHK */){
                    if(0>_ox/* sFHK */){
                      return new F(function(){return _oy/* sFHL */(0);});
                    }else{
                      return new F(function(){return _oy/* sFHL */(_ox/* sFHK */);});
                    }
                  }else{
                    return new F(function(){return _oy/* sFHL */(255);});
                  }
                }else{
                  var _oJ/* sFIm */ = _ox/* sFHK */-1|0;
                  if(255>_oJ/* sFIm */){
                    if(0>_oJ/* sFIm */){
                      return new F(function(){return _oy/* sFHL */(0);});
                    }else{
                      return new F(function(){return _oy/* sFHL */(_oJ/* sFIm */);});
                    }
                  }else{
                    return new F(function(){return _oy/* sFHL */(255);});
                  }
                }
              },
              _oK/* sFIr */ = E(_lJ/* sFyH */);
              if(!_oK/* sFIr */._){
                return B(_ou/* sFHH */(0));
              }else{
                return B(_ou/* sFHH */(E(_oK/* sFIr */.a)));
              }
            });
          case 2:
            var _oL/* sFIE */ = rMV/* EXTERNAL */(E(E(_oa/* sFGM */.a).c)),
            _oM/* sFIH */ = E(_oL/* sFIE */);
            return (_oM/* sFIH */._==0) ? new T(function(){
              var _oN/* sFIK */ = function(_oO/* sFIL */){
                var _oP/* sFIM */ = _oO/* sFIL */*256,
                _oQ/* sFIN */ = _oP/* sFIM */&4294967295,
                _oR/* sFIO */ = function(_oS/* sFIP */){
                  var _oT/* sFIQ */ = function(_oU/* sFIR */){
                    var _oV/* sFIS */ = _oU/* sFIR */*256,
                    _oW/* sFIT */ = _oV/* sFIS */&4294967295,
                    _oX/* sFIU */ = function(_oY/* sFIV */){
                      var _oZ/* sFIX */ = B(A1(_oa/* sFGM */.b,new T(function(){
                        return B(_fB/* Data.Tuple.fst */(_oM/* sFIH */.a));
                      })));
                      return (1>_oZ/* sFIX */) ? (0>_oZ/* sFIX */) ? new T4(1,_oS/* sFIP */,0,_oY/* sFIV */,0) : new T4(1,_oS/* sFIP */,0,_oY/* sFIV */,_oZ/* sFIX */) : new T4(1,_oS/* sFIP */,0,_oY/* sFIV */,1);
                    };
                    if(_oV/* sFIS */>=_oW/* sFIT */){
                      if(255>_oW/* sFIT */){
                        if(0>_oW/* sFIT */){
                          return new F(function(){return _oX/* sFIU */(0);});
                        }else{
                          return new F(function(){return _oX/* sFIU */(_oW/* sFIT */);});
                        }
                      }else{
                        return new F(function(){return _oX/* sFIU */(255);});
                      }
                    }else{
                      var _p0/* sFJa */ = _oW/* sFIT */-1|0;
                      if(255>_p0/* sFJa */){
                        if(0>_p0/* sFJa */){
                          return new F(function(){return _oX/* sFIU */(0);});
                        }else{
                          return new F(function(){return _oX/* sFIU */(_p0/* sFJa */);});
                        }
                      }else{
                        return new F(function(){return _oX/* sFIU */(255);});
                      }
                    }
                  },
                  _p1/* sFJf */ = E(_o9/* sFGL */);
                  if(!_p1/* sFJf */._){
                    return new F(function(){return _oT/* sFIQ */(0);});
                  }else{
                    return new F(function(){return _oT/* sFIQ */(E(_p1/* sFJf */.a));});
                  }
                };
                if(_oP/* sFIM */>=_oQ/* sFIN */){
                  if(255>_oQ/* sFIN */){
                    if(0>_oQ/* sFIN */){
                      return new F(function(){return _oR/* sFIO */(0);});
                    }else{
                      return new F(function(){return _oR/* sFIO */(_oQ/* sFIN */);});
                    }
                  }else{
                    return new F(function(){return _oR/* sFIO */(255);});
                  }
                }else{
                  var _p2/* sFJq */ = _oQ/* sFIN */-1|0;
                  if(255>_p2/* sFJq */){
                    if(0>_p2/* sFJq */){
                      return new F(function(){return _oR/* sFIO */(0);});
                    }else{
                      return new F(function(){return _oR/* sFIO */(_p2/* sFJq */);});
                    }
                  }else{
                    return new F(function(){return _oR/* sFIO */(255);});
                  }
                }
              },
              _p3/* sFJv */ = E(_lJ/* sFyH */);
              if(!_p3/* sFJv */._){
                return B(_oN/* sFIK */(0));
              }else{
                return B(_oN/* sFIK */(E(_p3/* sFJv */.a)));
              }
            }) : new T(function(){
              var _p4/* sFJB */ = function(_p5/* sFJC */){
                var _p6/* sFJD */ = _p5/* sFJC */*256,
                _p7/* sFJE */ = _p6/* sFJD */&4294967295,
                _p8/* sFJF */ = function(_p9/* sFJG */){
                  var _pa/* sFJH */ = function(_pb/* sFJI */){
                    var _pc/* sFJJ */ = _pb/* sFJI */*256,
                    _pd/* sFJK */ = _pc/* sFJJ */&4294967295;
                    if(_pc/* sFJJ */>=_pd/* sFJK */){
                      return (255>_pd/* sFJK */) ? (0>_pd/* sFJK */) ? new T4(1,_p9/* sFJG */,0,0,1) : new T4(1,_p9/* sFJG */,0,_pd/* sFJK */,1) : new T4(1,_p9/* sFJG */,0,255,1);
                    }else{
                      var _pe/* sFJS */ = _pd/* sFJK */-1|0;
                      return (255>_pe/* sFJS */) ? (0>_pe/* sFJS */) ? new T4(1,_p9/* sFJG */,0,0,1) : new T4(1,_p9/* sFJG */,0,_pe/* sFJS */,1) : new T4(1,_p9/* sFJG */,0,255,1);
                    }
                  },
                  _pf/* sFJX */ = E(_o9/* sFGL */);
                  if(!_pf/* sFJX */._){
                    return new F(function(){return _pa/* sFJH */(0);});
                  }else{
                    return new F(function(){return _pa/* sFJH */(E(_pf/* sFJX */.a));});
                  }
                };
                if(_p6/* sFJD */>=_p7/* sFJE */){
                  if(255>_p7/* sFJE */){
                    if(0>_p7/* sFJE */){
                      return new F(function(){return _p8/* sFJF */(0);});
                    }else{
                      return new F(function(){return _p8/* sFJF */(_p7/* sFJE */);});
                    }
                  }else{
                    return new F(function(){return _p8/* sFJF */(255);});
                  }
                }else{
                  var _pg/* sFK8 */ = _p7/* sFJE */-1|0;
                  if(255>_pg/* sFK8 */){
                    if(0>_pg/* sFK8 */){
                      return new F(function(){return _p8/* sFJF */(0);});
                    }else{
                      return new F(function(){return _p8/* sFJF */(_pg/* sFK8 */);});
                    }
                  }else{
                    return new F(function(){return _p8/* sFJF */(255);});
                  }
                }
              },
              _ph/* sFKd */ = E(_lJ/* sFyH */);
              if(!_ph/* sFKd */._){
                return B(_p4/* sFJB */(0));
              }else{
                return B(_p4/* sFJB */(E(_ph/* sFKd */.a)));
              }
            });
          default:
            var _pi/* sFKq */ = rMV/* EXTERNAL */(E(E(_oa/* sFGM */.a).c)),
            _pj/* sFKt */ = E(_pi/* sFKq */);
            if(!_pj/* sFKt */._){
              var _pk/* sFKz */ = B(A2(_oa/* sFGM */.b,E(_pj/* sFKt */.a).a, _/* EXTERNAL */)),
              _pl/* sFKB */ = _pk/* sFKz */;
              return new T(function(){
                var _pm/* sFKC */ = function(_pn/* sFKD */){
                  var _po/* sFKE */ = _pn/* sFKD */*256,
                  _pp/* sFKF */ = _po/* sFKE */&4294967295,
                  _pq/* sFKG */ = function(_pr/* sFKH */){
                    var _ps/* sFKI */ = function(_pt/* sFKJ */){
                      var _pu/* sFKK */ = _pt/* sFKJ */*256,
                      _pv/* sFKL */ = _pu/* sFKK */&4294967295,
                      _pw/* sFKM */ = function(_px/* sFKN */){
                        var _py/* sFKO */ = E(_pl/* sFKB */);
                        return (1>_py/* sFKO */) ? (0>_py/* sFKO */) ? new T4(1,_pr/* sFKH */,0,_px/* sFKN */,0) : new T4(1,_pr/* sFKH */,0,_px/* sFKN */,_py/* sFKO */) : new T4(1,_pr/* sFKH */,0,_px/* sFKN */,1);
                      };
                      if(_pu/* sFKK */>=_pv/* sFKL */){
                        if(255>_pv/* sFKL */){
                          if(0>_pv/* sFKL */){
                            return new F(function(){return _pw/* sFKM */(0);});
                          }else{
                            return new F(function(){return _pw/* sFKM */(_pv/* sFKL */);});
                          }
                        }else{
                          return new F(function(){return _pw/* sFKM */(255);});
                        }
                      }else{
                        var _pz/* sFL1 */ = _pv/* sFKL */-1|0;
                        if(255>_pz/* sFL1 */){
                          if(0>_pz/* sFL1 */){
                            return new F(function(){return _pw/* sFKM */(0);});
                          }else{
                            return new F(function(){return _pw/* sFKM */(_pz/* sFL1 */);});
                          }
                        }else{
                          return new F(function(){return _pw/* sFKM */(255);});
                        }
                      }
                    },
                    _pA/* sFL6 */ = E(_o9/* sFGL */);
                    if(!_pA/* sFL6 */._){
                      return new F(function(){return _ps/* sFKI */(0);});
                    }else{
                      return new F(function(){return _ps/* sFKI */(E(_pA/* sFL6 */.a));});
                    }
                  };
                  if(_po/* sFKE */>=_pp/* sFKF */){
                    if(255>_pp/* sFKF */){
                      if(0>_pp/* sFKF */){
                        return new F(function(){return _pq/* sFKG */(0);});
                      }else{
                        return new F(function(){return _pq/* sFKG */(_pp/* sFKF */);});
                      }
                    }else{
                      return new F(function(){return _pq/* sFKG */(255);});
                    }
                  }else{
                    var _pB/* sFLh */ = _pp/* sFKF */-1|0;
                    if(255>_pB/* sFLh */){
                      if(0>_pB/* sFLh */){
                        return new F(function(){return _pq/* sFKG */(0);});
                      }else{
                        return new F(function(){return _pq/* sFKG */(_pB/* sFLh */);});
                      }
                    }else{
                      return new F(function(){return _pq/* sFKG */(255);});
                    }
                  }
                },
                _pC/* sFLm */ = E(_lJ/* sFyH */);
                if(!_pC/* sFLm */._){
                  return B(_pm/* sFKC */(0));
                }else{
                  return B(_pm/* sFKC */(E(_pC/* sFLm */.a)));
                }
              });
            }else{
              return new T(function(){
                var _pD/* sFLs */ = function(_pE/* sFLt */){
                  var _pF/* sFLu */ = _pE/* sFLt */*256,
                  _pG/* sFLv */ = _pF/* sFLu */&4294967295,
                  _pH/* sFLw */ = function(_pI/* sFLx */){
                    var _pJ/* sFLy */ = function(_pK/* sFLz */){
                      var _pL/* sFLA */ = _pK/* sFLz */*256,
                      _pM/* sFLB */ = _pL/* sFLA */&4294967295;
                      if(_pL/* sFLA */>=_pM/* sFLB */){
                        return (255>_pM/* sFLB */) ? (0>_pM/* sFLB */) ? new T4(1,_pI/* sFLx */,0,0,1) : new T4(1,_pI/* sFLx */,0,_pM/* sFLB */,1) : new T4(1,_pI/* sFLx */,0,255,1);
                      }else{
                        var _pN/* sFLJ */ = _pM/* sFLB */-1|0;
                        return (255>_pN/* sFLJ */) ? (0>_pN/* sFLJ */) ? new T4(1,_pI/* sFLx */,0,0,1) : new T4(1,_pI/* sFLx */,0,_pN/* sFLJ */,1) : new T4(1,_pI/* sFLx */,0,255,1);
                      }
                    },
                    _pO/* sFLO */ = E(_o9/* sFGL */);
                    if(!_pO/* sFLO */._){
                      return new F(function(){return _pJ/* sFLy */(0);});
                    }else{
                      return new F(function(){return _pJ/* sFLy */(E(_pO/* sFLO */.a));});
                    }
                  };
                  if(_pF/* sFLu */>=_pG/* sFLv */){
                    if(255>_pG/* sFLv */){
                      if(0>_pG/* sFLv */){
                        return new F(function(){return _pH/* sFLw */(0);});
                      }else{
                        return new F(function(){return _pH/* sFLw */(_pG/* sFLv */);});
                      }
                    }else{
                      return new F(function(){return _pH/* sFLw */(255);});
                    }
                  }else{
                    var _pP/* sFLZ */ = _pG/* sFLv */-1|0;
                    if(255>_pP/* sFLZ */){
                      if(0>_pP/* sFLZ */){
                        return new F(function(){return _pH/* sFLw */(0);});
                      }else{
                        return new F(function(){return _pH/* sFLw */(_pP/* sFLZ */);});
                      }
                    }else{
                      return new F(function(){return _pH/* sFLw */(255);});
                    }
                  }
                },
                _pQ/* sFM4 */ = E(_lJ/* sFyH */);
                if(!_pQ/* sFM4 */._){
                  return B(_pD/* sFLs */(0));
                }else{
                  return B(_pD/* sFLs */(E(_pQ/* sFM4 */.a)));
                }
              });
            }
        }
      },
      _pR/* sFM9 */ = E(_lG/* sFyC */);
      switch(_pR/* sFM9 */._){
        case 0:
          return new F(function(){return _o8/* sFGJ */(_/* EXTERNAL */, new T1(1,_pR/* sFM9 */.a));});
          break;
        case 1:
          var _pS/* sFMd */ = B(A1(_pR/* sFM9 */.a,_/* EXTERNAL */));
          return new F(function(){return _o8/* sFGJ */(_/* EXTERNAL */, new T1(1,_pS/* sFMd */));});
          break;
        case 2:
          var _pT/* sFMp */ = rMV/* EXTERNAL */(E(E(_pR/* sFM9 */.a).c)),
          _pU/* sFMs */ = E(_pT/* sFMp */);
          if(!_pU/* sFMs */._){
            var _pV/* sFMw */ = new T(function(){
              return B(A1(_pR/* sFM9 */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_pU/* sFMs */.a));
              })));
            });
            return new F(function(){return _o8/* sFGJ */(_/* EXTERNAL */, new T1(1,_pV/* sFMw */));});
          }else{
            return new F(function(){return _o8/* sFGJ */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _pW/* sFMH */ = rMV/* EXTERNAL */(E(E(_pR/* sFM9 */.a).c)),
          _pX/* sFMK */ = E(_pW/* sFMH */);
          if(!_pX/* sFMK */._){
            var _pY/* sFMQ */ = B(A2(_pR/* sFM9 */.b,E(_pX/* sFMK */.a).a, _/* EXTERNAL */));
            return new F(function(){return _o8/* sFGJ */(_/* EXTERNAL */, new T1(1,_pY/* sFMQ */));});
          }else{
            return new F(function(){return _o8/* sFGJ */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _pZ/* sFMV */ = E(_lF/* sFyB */);
    switch(_pZ/* sFMV */._){
      case 0:
        return new F(function(){return _lK/* sFyI */(_/* EXTERNAL */, _pZ/* sFMV */.a);});
        break;
      case 1:
        var _q0/* sFMY */ = B(A1(_pZ/* sFMV */.a,_/* EXTERNAL */));
        return new F(function(){return _lK/* sFyI */(_/* EXTERNAL */, _q0/* sFMY */);});
        break;
      case 2:
        var _q1/* sFN9 */ = rMV/* EXTERNAL */(E(E(_pZ/* sFMV */.a).c)),
        _q2/* sFNc */ = E(_q1/* sFN9 */);
        if(!_q2/* sFNc */._){
          var _q3/* sFNj */ = new T(function(){
            return B(A1(_pZ/* sFMV */.b,new T(function(){
              return E(E(_q2/* sFNc */.a).a);
            })));
          });
          return new F(function(){return _lK/* sFyI */(_/* EXTERNAL */, _q3/* sFNj */);});
        }else{
          return new F(function(){return _o7/* sFGH */(_/* EXTERNAL */);});
        }
        break;
      default:
        var _q4/* sFNt */ = rMV/* EXTERNAL */(E(E(_pZ/* sFMV */.a).c)),
        _q5/* sFNw */ = E(_q4/* sFNt */);
        if(!_q5/* sFNw */._){
          var _q6/* sFNC */ = B(A2(_pZ/* sFMV */.b,E(_q5/* sFNw */.a).a, _/* EXTERNAL */));
          return new F(function(){return _lK/* sFyI */(_/* EXTERNAL */, _q6/* sFNC */);});
        }else{
          return new F(function(){return _o7/* sFGH */(_/* EXTERNAL */);});
        }
    }
  },
  _q7/* sFNG */ = E(_lE/* sFyA */);
  switch(_q7/* sFNG */._){
    case 0:
      return new F(function(){return _lI/* sFyF */(_/* EXTERNAL */, new T1(1,_q7/* sFNG */.a));});
      break;
    case 1:
      var _q8/* sFNK */ = B(A1(_q7/* sFNG */.a,_/* EXTERNAL */));
      return new F(function(){return _lI/* sFyF */(_/* EXTERNAL */, new T1(1,_q8/* sFNK */));});
      break;
    case 2:
      var _q9/* sFNW */ = rMV/* EXTERNAL */(E(E(_q7/* sFNG */.a).c)),
      _qa/* sFNZ */ = E(_q9/* sFNW */);
      if(!_qa/* sFNZ */._){
        var _qb/* sFO3 */ = new T(function(){
          return B(A1(_q7/* sFNG */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_qa/* sFNZ */.a));
          })));
        });
        return new F(function(){return _lI/* sFyF */(_/* EXTERNAL */, new T1(1,_qb/* sFO3 */));});
      }else{
        return new F(function(){return _lI/* sFyF */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
      }
      break;
    default:
      var _qc/* sFOe */ = rMV/* EXTERNAL */(E(E(_q7/* sFNG */.a).c)),
      _qd/* sFOh */ = E(_qc/* sFOe */);
      if(!_qd/* sFOh */._){
        var _qe/* sFOn */ = B(A2(_q7/* sFNG */.b,E(_qd/* sFOh */.a).a, _/* EXTERNAL */));
        return new F(function(){return _lI/* sFyF */(_/* EXTERNAL */, new T1(1,_qe/* sFOn */));});
      }else{
        return new F(function(){return _lI/* sFyF */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
      }
  }
},
_qf/* lvl1 */ = new T(function(){
  return toJSStr/* EXTERNAL */(_6/* GHC.Types.[] */);
}),
_qg/* lvl2 */ = "rgb(",
_qh/* lvl3 */ = ",",
_qi/* lvl5 */ = "rgba(",
_qj/* lvl4 */ = ")",
_qk/* lvl6 */ = new T2(1,_qj/* Core.Render.Internal.lvl4 */,_6/* GHC.Types.[] */),
_ql/* $wcolor2JSString */ = function(_qm/* sFk8 */){
  var _qn/* sFk9 */ = E(_qm/* sFk8 */);
  if(!_qn/* sFk9 */._){
    var _qo/* sFkI */ = jsCat/* EXTERNAL */(new T2(1,_qg/* Core.Render.Internal.lvl2 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk9 */.a);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk9 */.b);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk9 */.c);
    }),_qk/* Core.Render.Internal.lvl6 */)))))), E(_qf/* Core.Render.Internal.lvl1 */));
    return E(_qo/* sFkI */);
  }else{
    var _qp/* sFlr */ = jsCat/* EXTERNAL */(new T2(1,_qi/* Core.Render.Internal.lvl5 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk9 */.a);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk9 */.b);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk9 */.c);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk9 */.d);
    }),_qk/* Core.Render.Internal.lvl6 */)))))))), E(_qf/* Core.Render.Internal.lvl1 */));
    return E(_qp/* sFlr */);
  }
},
_qq/* $w$c<*> */ = function(_qr/* s1DM */, _qs/* s1DN */){
  var _qt/* s1DO */ = E(_qr/* s1DM */),
  _qu/* s1E2 */ = function(_qv/* s1DR */){
    var _qw/* s1DS */ = E(_qs/* s1DN */),
    _qx/* s1DZ */ = function(_qy/* s1DV */){
      return new T2(0,E(new T1(0,new T(function(){
        return B(A1(_qv/* s1DR */,_qy/* s1DV */));
      }))),E(new T1(0,_/* EXTERNAL */)));
    };
    return new T2(0,E(_qw/* s1DS */.a),E(new T2(2,_qw/* s1DS */.b,new T1(1,_qx/* s1DZ */))));
  };
  return new T2(0,E(_qt/* s1DO */.a),E(new T2(2,_qt/* s1DO */.b,new T1(1,_qu/* s1E2 */))));
},
_qz/* <$ */ = function(_qA/* s35r */){
  return E(E(_qA/* s35r */).b);
},
_qB/* $fApplicativeSkeleton_$c*> */ = function(_qC/* s1E9 */, _qD/* s1Ea */, _qE/* s1Eb */){
  return new F(function(){return _qq/* Control.Monad.Skeleton.$w$c<*> */(B(A3(_qz/* GHC.Base.<$ */,_qC/* s1E9 */, _2E/* GHC.Base.id */, _qD/* s1Ea */)), _qE/* s1Eb */);});
},
_qF/* const */ = function(_qG/* s3aC */, _qH/* s3aD */){
  return E(_qG/* s3aC */);
},
_qI/* fmap */ = function(_qJ/* s35n */){
  return E(E(_qJ/* s35n */).a);
},
_qK/* $fApplicativeSkeleton_$c<* */ = function(_qL/* s1E5 */, _qM/* s1E6 */, _qN/* s1E7 */){
  return new F(function(){return _qq/* Control.Monad.Skeleton.$w$c<*> */(B(A3(_qI/* GHC.Base.fmap */,_qL/* s1E5 */, _qF/* GHC.Base.const */, _qM/* s1E6 */)), _qN/* s1E7 */);});
},
_qO/* a1 */ = function(_qP/* s1Dn */, _qQ/* s1Do */){
  return new T2(0,E(new T1(0,_qQ/* s1Do */)),E(new T1(0,_/* EXTERNAL */)));
},
_qR/* $fApplicativeSkeleton_$creturn */ = function(_qS/* B2 */, _qT/* B1 */){
  return new F(function(){return _qO/* Control.Monad.Skeleton.a1 */(_qS/* B2 */, _qT/* B1 */);});
},
_qU/* lvl1 */ = new T(function(){
  return B(_bo/* Control.Exception.Base.absentError */("w_s1yq Functor (Skeleton t)"));
}),
_qV/* lvl3 */ = new T(function(){
  return B(_qW/* Control.Monad.Skeleton.$fApplicativeSkeleton */(_qU/* Control.Monad.Skeleton.lvl1 */));
}),
_qX/* lvl4 */ = function(_qT/* B1 */){
  return new F(function(){return _qR/* Control.Monad.Skeleton.$fApplicativeSkeleton_$creturn */(_qV/* Control.Monad.Skeleton.lvl3 */, _qT/* B1 */);});
},
_qY/* $w$cpure */ = function(_qZ/* s1Ek */, _qT/* B1 */){
  return new F(function(){return _qX/* Control.Monad.Skeleton.lvl4 */(_qT/* B1 */);});
},
_r0/* lvl2 */ = function(_qT/* B1 */){
  return new F(function(){return _qY/* Control.Monad.Skeleton.$w$cpure */(_/* EXTERNAL */, _qT/* B1 */);});
},
_qW/* $fApplicativeSkeleton */ = function(_r1/* s1Eh */){
  return new T5(0,_r1/* s1Eh */,_r0/* Control.Monad.Skeleton.lvl2 */,_qq/* Control.Monad.Skeleton.$w$c<*> */,function(_qS/* B2 */, _qT/* B1 */){
    return new F(function(){return _qB/* Control.Monad.Skeleton.$fApplicativeSkeleton_$c*> */(_r1/* s1Eh */, _qS/* B2 */, _qT/* B1 */);});
  },function(_qS/* B2 */, _qT/* B1 */){
    return new F(function(){return _qK/* Control.Monad.Skeleton.$fApplicativeSkeleton_$c<* */(_r1/* s1Eh */, _qS/* B2 */, _qT/* B1 */);});
  });
},
_r2/* $fMonadSkeleton_$c>> */ = function(_r3/* s1DC */, _r4/* s1DD */, _r5/* s1DE */){
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,B(_r6/* Control.Monad.Skeleton.$fMonadSkeleton */(_r3/* s1DC */)), _r4/* s1DD */, function(_r7/* s1DG */){
    return E(_r5/* s1DE */);
  });});
},
_r8/* $fMonadSkeleton_$c>>= */ = function(_r9/* s1Dr */, _ra/* s1Ds */, _rb/* s1Dt */){
  var _rc/* s1Du */ = E(_ra/* s1Ds */);
  return new T2(0,E(_rc/* s1Du */.a),E(new T2(2,_rc/* s1Du */.b,new T1(1,_rb/* s1Dt */))));
},
_rd/* lvl */ = function(_re/* s1DB */){
  return new F(function(){return err/* EXTERNAL */(_re/* s1DB */);});
},
_r6/* $fMonadSkeleton */ = function(_rf/* s1DI */){
  return new T5(0,_rf/* s1DI */,function(_qS/* B2 */, _qT/* B1 */){
    return new F(function(){return _r8/* Control.Monad.Skeleton.$fMonadSkeleton_$c>>= */(_rf/* s1DI */, _qS/* B2 */, _qT/* B1 */);});
  },function(_qS/* B2 */, _qT/* B1 */){
    return new F(function(){return _r2/* Control.Monad.Skeleton.$fMonadSkeleton_$c>> */(_rf/* s1DI */, _qS/* B2 */, _qT/* B1 */);});
  },function(_qT/* B1 */){
    return new F(function(){return _qR/* Control.Monad.Skeleton.$fApplicativeSkeleton_$creturn */(_rf/* s1DI */, _qT/* B1 */);});
  },_rd/* Control.Monad.Skeleton.lvl */);
},
_rg/* $dMonad */ = new T(function(){
  return B(_r6/* Control.Monad.Skeleton.$fMonadSkeleton */(_rh/* Control.Monad.Skeleton.$dApplicative */));
}),
_ri/* liftM */ = function(_rj/* s3mK */, _rk/* s3mL */, _rl/* s3mM */){
  var _rm/* s3mP */ = function(_rn/* s3mN */){
    return new F(function(){return A2(_6T/* GHC.Base.return */,_rj/* s3mK */, new T(function(){
      return B(A1(_rk/* s3mL */,_rn/* s3mN */));
    }));});
  };
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_rj/* s3mK */, _rl/* s3mM */, _rm/* s3mP */);});
},
_ro/* $fFunctorSkeleton_$cfmap */ = function(_qS/* B2 */, _qT/* B1 */){
  return new F(function(){return _ri/* GHC.Base.liftM */(_rg/* Control.Monad.Skeleton.$dMonad */, _qS/* B2 */, _qT/* B1 */);});
},
_rp/* $fFunctorSkeleton_$c<$ */ = function(_rq/* s1El */, _rr/* s1Em */){
  return new F(function(){return _ro/* Control.Monad.Skeleton.$fFunctorSkeleton_$cfmap */(function(_rs/* s1En */){
    return E(_rq/* s1El */);
  }, _rr/* s1Em */);});
},
_rt/* $fFunctorSkeleton */ = new T(function(){
  return new T2(0,_ro/* Control.Monad.Skeleton.$fFunctorSkeleton_$cfmap */,_rp/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */);
}),
_rh/* $dApplicative */ = new T(function(){
  return B(_qW/* Control.Monad.Skeleton.$fApplicativeSkeleton */(_rt/* Control.Monad.Skeleton.$fFunctorSkeleton */));
}),
_ru/* lvl5 */ = function(_qT/* B1 */){
  return new F(function(){return _qR/* Control.Monad.Skeleton.$fApplicativeSkeleton_$creturn */(_rh/* Control.Monad.Skeleton.$dApplicative */, _qT/* B1 */);});
},
_rv/* a2 */ = function(_rw/* s1Ep */){
  return new T2(0,E(new T2(1,_rw/* s1Ep */,_ru/* Control.Monad.Skeleton.lvl5 */)),E(new T1(0,_/* EXTERNAL */)));
},
_rx/* bone */ = function(_qT/* B1 */){
  return new F(function(){return _rv/* Control.Monad.Skeleton.a2 */(_qT/* B1 */);});
},
_ry/* clip_f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.beginPath();})");
}),
_rz/* fill2 */ = "fillStyle",
_rA/* fill_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.fill();})");
}),
_rB/* fill1 */ = function(_rC/* sFOs */, _rD/* sFOt */){
  return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T2(0,function(_rE/* sFOu */, _/* EXTERNAL */){
    var _rF/* sFOw */ = E(_rC/* sFOs */),
    _rG/* sFOB */ = B(_lD/* Core.Render.Internal.$wa */(_rF/* sFOw */.a, _rF/* sFOw */.b, _rF/* sFOw */.c, _rF/* sFOw */.d, _/* EXTERNAL */)),
    _rH/* sFOE */ = E(_rE/* sFOu */),
    _rI/* sFOM */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), _rH/* sFOE */, E(_rz/* Core.Render.Internal.fill2 */), B(_ql/* Core.Render.Internal.$wcolor2JSString */(_rG/* sFOB */))),
    _rJ/* sFOS */ = __app1/* EXTERNAL */(E(_ry/* Core.Render.Internal.clip_f3 */), _rH/* sFOE */),
    _rK/* sFOZ */ = B(A3(E(_rD/* sFOt */).b,_rH/* sFOE */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _rL/* sFP5 */ = __app1/* EXTERNAL */(E(_rA/* Core.Render.Internal.fill_f1 */), _rH/* sFOE */);
    return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */));});
},
_rM/* lvl */ = 50,
_rN/* lvl1 */ = 3,
_rO/* lvl10 */ = function(_rP/* sNuJ */){
  return  -E(_rP/* sNuJ */);
},
_rQ/* lvl9 */ = 0,
_rR/* lvl11 */ = new T4(0,_rQ/* Motion.Bounce.lvl9 */,_rQ/* Motion.Bounce.lvl9 */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_rS/* lvl12 */ = new T2(0,_rQ/* Motion.Bounce.lvl9 */,_rR/* Motion.Bounce.lvl11 */),
_rT/* lvl13 */ = new T2(0,_rS/* Motion.Bounce.lvl12 */,_6/* GHC.Types.[] */),
_rU/* lvl14 */ = new T4(0,_lq/* Motion.Bounce.a */,_lq/* Motion.Bounce.a */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_rV/* lvl15 */ = new T2(0,_lq/* Motion.Bounce.a */,_rU/* Motion.Bounce.lvl14 */),
_rW/* lvl16 */ = new T2(0,_rV/* Motion.Bounce.lvl15 */,_6/* GHC.Types.[] */),
_rX/* lvl2 */ = -30,
_rY/* lvl3 */ = 30,
_rZ/* lvl4 */ = -10,
_s0/* lvl5 */ = 0,
_s1/* lvl6 */ = new T1(0,_lq/* Motion.Bounce.a */),
_s2/* a1 */ = 50,
_s3/* lvl7 */ = new T1(0,_s2/* Motion.Bounce.a1 */),
_s4/* a2 */ = 75,
_s5/* lvl8 */ = new T1(0,_s4/* Motion.Bounce.a2 */),
_s6/* liftA1 */ = function(_s7/* s3h5 */, _s8/* s3h6 */, _s9/* s3h7 */, _/* EXTERNAL */){
  var _sa/* s3h9 */ = B(A1(_s8/* s3h6 */,_/* EXTERNAL */)),
  _sb/* s3hc */ = B(A1(_s9/* s3h7 */,_/* EXTERNAL */));
  return new T(function(){
    return B(A2(_s7/* s3h5 */,_sa/* s3h9 */, _sb/* s3hc */));
  });
},
_sc/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Unable to operate opLift"));
}),
_sd/* $wpoly_fail */ = function(_se/* sb82 */){
  return new F(function(){return err/* EXTERNAL */(_sc/* Core.Ease.lvl */);});
},
_sf/* lvl1 */ = new T(function(){
  return B(_sd/* Core.Ease.$wpoly_fail */(_/* EXTERNAL */));
}),
_sg/* opLift */ = function(_sh/* sb83 */, _si/* sb84 */, _sj/* sb85 */){
  var _sk/* sb86 */ = function(_sl/* sb87 */){
    var _sm/* sbaz */ = function(_/* EXTERNAL */){
      var _sn/* sb89 */ = function(_/* EXTERNAL */, _so/* sb8b */){
        var _sp/* sb8c */ = E(_sj/* sb85 */);
        switch(_sp/* sb8c */._){
          case 0:
            return new T(function(){
              return B(A2(_sh/* sb83 */,_so/* sb8b */, _sp/* sb8c */.a));
            });
          case 1:
            var _sq/* sb8g */ = B(A1(_sp/* sb8c */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb83 */,_so/* sb8b */, _sq/* sb8g */));
            });
          case 2:
            var _sr/* sb8s */ = rMV/* EXTERNAL */(E(E(_sp/* sb8c */.a).c)),
            _ss/* sb8v */ = E(_sr/* sb8s */);
            return (_ss/* sb8v */._==0) ? new T(function(){
              var _st/* sb8z */ = new T(function(){
                return B(A1(_sp/* sb8c */.b,new T(function(){
                  return B(_fB/* Data.Tuple.fst */(_ss/* sb8v */.a));
                })));
              });
              return B(A2(_sh/* sb83 */,_so/* sb8b */, _st/* sb8z */));
            }) : E(_sf/* Core.Ease.lvl1 */);
          default:
            var _su/* sb8L */ = rMV/* EXTERNAL */(E(E(_sp/* sb8c */.a).c)),
            _sv/* sb8O */ = E(_su/* sb8L */);
            if(!_sv/* sb8O */._){
              var _sw/* sb8U */ = B(A2(_sp/* sb8c */.b,E(_sv/* sb8O */.a).a, _/* EXTERNAL */));
              return new T(function(){
                return B(A2(_sh/* sb83 */,_so/* sb8b */, _sw/* sb8U */));
              });
            }else{
              return E(_sf/* Core.Ease.lvl1 */);
            }
        }
      },
      _sx/* sb90 */ = function(_/* EXTERNAL */){
        var _sy/* sb92 */ = E(_sj/* sb85 */);
        switch(_sy/* sb92 */._){
          case 0:
            return E(_sf/* Core.Ease.lvl1 */);
          case 1:
            var _sz/* sb96 */ = B(A1(_sy/* sb92 */.a,_/* EXTERNAL */));
            return E(_sf/* Core.Ease.lvl1 */);
          case 2:
            var _sA/* sb9i */ = rMV/* EXTERNAL */(E(E(_sy/* sb92 */.a).c));
            return (E(_sA/* sb9i */)._==0) ? E(_sf/* Core.Ease.lvl1 */) : E(_sf/* Core.Ease.lvl1 */);
          default:
            var _sB/* sb9z */ = rMV/* EXTERNAL */(E(E(_sy/* sb92 */.a).c)),
            _sC/* sb9C */ = E(_sB/* sb9z */);
            if(!_sC/* sb9C */._){
              var _sD/* sb9I */ = B(A2(_sy/* sb92 */.b,E(_sC/* sb9C */.a).a, _/* EXTERNAL */));
              return E(_sf/* Core.Ease.lvl1 */);
            }else{
              return E(_sf/* Core.Ease.lvl1 */);
            }
        }
      },
      _sE/* sb9O */ = E(_si/* sb84 */);
      switch(_sE/* sb9O */._){
        case 0:
          return new F(function(){return _sn/* sb89 */(_/* EXTERNAL */, _sE/* sb9O */.a);});
          break;
        case 1:
          var _sF/* sb9R */ = B(A1(_sE/* sb9O */.a,_/* EXTERNAL */));
          return new F(function(){return _sn/* sb89 */(_/* EXTERNAL */, _sF/* sb9R */);});
          break;
        case 2:
          var _sG/* sba2 */ = rMV/* EXTERNAL */(E(E(_sE/* sb9O */.a).c)),
          _sH/* sba5 */ = E(_sG/* sba2 */);
          if(!_sH/* sba5 */._){
            var _sI/* sbac */ = new T(function(){
              return B(A1(_sE/* sb9O */.b,new T(function(){
                return E(E(_sH/* sba5 */.a).a);
              })));
            });
            return new F(function(){return _sn/* sb89 */(_/* EXTERNAL */, _sI/* sbac */);});
          }else{
            return new F(function(){return _sx/* sb90 */(_/* EXTERNAL */);});
          }
          break;
        default:
          var _sJ/* sbam */ = rMV/* EXTERNAL */(E(E(_sE/* sb9O */.a).c)),
          _sK/* sbap */ = E(_sJ/* sbam */);
          if(!_sK/* sbap */._){
            var _sL/* sbav */ = B(A2(_sE/* sb9O */.b,E(_sK/* sbap */.a).a, _/* EXTERNAL */));
            return new F(function(){return _sn/* sb89 */(_/* EXTERNAL */, _sL/* sbav */);});
          }else{
            return new F(function(){return _sx/* sb90 */(_/* EXTERNAL */);});
          }
      }
    };
    return new T1(1,_sm/* sbaz */);
  },
  _sM/* sbaA */ = E(_si/* sb84 */);
  switch(_sM/* sbaA */._){
    case 0:
      var _sN/* sbaB */ = _sM/* sbaA */.a,
      _sO/* sbaC */ = E(_sj/* sb85 */);
      switch(_sO/* sbaC */._){
        case 0:
          return new T1(0,new T(function(){
            return B(A2(_sh/* sb83 */,_sN/* sbaB */, _sO/* sbaC */.a));
          }));
        case 1:
          var _sP/* sbaL */ = function(_/* EXTERNAL */){
            var _sQ/* sbaH */ = B(A1(_sO/* sbaC */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb83 */,_sN/* sbaB */, _sQ/* sbaH */));
            });
          };
          return new T1(1,_sP/* sbaL */);
        case 2:
          var _sR/* sbaO */ = new T(function(){
            return B(A1(_sh/* sb83 */,_sN/* sbaB */));
          }),
          _sS/* sbaR */ = function(_sT/* sbaP */){
            return new F(function(){return A1(_sR/* sbaO */,new T(function(){
              return B(A1(_sO/* sbaC */.b,_sT/* sbaP */));
            }));});
          };
          return new T2(2,_sO/* sbaC */.a,_sS/* sbaR */);
        default:
          var _sU/* sbaU */ = new T(function(){
            return B(A1(_sh/* sb83 */,_sN/* sbaB */));
          }),
          _sV/* sbb1 */ = function(_sW/* sbaV */, _/* EXTERNAL */){
            var _sX/* sbaX */ = B(A2(_sO/* sbaC */.b,_sW/* sbaV */, _/* EXTERNAL */));
            return new T(function(){
              return B(A1(_sU/* sbaU */,_sX/* sbaX */));
            });
          };
          return new T2(3,_sO/* sbaC */.a,_sV/* sbb1 */);
      }
      break;
    case 1:
      var _sY/* sbb2 */ = _sM/* sbaA */.a,
      _sZ/* sbb3 */ = E(_sj/* sb85 */);
      switch(_sZ/* sbb3 */._){
        case 0:
          var _t0/* sbba */ = function(_/* EXTERNAL */){
            var _t1/* sbb6 */ = B(A1(_sY/* sbb2 */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb83 */,_t1/* sbb6 */, _sZ/* sbb3 */.a));
            });
          };
          return new T1(1,_t0/* sbba */);
        case 1:
          return new T1(1,function(_/* EXTERNAL */){
            return new F(function(){return _s6/* GHC.Base.liftA1 */(_sh/* sb83 */, _sY/* sbb2 */, _sZ/* sbb3 */.a, _/* EXTERNAL */);});
          });
        case 2:
          var _t2/* sbbm */ = function(_t3/* sbbf */, _/* EXTERNAL */){
            var _t4/* sbbh */ = B(A1(_sY/* sbb2 */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb83 */,_t4/* sbbh */, new T(function(){
                return B(A1(_sZ/* sbb3 */.b,_t3/* sbbf */));
              })));
            });
          };
          return new T2(3,_sZ/* sbb3 */.a,_t2/* sbbm */);
        default:
          var _t5/* sbby */ = function(_t6/* sbbp */, _/* EXTERNAL */){
            var _t7/* sbbr */ = B(A1(_sY/* sbb2 */,_/* EXTERNAL */)),
            _t8/* sbbu */ = B(A2(_sZ/* sbb3 */.b,_t6/* sbbp */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb83 */,_t7/* sbbr */, _t8/* sbbu */));
            });
          };
          return new T2(3,_sZ/* sbb3 */.a,_t5/* sbby */);
      }
      break;
    case 2:
      var _t9/* sbbz */ = _sM/* sbaA */.a,
      _ta/* sbbA */ = _sM/* sbaA */.b,
      _tb/* sbbB */ = E(_sj/* sb85 */);
      switch(_tb/* sbbB */._){
        case 0:
          var _tc/* sbbF */ = function(_td/* sbbD */){
            return new F(function(){return A2(_sh/* sb83 */,new T(function(){
              return B(A1(_ta/* sbbA */,_td/* sbbD */));
            }), _tb/* sbbB */.a);});
          };
          return new T2(2,_t9/* sbbz */,_tc/* sbbF */);
        case 1:
          var _te/* sbbO */ = function(_tf/* sbbH */, _/* EXTERNAL */){
            var _tg/* sbbJ */ = B(A1(_tb/* sbbB */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb83 */,new T(function(){
                return B(A1(_ta/* sbbA */,_tf/* sbbH */));
              }), _tg/* sbbJ */));
            });
          };
          return new T2(3,_t9/* sbbz */,_te/* sbbO */);
        default:
          return new F(function(){return _sk/* sb86 */(_/* EXTERNAL */);});
      }
      break;
    default:
      var _th/* sbbP */ = _sM/* sbaA */.a,
      _ti/* sbbQ */ = _sM/* sbaA */.b,
      _tj/* sbbR */ = E(_sj/* sb85 */);
      switch(_tj/* sbbR */._){
        case 0:
          var _tk/* sbbZ */ = function(_tl/* sbbT */, _/* EXTERNAL */){
            var _tm/* sbbV */ = B(A2(_ti/* sbbQ */,_tl/* sbbT */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb83 */,_tm/* sbbV */, _tj/* sbbR */.a));
            });
          };
          return new T2(3,_th/* sbbP */,_tk/* sbbZ */);
        case 1:
          var _tn/* sbca */ = function(_to/* sbc1 */, _/* EXTERNAL */){
            var _tp/* sbc3 */ = B(A2(_ti/* sbbQ */,_to/* sbc1 */, _/* EXTERNAL */)),
            _tq/* sbc6 */ = B(A1(_tj/* sbbR */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb83 */,_tp/* sbc3 */, _tq/* sbc6 */));
            });
          };
          return new T2(3,_th/* sbbP */,_tn/* sbca */);
        default:
          return new F(function(){return _sk/* sb86 */(_/* EXTERNAL */);});
      }
  }
},
_tr/* plusDouble */ = function(_ts/* s18yY */, _tt/* s18yZ */){
  return E(_ts/* s18yY */)+E(_tt/* s18yZ */);
},
_tu/* Zero */ = 0,
_tv/* sleep1 */ = function(_tw/* sc1c */, _tx/* sc1d */, _ty/* sc1e */){
  var _tz/* sc34 */ = function(_tA/* sc1f */){
    var _tB/* sc1g */ = E(_tA/* sc1f */),
    _tC/* sc1i */ = _tB/* sc1g */.b,
    _tD/* sc1j */ = new T(function(){
      return E(_tB/* sc1g */.a)+E(_tw/* sc1c */)|0;
    }),
    _tE/* sc33 */ = function(_/* EXTERNAL */){
      var _tF/* sc1q */ = nMV/* EXTERNAL */(_ii/* Core.World.Internal.waitUntil2 */),
      _tG/* sc1s */ = _tF/* sc1q */;
      return new T(function(){
        var _tH/* sc31 */ = function(_tI/* sc2R */){
          var _tJ/* sc2V */ = new T(function(){
            return B(A1(_ty/* sc1e */,new T2(0,_7/* GHC.Tuple.() */,E(_tI/* sc2R */).b)));
          });
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_tG/* sc1s */, function(_tK/* sc2X */){
            return E(_tJ/* sc2V */);
          })));
        },
        _tL/* sc1u */ = new T2(0,_tD/* sc1j */,_tG/* sc1s */),
        _tM/* sc2Q */ = function(_tN/* sc1w */){
          var _tO/* sc1x */ = new T(function(){
            var _tP/* sc1y */ = E(_tN/* sc1w */),
            _tQ/* sc1D */ = E(_tP/* sc1y */.c);
            if(!_tQ/* sc1D */._){
              var _tR/* sc1D#result */ = E(new T3(1,1,_tL/* sc1u */,E(_ax/* Data.PQueue.Internals.Nil */)));
            }else{
              var _tS/* sc1E */ = _tQ/* sc1D */.a,
              _tT/* sc1G */ = _tQ/* sc1D */.c,
              _tU/* sc1H */ = E(_tQ/* sc1D */.b),
              _tV/* sc1K */ = E(_tD/* sc1j */),
              _tW/* sc1M */ = E(_tU/* sc1H */.a);
              if(_tV/* sc1K */>=_tW/* sc1M */){
                if(_tV/* sc1K */!=_tW/* sc1M */){
                  var _tX/* sc1R#result */ = new T3(1,_tS/* sc1E */+1|0,_tU/* sc1H */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_tY/* sc1S */, _tZ/* sc1T */){
                    var _u0/* sc20 */ = E(E(_tY/* sc1S */).a),
                    _u1/* sc22 */ = E(E(_tZ/* sc1T */).a);
                    return (_u0/* sc20 */>=_u1/* sc22 */) ? _u0/* sc20 */==_u1/* sc22 */ : true;
                  }, _tL/* sc1u */, _tu/* Data.PQueue.Internals.Zero */, _tT/* sc1G */))));
                }else{
                  var _tX/* sc1R#result */ = new T3(1,_tS/* sc1E */+1|0,_tL/* sc1u */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_u2/* sc2a */, _u3/* sc2b */){
                    var _u4/* sc2i */ = E(E(_u2/* sc2a */).a),
                    _u5/* sc2k */ = E(E(_u3/* sc2b */).a);
                    return (_u4/* sc2i */>=_u5/* sc2k */) ? _u4/* sc2i */==_u5/* sc2k */ : true;
                  }, _tU/* sc1H */, _tu/* Data.PQueue.Internals.Zero */, _tT/* sc1G */))));
                }
                var _u6/* sc1P#result */ = _tX/* sc1R#result */;
              }else{
                var _u6/* sc1P#result */ = new T3(1,_tS/* sc1E */+1|0,_tL/* sc1u */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_u7/* sc2s */, _u8/* sc2t */){
                  var _u9/* sc2A */ = E(E(_u7/* sc2s */).a),
                  _ua/* sc2C */ = E(E(_u8/* sc2t */).a);
                  return (_u9/* sc2A */>=_ua/* sc2C */) ? _u9/* sc2A */==_ua/* sc2C */ : true;
                }, _tU/* sc1H */, _tu/* Data.PQueue.Internals.Zero */, _tT/* sc1G */))));
              }
              var _tR/* sc1D#result */ = _u6/* sc1P#result */;
            }
            return new T4(0,E(_tP/* sc1y */.a),_tP/* sc1y */.b,E(_tR/* sc1D#result */),E(_tP/* sc1y */.d));
          });
          return function(_ub/* sc2M */, _uc/* sc2N */){
            return new F(function(){return A1(_uc/* sc2N */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,_tO/* sc1x */),_ub/* sc2M */));});
          };
        };
        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _tC/* sc1i */, _tM/* sc2Q */, _tC/* sc1i */, _tH/* sc31 */]));
      });
    };
    return new T1(0,_tE/* sc33 */);
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _tx/* sc1d */, _ar/* Core.World.Internal.a */, _tx/* sc1d */, _tz/* sc34 */]);});
},
_ud/* $wa */ = function(_ue/* sNuN */, _uf/* sNuO */, _ug/* sNuP */){
  return function(_/* EXTERNAL */){
    var _uh/* sNuR */ = nMV/* EXTERNAL */(_rW/* Motion.Bounce.lvl16 */),
    _ui/* sNuT */ = _uh/* sNuR */,
    _uj/* sNuV */ = function(_uk/* sNuW */){
      return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _lv/* Motion.Bounce.dur */, _lr/* Motion.Bounce.a4 */, _ui/* sNuT */, _lq/* Motion.Bounce.a */, function(_ul/* sNuX */){
        return E(_uk/* sNuW */);
      });});
    },
    _um/* sNuZ */ = function(_un/* sNv0 */){
      return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _lv/* Motion.Bounce.dur */, _lw/* Motion.Bounce.e */, _ui/* sNuT */, _rY/* Motion.Bounce.lvl3 */, function(_uo/* sNv1 */){
        return E(_un/* sNv0 */);
      });});
    },
    _up/* sNCD */ = function(_/* EXTERNAL */){
      var _uq/* sNv4 */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
      _ur/* sNv6 */ = _uq/* sNv4 */,
      _us/* sNv8 */ = new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_ur/* sNv6 */),
      _ut/* sNCB */ = function(_/* EXTERNAL */){
        var _uu/* sNva */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
        _uv/* sNvc */ = _uu/* sNva */,
        _uw/* sNCz */ = function(_/* EXTERNAL */){
          var _ux/* sNvf */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
          _uy/* sNvh */ = _ux/* sNvf */,
          _uz/* sNvj */ = new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_uy/* sNvh */),
          _uA/* sNCx */ = function(_/* EXTERNAL */){
            var _uB/* sNvl */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
            _uC/* sNvn */ = _uB/* sNvl */,
            _uD/* sNCv */ = function(_/* EXTERNAL */){
              var _uE/* sNvq */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
              _uF/* sNvs */ = _uE/* sNvq */,
              _uG/* sNCt */ = function(_/* EXTERNAL */){
                var _uH/* sNvv */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                _uI/* sNvx */ = _uH/* sNvv */,
                _uJ/* sNCr */ = function(_/* EXTERNAL */){
                  var _uK/* sNvA */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                  _uL/* sNvC */ = _uK/* sNvA */,
                  _uM/* sNvE */ = new T(function(){
                    return B(_jN/* Core.Ease.$wforceTo */(_uL/* sNvC */, _rX/* Motion.Bounce.lvl2 */));
                  }),
                  _uN/* sNCp */ = function(_/* EXTERNAL */){
                    var _uO/* sNvG */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                    _uP/* sNvI */ = _uO/* sNvG */,
                    _uQ/* sNCn */ = function(_/* EXTERNAL */){
                      var _uR/* sNvL */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                      _uS/* sNvN */ = _uR/* sNvL */,
                      _uT/* sNvP */ = new T(function(){
                        return B(_jN/* Core.Ease.$wforceTo */(_uS/* sNvN */, _rN/* Motion.Bounce.lvl1 */));
                      }),
                      _uU/* sNCl */ = function(_/* EXTERNAL */){
                        var _uV/* sNvR */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                        _uW/* sNvT */ = _uV/* sNvR */,
                        _uX/* sNvV */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_uW/* sNvT */, _rN/* Motion.Bounce.lvl1 */));
                        }),
                        _uY/* sNCj */ = function(_/* EXTERNAL */){
                          var _uZ/* sNvX */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                          _v0/* sNvZ */ = _uZ/* sNvX */,
                          _v1/* sNCh */ = function(_/* EXTERNAL */){
                            var _v2/* sNw2 */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                            _v3/* sNw4 */ = _v2/* sNw2 */;
                            return new T(function(){
                              var _v4/* sNw7 */ = function(_v5/* sNwc */){
                                return new F(function(){return _v6/* sNw9 */(E(_v5/* sNwc */).b);});
                              },
                              _v7/* sNw8 */ = function(_v8/* sNwg */){
                                return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_s0/* Motion.Bounce.lvl5 */, E(_v8/* sNwg */).b, _v4/* sNw7 */);});
                              },
                              _v6/* sNw9 */ = function(_v9/* sNwk */){
                                var _va/* sNAZ */ = function(_vb/* sNwl */){
                                  var _vc/* sNwm */ = new T(function(){
                                    var _vd/* sNAS */ = function(_ve/* sNwn */){
                                      var _vf/* sNwo */ = new T(function(){
                                        var _vg/* sNAL */ = function(_vh/* sNwp */){
                                          var _vi/* sNwq */ = new T(function(){
                                            var _vj/* sNAE */ = function(_vk/* sNwr */){
                                              var _vl/* sNws */ = new T(function(){
                                                var _vm/* sNAx */ = function(_vn/* sNwt */){
                                                  var _vo/* sNwu */ = new T(function(){
                                                    var _vp/* sNwv */ = new T(function(){
                                                      return E(E(_vn/* sNwt */).a);
                                                    }),
                                                    _vq/* sNwz */ = new T(function(){
                                                      return B(_jN/* Core.Ease.$wforceTo */(_ur/* sNv6 */, new T(function(){
                                                        return (E(E(_vb/* sNwl */).a)+E(_vp/* sNwv */))*0.7;
                                                      })));
                                                    }),
                                                    _vr/* sNAq */ = function(_vs/* sNwK */){
                                                      var _vt/* sNwL */ = new T(function(){
                                                        var _vu/* sNwM */ = new T(function(){
                                                          return E(E(_vs/* sNwK */).a);
                                                        }),
                                                        _vv/* sNwQ */ = new T(function(){
                                                          return B(_jN/* Core.Ease.$wforceTo */(_uv/* sNvc */, new T(function(){
                                                            return (E(E(_ve/* sNwn */).a)+E(_vu/* sNwM */))*0.7;
                                                          })));
                                                        }),
                                                        _vw/* sNAj */ = function(_vx/* sNx1 */){
                                                          var _vy/* sNx2 */ = new T(function(){
                                                            var _vz/* sNx3 */ = new T(function(){
                                                              return E(E(_vx/* sNx1 */).a);
                                                            }),
                                                            _vA/* sNx7 */ = new T(function(){
                                                              return B(_jN/* Core.Ease.$wforceTo */(_uy/* sNvh */, new T(function(){
                                                                return (E(E(_vh/* sNwp */).a)+E(_vz/* sNx3 */))*0.7;
                                                              })));
                                                            }),
                                                            _vB/* sNAc */ = function(_vC/* sNxi */){
                                                              var _vD/* sNxj */ = new T(function(){
                                                                var _vE/* sNxk */ = new T(function(){
                                                                  return E(E(_vC/* sNxi */).a);
                                                                }),
                                                                _vF/* sNxo */ = new T(function(){
                                                                  return B(_jN/* Core.Ease.$wforceTo */(_uC/* sNvn */, new T(function(){
                                                                    return (E(E(_vk/* sNwr */).a)+E(_vE/* sNxk */))*0.7;
                                                                  })));
                                                                }),
                                                                _vG/* sNxz */ = function(_vH/* sNxA */){
                                                                  return new F(function(){return A2(_vF/* sNxo */,E(_vH/* sNxA */).b, _v7/* sNw8 */);});
                                                                },
                                                                _vI/* sNxE */ = function(_vJ/* sNxF */){
                                                                  return new F(function(){return A2(_vA/* sNx7 */,E(_vJ/* sNxF */).b, _vG/* sNxz */);});
                                                                },
                                                                _vK/* sNxJ */ = function(_vL/* sNxK */){
                                                                  return new F(function(){return A2(_vv/* sNwQ */,E(_vL/* sNxK */).b, _vI/* sNxE */);});
                                                                },
                                                                _vM/* sNxO */ = function(_vN/* sNxP */){
                                                                  return new F(function(){return A2(_vq/* sNwz */,E(_vN/* sNxP */).b, _vK/* sNxJ */);});
                                                                },
                                                                _vO/* sNA5 */ = function(_vP/* sNxT */){
                                                                  var _vQ/* sNxU */ = new T(function(){
                                                                    var _vR/* sNxV */ = new T(function(){
                                                                      return E(E(_vP/* sNxT */).a);
                                                                    }),
                                                                    _vS/* sNxZ */ = new T(function(){
                                                                      return B(_jN/* Core.Ease.$wforceTo */(_uS/* sNvN */, new T(function(){
                                                                        return E(_vR/* sNxV */)*0.7;
                                                                      })));
                                                                    }),
                                                                    _vT/* sNy4 */ = new T(function(){
                                                                      return B(_jN/* Core.Ease.$wforceTo */(_uF/* sNvs */, new T(function(){
                                                                        return (E(_vp/* sNwv */)+E(_vR/* sNxV */))*0.7;
                                                                      })));
                                                                    }),
                                                                    _vU/* sNzY */ = function(_vV/* sNyc */){
                                                                      var _vW/* sNyd */ = new T(function(){
                                                                        var _vX/* sNye */ = new T(function(){
                                                                          return E(E(_vV/* sNyc */).a);
                                                                        }),
                                                                        _vY/* sNyi */ = new T(function(){
                                                                          return B(_jN/* Core.Ease.$wforceTo */(_uW/* sNvT */, new T(function(){
                                                                            return E(_vX/* sNye */)*0.7;
                                                                          })));
                                                                        }),
                                                                        _vZ/* sNyn */ = new T(function(){
                                                                          return B(_jN/* Core.Ease.$wforceTo */(_uI/* sNvx */, new T(function(){
                                                                            return (E(_vu/* sNwM */)+E(_vX/* sNye */))*0.7;
                                                                          })));
                                                                        }),
                                                                        _w0/* sNzR */ = function(_w1/* sNyv */){
                                                                          var _w2/* sNyw */ = new T(function(){
                                                                            var _w3/* sNyx */ = new T(function(){
                                                                              return E(E(_w1/* sNyv */).a);
                                                                            }),
                                                                            _w4/* sNyB */ = new T(function(){
                                                                              return B(_jN/* Core.Ease.$wforceTo */(_v0/* sNvZ */, new T(function(){
                                                                                return E(_w3/* sNyx */)*0.7;
                                                                              })));
                                                                            }),
                                                                            _w5/* sNyG */ = new T(function(){
                                                                              return B(_jN/* Core.Ease.$wforceTo */(_uL/* sNvC */, new T(function(){
                                                                                return (E(_vz/* sNx3 */)+E(_w3/* sNyx */))*0.7;
                                                                              })));
                                                                            }),
                                                                            _w6/* sNzK */ = function(_w7/* sNyO */){
                                                                              var _w8/* sNyP */ = new T(function(){
                                                                                var _w9/* sNyQ */ = new T(function(){
                                                                                  return E(E(_w7/* sNyO */).a);
                                                                                }),
                                                                                _wa/* sNyU */ = new T(function(){
                                                                                  return B(_jN/* Core.Ease.$wforceTo */(_v3/* sNw4 */, new T(function(){
                                                                                    return E(_w9/* sNyQ */)*0.7;
                                                                                  })));
                                                                                }),
                                                                                _wb/* sNyZ */ = new T(function(){
                                                                                  return B(_jN/* Core.Ease.$wforceTo */(_uP/* sNvI */, new T(function(){
                                                                                    return (E(_vE/* sNxk */)+E(_w9/* sNyQ */))*0.7;
                                                                                  })));
                                                                                }),
                                                                                _wc/* sNz7 */ = function(_wd/* sNz8 */){
                                                                                  return new F(function(){return A2(_wb/* sNyZ */,E(_wd/* sNz8 */).b, _vM/* sNxO */);});
                                                                                },
                                                                                _we/* sNzc */ = function(_wf/* sNzd */){
                                                                                  return new F(function(){return A2(_w5/* sNyG */,E(_wf/* sNzd */).b, _wc/* sNz7 */);});
                                                                                },
                                                                                _wg/* sNzh */ = function(_wh/* sNzi */){
                                                                                  return new F(function(){return A2(_vZ/* sNyn */,E(_wh/* sNzi */).b, _we/* sNzc */);});
                                                                                },
                                                                                _wi/* sNzm */ = function(_wj/* sNzn */){
                                                                                  return new F(function(){return A2(_vT/* sNy4 */,E(_wj/* sNzn */).b, _wg/* sNzh */);});
                                                                                },
                                                                                _wk/* sNzr */ = function(_wl/* sNzs */){
                                                                                  return new F(function(){return A2(_wa/* sNyU */,E(_wl/* sNzs */).b, _wi/* sNzm */);});
                                                                                },
                                                                                _wm/* sNzw */ = function(_wn/* sNzx */){
                                                                                  return new F(function(){return A2(_w4/* sNyB */,E(_wn/* sNzx */).b, _wk/* sNzr */);});
                                                                                };
                                                                                return B(A2(_vS/* sNxZ */,_v9/* sNwk */, function(_wo/* sNzB */){
                                                                                  return new F(function(){return A2(_vY/* sNyi */,E(_wo/* sNzB */).b, _wm/* sNzw */);});
                                                                                }));
                                                                              });
                                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_v3/* sNw4 */, _w7/* sNyO */, function(_wp/* sNzG */){
                                                                                return E(_w8/* sNyP */);
                                                                              })));
                                                                            };
                                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_v3/* sNw4 */, _w6/* sNzK */)));
                                                                          });
                                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_v0/* sNvZ */, _w1/* sNyv */, function(_wq/* sNzN */){
                                                                            return E(_w2/* sNyw */);
                                                                          })));
                                                                        };
                                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_v0/* sNvZ */, _w0/* sNzR */)));
                                                                      });
                                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uW/* sNvT */, _vV/* sNyc */, function(_wr/* sNzU */){
                                                                        return E(_vW/* sNyd */);
                                                                      })));
                                                                    };
                                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uW/* sNvT */, _vU/* sNzY */)));
                                                                  });
                                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uS/* sNvN */, _vP/* sNxT */, function(_ws/* sNA1 */){
                                                                    return E(_vQ/* sNxU */);
                                                                  })));
                                                                };
                                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uS/* sNvN */, _vO/* sNA5 */)));
                                                              });
                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uP/* sNvI */, _vC/* sNxi */, function(_wt/* sNA8 */){
                                                                return E(_vD/* sNxj */);
                                                              })));
                                                            };
                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uP/* sNvI */, _vB/* sNAc */)));
                                                          });
                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uL/* sNvC */, _vx/* sNx1 */, function(_wu/* sNAf */){
                                                            return E(_vy/* sNx2 */);
                                                          })));
                                                        };
                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uL/* sNvC */, _vw/* sNAj */)));
                                                      });
                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uI/* sNvx */, _vs/* sNwK */, function(_wv/* sNAm */){
                                                        return E(_vt/* sNwL */);
                                                      })));
                                                    };
                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uI/* sNvx */, _vr/* sNAq */)));
                                                  });
                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uF/* sNvs */, _vn/* sNwt */, function(_ww/* sNAt */){
                                                    return E(_vo/* sNwu */);
                                                  })));
                                                };
                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uF/* sNvs */, _vm/* sNAx */)));
                                              });
                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uC/* sNvn */, _vk/* sNwr */, function(_wx/* sNAA */){
                                                return E(_vl/* sNws */);
                                              })));
                                            };
                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uC/* sNvn */, _vj/* sNAE */)));
                                          });
                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uy/* sNvh */, _vh/* sNwp */, function(_wy/* sNAH */){
                                            return E(_vi/* sNwq */);
                                          })));
                                        };
                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uy/* sNvh */, _vg/* sNAL */)));
                                      });
                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uv/* sNvc */, _ve/* sNwn */, function(_wz/* sNAO */){
                                        return E(_vf/* sNwo */);
                                      })));
                                    };
                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uv/* sNvc */, _vd/* sNAS */)));
                                  });
                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_ur/* sNv6 */, _vb/* sNwl */, function(_wA/* sNAV */){
                                    return E(_vc/* sNwm */);
                                  })));
                                };
                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_ur/* sNv6 */, _va/* sNAZ */)));
                              },
                              _wB/* sNB2 */ = new T(function(){
                                return B(_jN/* Core.Ease.$wforceTo */(_v3/* sNw4 */, _rZ/* Motion.Bounce.lvl4 */));
                              }),
                              _wC/* sNB4 */ = function(_wD/* sNBe */){
                                return new F(function(){return _wE/* sNBb */(E(_wD/* sNBe */).b);});
                              },
                              _wF/* sNB5 */ = function(_wG/* sNBi */){
                                return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_rM/* Motion.Bounce.lvl */, E(_wG/* sNBi */).b, _wC/* sNB4 */);});
                              },
                              _wH/* sNB6 */ = function(_wI/* sNBm */){
                                return new F(function(){return A2(_uX/* sNvV */,E(_wI/* sNBm */).b, _wF/* sNB5 */);});
                              },
                              _wJ/* sNB7 */ = function(_wK/* sNBq */){
                                return new F(function(){return A2(_uT/* sNvP */,E(_wK/* sNBq */).b, _wH/* sNB6 */);});
                              },
                              _wL/* sNB8 */ = function(_wM/* sNBu */){
                                return new F(function(){return A2(_uM/* sNvE */,E(_wM/* sNBu */).b, _wJ/* sNB7 */);});
                              },
                              _wN/* sNB9 */ = function(_wO/* sNBy */){
                                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_uj/* sNuV */, E(_wO/* sNBy */).b, _wL/* sNB8 */)));
                              },
                              _wP/* sNBa */ = function(_wQ/* sNBE */){
                                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_um/* sNuZ */, E(_wQ/* sNBE */).b, _wN/* sNB9 */)));
                              },
                              _wE/* sNBb */ = function(_wR/* sNBK */){
                                return new F(function(){return A2(_wB/* sNB2 */,_wR/* sNBK */, _wP/* sNBa */);});
                              },
                              _wS/* sNCd */ = function(_wT/* sNC7 */, _wU/* sNC8 */){
                                return new T1(1,new T2(1,new T(function(){
                                  return B(_wE/* sNBb */(_wT/* sNC7 */));
                                }),new T2(1,new T(function(){
                                  return B(_v6/* sNw9 */(_wT/* sNC7 */));
                                }),_6/* GHC.Types.[] */)));
                              },
                              _wV/* sNC6 */ = new T(function(){
                                var _wW/* sNC5 */ = new T(function(){
                                  var _wX/* sNC1 */ = B(_kB/* Core.Shape.Internal.$wrect */(new T(function(){
                                    return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _s5/* Motion.Bounce.lvl8 */, new T2(2,_us/* sNv8 */,_rO/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, new T2(2,new T3(0,_lv/* Motion.Bounce.dur */,_lw/* Motion.Bounce.e */,_ui/* sNuT */),_2E/* GHC.Base.id */), new T2(2,_uz/* sNvj */,_rO/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _s3/* Motion.Bounce.lvl7 */, new T2(2,_us/* sNv8 */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_uv/* sNvc */),_2E/* GHC.Base.id */)));
                                  }), new T(function(){
                                    return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _s1/* Motion.Bounce.lvl6 */, new T2(2,_uz/* sNvj */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_uC/* sNvn */),_2E/* GHC.Base.id */)));
                                  })));
                                  return new T3(0,_wX/* sNC1 */.a,_wX/* sNC1 */.b,_wX/* sNC1 */.c);
                                });
                                return B(_rB/* Core.Render.Internal.fill1 */(_ue/* sNuN */, _wW/* sNC5 */));
                              });
                              return B(A1(_ug/* sNuP */,new T2(0,new T2(0,_wV/* sNC6 */,_wS/* sNCd */),_uf/* sNuO */)));
                            });
                          };
                          return new T1(0,_v1/* sNCh */);
                        };
                        return new T1(0,_uY/* sNCj */);
                      };
                      return new T1(0,_uU/* sNCl */);
                    };
                    return new T1(0,_uQ/* sNCn */);
                  };
                  return new T1(0,_uN/* sNCp */);
                };
                return new T1(0,_uJ/* sNCr */);
              };
              return new T1(0,_uG/* sNCt */);
            };
            return new T1(0,_uD/* sNCv */);
          };
          return new T1(0,_uA/* sNCx */);
        };
        return new T1(0,_uw/* sNCz */);
      };
      return new T1(0,_ut/* sNCB */);
    };
    return new T1(0,_up/* sNCD */);
  };
},
_wY/* bounceMot1 */ = function(_wZ/* sNCG */, _x0/* sNCH */, _x1/* sNCI */){
  return new T1(0,B(_ud/* Motion.Bounce.$wa */(_wZ/* sNCG */, _x0/* sNCH */, _x1/* sNCI */)));
},
_x2/* clip_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.restore();})");
}),
_x3/* clip5 */ = function(_x4/* sFxK */, _/* EXTERNAL */){
  var _x5/* sFxR */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), E(_x4/* sFxK */));
  return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_x6/* clip4 */ = new T2(0,_x3/* Core.Render.Internal.clip5 */,_7/* GHC.Tuple.() */),
_x7/* clip3 */ = new T(function(){
  return B(_rx/* Control.Monad.Skeleton.bone */(_x6/* Core.Render.Internal.clip4 */));
}),
_x8/* clip2 */ = function(_x9/* sFxU */){
  return E(_x7/* Core.Render.Internal.clip3 */);
},
_xa/* clip1 */ = new T1(1,_x8/* Core.Render.Internal.clip2 */),
_xb/* clip_f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.save();})");
}),
_xc/* getImage2 */ = function(_xd/* sFgr */, _xe/* sFgs */, _/* EXTERNAL */){
  var _xf/* sFgu */ = E(_xd/* sFgr */);
  switch(_xf/* sFgu */._){
    case 0:
      return new F(function(){return A2(_xe/* sFgs */,_xf/* sFgu */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _xg/* sFgx */ = B(A1(_xf/* sFgu */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_xe/* sFgs */,_xg/* sFgx */, _/* EXTERNAL */);});
      break;
    case 2:
      var _xh/* sFgI */ = rMV/* EXTERNAL */(E(E(_xf/* sFgu */.a).c)),
      _xi/* sFgL */ = E(_xh/* sFgI */);
      if(!_xi/* sFgL */._){
        var _xj/* sFgP */ = new T(function(){
          return B(A1(_xf/* sFgu */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_xi/* sFgL */.a));
          })));
        });
        return new F(function(){return A2(_xe/* sFgs */,_xj/* sFgP */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _xk/* sFgZ */ = rMV/* EXTERNAL */(E(E(_xf/* sFgu */.a).c)),
      _xl/* sFh2 */ = E(_xk/* sFgZ */);
      if(!_xl/* sFh2 */._){
        var _xm/* sFh8 */ = B(A2(_xf/* sFgu */.b,E(_xl/* sFh2 */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_xe/* sFgs */,_xm/* sFh8 */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
  }
},
_xn/* lvl10 */ = "shadowBlur",
_xo/* lvl7 */ = "shadowColor",
_xp/* lvl8 */ = "shadowOffsetX",
_xq/* lvl9 */ = "shadowOffsetY",
_xr/* $wshadowed */ = function(_xs/* sFQ9 */, _xt/* sFQa */, _xu/* sFQb */, _xv/* sFQc */, _xw/* sFQd */){
  var _xx/* sFRu */ = function(_xy/* sFQe */, _/* EXTERNAL */){
    var _xz/* sFRt */ = function(_xA/* sFQg */, _/* EXTERNAL */){
      var _xB/* sFRs */ = function(_xC/* sFQi */, _/* EXTERNAL */){
        return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_xu/* sFQb */, function(_xD/* sFQk */, _/* EXTERNAL */){
          var _xE/* sFQm */ = E(_xv/* sFQc */),
          _xF/* sFQr */ = B(_lD/* Core.Render.Internal.$wa */(_xE/* sFQm */.a, _xE/* sFQm */.b, _xE/* sFQm */.c, _xE/* sFQm */.d, _/* EXTERNAL */)),
          _xG/* sFQu */ = E(_xy/* sFQe */),
          _xH/* sFQz */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _xG/* sFQu */),
          _xI/* sFQF */ = E(_ic/* Haste.DOM.Core.jsSet_f1 */),
          _xJ/* sFQI */ = __app3/* EXTERNAL */(_xI/* sFQF */, _xG/* sFQu */, E(_xo/* Core.Render.Internal.lvl7 */), B(_ql/* Core.Render.Internal.$wcolor2JSString */(_xF/* sFQr */))),
          _xK/* sFQQ */ = String/* EXTERNAL */(E(_xA/* sFQg */)),
          _xL/* sFQU */ = __app3/* EXTERNAL */(_xI/* sFQF */, _xG/* sFQu */, E(_xp/* Core.Render.Internal.lvl8 */), _xK/* sFQQ */),
          _xM/* sFR2 */ = String/* EXTERNAL */(E(_xC/* sFQi */)),
          _xN/* sFR6 */ = __app3/* EXTERNAL */(_xI/* sFQF */, _xG/* sFQu */, E(_xq/* Core.Render.Internal.lvl9 */), _xM/* sFR2 */),
          _xO/* sFRe */ = String/* EXTERNAL */(E(_xD/* sFQk */)),
          _xP/* sFRi */ = __app3/* EXTERNAL */(_xI/* sFQF */, _xG/* sFQu */, E(_xn/* Core.Render.Internal.lvl10 */), _xO/* sFRe */),
          _xQ/* sFRo */ = __app1/* EXTERNAL */(E(_ry/* Core.Render.Internal.clip_f3 */), _xG/* sFQu */);
          return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _/* EXTERNAL */);});
      };
      return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_xt/* sFQa */, _xB/* sFRs */, _/* EXTERNAL */);});
    };
    return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_xs/* sFQ9 */, _xz/* sFRt */, _/* EXTERNAL */);});
  },
  _xR/* sFRw */ = B(_rx/* Control.Monad.Skeleton.bone */(new T2(0,_xx/* sFRu */,_7/* GHC.Tuple.() */)));
  return new T2(0,E(_xR/* sFRw */.a),E(new T2(2,new T2(2,_xR/* sFRw */.b,new T1(1,function(_xS/* sFRz */){
    return E(_xw/* sFQd */);
  })),_xa/* Core.Render.Internal.clip1 */)));
},
_xT/* $fAffineShape_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,_){ctx.restore();})");
}),
_xU/* $fApplicativeShape4 */ = function(_/* EXTERNAL */){
  return _av/* GHC.Types.False */;
},
_xV/* $fApplicativeShape3 */ = function(_xW/* stcF */, _/* EXTERNAL */){
  return new F(function(){return _xU/* Core.Shape.Internal.$fApplicativeShape4 */(_/* EXTERNAL */);});
},
_xX/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,_){ctx.save();})");
}),
_xY/* f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.scale(x,y);})");
}),
_xZ/* f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(str,x,y,ctx,_){ctx.strokeText(str,x,y);})");
}),
_y0/* f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(str,x,y,ctx,_){ctx.fillText(str,x,y);})");
}),
_y1/* f5 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.translate(x,y);})");
}),
_y2/* lvl */ = "alphabetic",
_y3/* lvl1 */ = "middle",
_y4/* lvl2 */ = "hanging",
_y5/* lvl3 */ = "right",
_y6/* lvl4 */ = "center",
_y7/* lvl5 */ = "left",
_y8/* lvl6 */ = "(function(fn,a,b,ctx){ctx.font=\"10px \"+fn;ctx.textAlign=a;ctx.textBaseline=b;})",
_y9/* $wtext */ = function(_ya/* stTi */, _yb/* stTj */, _yc/* stTk */, _yd/* stTl */, _ye/* stTm */, _yf/* stTn */, _yg/* stTo */){
  var _yh/* stVw */ = function(_yi/* stTp */, _yj/* stTq */, _yk/* stTr */, _/* EXTERNAL */){
    var _yl/* stVv */ = function(_ym/* stTt */, _yn/* stTu */, _yo/* stTv */, _/* EXTERNAL */){
      var _yp/* stVu */ = function(_yq/* stTx */, _yr/* stTy */, _ys/* stTz */, _/* EXTERNAL */){
        var _yt/* stVt */ = function(_yu/* stTB */, _yv/* stTC */, _yw/* stTD */, _/* EXTERNAL */){
          var _yx/* stTF */ = E(_yv/* stTC */),
          _yy/* stTJ */ = E(_yw/* stTD */),
          _yz/* stTM */ = __app2/* EXTERNAL */(E(_xX/* Core.Shape.Internal.f1 */), _yx/* stTF */, _yy/* stTJ */),
          _yA/* stTR */ = function(_yB/* stTS */){
            var _yC/* stTT */ = function(_yD/* stTU */){
              var _yE/* stTY */ = eval/* EXTERNAL */(E(_y8/* Core.Shape.Internal.lvl6 */)),
              _yF/* stU6 */ = __app4/* EXTERNAL */(E(_yE/* stTY */), E(_ya/* stTi */), _yB/* stTS */, _yD/* stTU */, _yx/* stTF */),
              _yG/* stUk */ = __app4/* EXTERNAL */(E(_y1/* Core.Shape.Internal.f5 */), E(_ym/* stTt */), E(_yq/* stTx */), _yx/* stTF */, _yy/* stTJ */),
              _yH/* stUp */ = E(_yu/* stTB */)/10,
              _yI/* stUv */ = __app4/* EXTERNAL */(E(_xY/* Core.Shape.Internal.f2 */), _yH/* stUp */, _yH/* stUp */, _yx/* stTF */, _yy/* stTJ */);
              if(!_yy/* stTJ */){
                var _yJ/* stUL */ = __app5/* EXTERNAL */(E(_xZ/* Core.Shape.Internal.f3 */), toJSStr/* EXTERNAL */(E(_yi/* stTp */)), 0, 0, _yx/* stTF */, false),
                _yK/* stUR */ = __app2/* EXTERNAL */(E(_xT/* Core.Shape.Internal.$fAffineShape_f1 */), _yx/* stTF */, false);
                return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }else{
                var _yL/* stV6 */ = __app5/* EXTERNAL */(E(_y0/* Core.Shape.Internal.f4 */), toJSStr/* EXTERNAL */(E(_yi/* stTp */)), 0, 0, _yx/* stTF */, true),
                _yM/* stVc */ = __app2/* EXTERNAL */(E(_xT/* Core.Shape.Internal.$fAffineShape_f1 */), _yx/* stTF */, true);
                return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }
            };
            switch(E(_yd/* stTl */)){
              case 0:
                return new F(function(){return _yC/* stTT */(E(_y4/* Core.Shape.Internal.lvl2 */));});
                break;
              case 1:
                return new F(function(){return _yC/* stTT */(E(_y3/* Core.Shape.Internal.lvl1 */));});
                break;
              default:
                return new F(function(){return _yC/* stTT */(E(_y2/* Core.Shape.Internal.lvl */));});
            }
          };
          switch(E(_yc/* stTk */)){
            case 0:
              return new F(function(){return _yA/* stTR */(E(_y7/* Core.Shape.Internal.lvl5 */));});
              break;
            case 1:
              return new F(function(){return _yA/* stTR */(E(_y6/* Core.Shape.Internal.lvl4 */));});
              break;
            default:
              return new F(function(){return _yA/* stTR */(E(_y5/* Core.Shape.Internal.lvl3 */));});
          }
        };
        return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_yg/* stTo */, _yt/* stVt */, _yr/* stTy */, _ys/* stTz */, _/* EXTERNAL */);});
      };
      return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_yf/* stTn */, _yp/* stVu */, _yn/* stTu */, _yo/* stTv */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_ye/* stTm */, _yl/* stVv */, _yj/* stTq */, _yk/* stTr */, _/* EXTERNAL */);});
  };
  return new T3(0,_xV/* Core.Shape.Internal.$fApplicativeShape3 */,function(_lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_yb/* stTj */, _yh/* stVw */, _lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_yN/* BottomBase */ = 2,
_yO/* Just */ = function(_yP/* B1 */){
  return new T1(1,_yP/* B1 */);
},
_yQ/* LeftAlign */ = 0,
_yR/* TopBase */ = 0,
_yS/* a15 */ = 0,
_yT/* lvl4 */ = new T1(0,_yS/* Motion.Main.a15 */),
_yU/* size */ = 150,
_yV/* sz */ = new T1(0,_yU/* Motion.Main.size */),
_yW/* shape */ = new T(function(){
  var _yX/* s7JG */ = B(_kB/* Core.Shape.Internal.$wrect */(_yT/* Motion.Main.lvl4 */, _yT/* Motion.Main.lvl4 */, _yV/* Motion.Main.sz */, _yV/* Motion.Main.sz */));
  return new T3(0,_yX/* s7JG */.a,_yX/* s7JG */.b,_yX/* s7JG */.c);
}),
_yY/* black1 */ = new T1(0,_f3/* Core.Render.Internal.applyTransform2 */),
_yZ/* white */ = new T4(0,_yY/* Core.Render.Internal.black1 */,_yY/* Core.Render.Internal.black1 */,_yY/* Core.Render.Internal.black1 */,_yY/* Core.Render.Internal.black1 */),
_z0/* a17 */ = new T(function(){
  return B(_rB/* Core.Render.Internal.fill1 */(_yZ/* Core.Render.Internal.white */, _yW/* Motion.Main.shape */));
}),
_z1/* a23 */ = function(_z2/* s7JK */, _z3/* s7JL */){
  return new F(function(){return A1(_z3/* s7JL */,new T2(0,_7/* GHC.Tuple.() */,_z2/* s7JK */));});
},
_z4/* black2 */ = new T1(0,_f2/* Core.Render.Internal.applyTransform1 */),
_z5/* black */ = new T4(0,_z4/* Core.Render.Internal.black2 */,_z4/* Core.Render.Internal.black2 */,_z4/* Core.Render.Internal.black2 */,_yY/* Core.Render.Internal.black1 */),
_z6/* Leave */ = 2,
_z7/* lvl2 */ = function(_z8/* s1156 */){
  switch(E(_z8/* s1156 */)){
    case 0:
      return true;
    case 1:
      return false;
    case 2:
      return false;
    case 3:
      return false;
    case 4:
      return false;
    case 5:
      return false;
    default:
      return false;
  }
},
_z9/* lvl3 */ = function(_za/* s1158 */){
  return (E(_za/* s1158 */)==2) ? true : false;
},
_zb/* lvl4 */ = function(_zc/* s115a */){
  switch(E(_zc/* s115a */)){
    case 5:
      return true;
    case 6:
      return true;
    default:
      return false;
  }
},
_zd/* waitFor */ = function(_ze/* s6dr */, _zf/* s6ds */, _zg/* s6dt */){
  var _zh/* s6du */ = new T(function(){
    return B(_zd/* Core.Util.waitFor */(_ze/* s6dr */, _zf/* s6ds */, _zg/* s6dt */));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_ze/* s6dr */, _zg/* s6dt */, function(_zi/* s6dv */){
    if(!B(A1(_zf/* s6ds */,_zi/* s6dv */))){
      return E(_zh/* s6du */);
    }else{
      return new F(function(){return A2(_6T/* GHC.Base.return */,_ze/* s6dr */, _zi/* s6dv */);});
    }
  });});
},
_zj/* button */ = function(_zk/* s115c */, _zl/* s115d */, _zm/* s115e */, _zn/* s115f */){
  var _zo/* s115g */ = new T(function(){
    var _zp/* s115h */ = new T(function(){
      var _zq/* s115p */ = function(_zr/* s115i */, _zs/* s115j */){
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zn/* s115f */, function(_zt/* s115k */){
          return new F(function(){return A1(_zs/* s115j */,new T2(0,_zt/* s115k */,_zr/* s115i */));});
        })));
      };
      return B(_zd/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _zb/* Core.UI.lvl4 */, _zq/* s115p */));
    }),
    _zu/* s115M */ = function(_zv/* s115q */, _zw/* s115r */){
      var _zx/* s115s */ = new T(function(){
        var _zy/* s115F */ = function(_zz/* s115t */){
          var _zA/* s115u */ = E(_zz/* s115t */),
          _zB/* s115w */ = _zA/* s115u */.b,
          _zC/* s115x */ = E(_zA/* s115u */.a);
          if(_zC/* s115x */==6){
            return new F(function(){return A1(_zw/* s115r */,new T2(0,_z6/* Core.View.Leave */,_zB/* s115w */));});
          }else{
            return new F(function(){return A2(_zm/* s115e */,_zB/* s115w */, function(_zD/* s115y */){
              return new F(function(){return A1(_zw/* s115r */,new T2(0,_zC/* s115x */,E(_zD/* s115y */).b));});
            });});
          }
        };
        return B(A2(_zp/* s115h */,_zv/* s115q */, _zy/* s115F */));
      });
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zn/* s115f */, function(_zE/* s115G */){
        var _zF/* s115H */ = E(_zE/* s115G */);
        if(_zF/* s115H */==3){
          return E(_zx/* s115s */);
        }else{
          return new F(function(){return A1(_zw/* s115r */,new T2(0,_zF/* s115H */,_zv/* s115q */));});
        }
      })));
    };
    return B(_zd/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _z9/* Core.UI.lvl3 */, _zu/* s115M */));
  }),
  _zG/* s115N */ = new T(function(){
    var _zH/* s115V */ = function(_zI/* s115O */, _zJ/* s115P */){
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zn/* s115f */, function(_zK/* s115Q */){
        return new F(function(){return A1(_zJ/* s115P */,new T2(0,_zK/* s115Q */,_zI/* s115O */));});
      })));
    };
    return B(_zd/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _z7/* Core.UI.lvl2 */, _zH/* s115V */));
  }),
  _zL/* s115W */ = function(_zM/* s115X */){
    var _zN/* s115Y */ = new T(function(){
      return B(A1(_zk/* s115c */,_zM/* s115X */));
    }),
    _zO/* s116k */ = function(_zP/* s115Z */){
      var _zQ/* s1160 */ = function(_zR/* s1161 */){
        return new F(function(){return A2(_zL/* s115W */,E(_zR/* s1161 */).b, _zP/* s115Z */);});
      },
      _zS/* s1165 */ = function(_zT/* s1166 */){
        return new F(function(){return A2(_zo/* s115g */,E(_zT/* s1166 */).b, _zQ/* s1160 */);});
      },
      _zU/* s116a */ = function(_zV/* s116b */){
        return new F(function(){return A2(_zl/* s115d */,E(_zV/* s116b */).b, _zS/* s1165 */);});
      };
      return new F(function(){return A1(_zN/* s115Y */,function(_zW/* s116f */){
        return new F(function(){return A2(_zG/* s115N */,E(_zW/* s116f */).b, _zU/* s116a */);});
      });});
    };
    return E(_zO/* s116k */);
  };
  return E(_zL/* s115W */);
},
_zX/* clip_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.clip();})");
}),
_zY/* clip */ = function(_zZ/* sFxV */, _A0/* sFxW */){
  var _A1/* sFys */ = B(_rx/* Control.Monad.Skeleton.bone */(new T2(0,function(_A2/* sFxX */, _/* EXTERNAL */){
    var _A3/* sFxZ */ = E(_A2/* sFxX */),
    _A4/* sFy4 */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _A3/* sFxZ */),
    _A5/* sFya */ = __app1/* EXTERNAL */(E(_ry/* Core.Render.Internal.clip_f3 */), _A3/* sFxZ */),
    _A6/* sFyh */ = B(A3(E(_zZ/* sFxV */).b,_A3/* sFxZ */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _A7/* sFyn */ = __app1/* EXTERNAL */(E(_zX/* Core.Render.Internal.clip_f2 */), _A3/* sFxZ */);
    return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */)));
  return new T2(0,E(_A1/* sFys */.a),E(new T2(2,new T2(2,_A1/* sFys */.b,new T1(1,function(_A8/* sFyv */){
    return E(_A0/* sFxW */);
  })),_xa/* Core.Render.Internal.clip1 */)));
},
_A9/* easeTo2 */ = function(_Aa/* sbio */, _Ab/* sbip */){
  return new F(function(){return A1(_Ab/* sbip */,new T2(0,_7/* GHC.Tuple.() */,_Aa/* sbio */));});
},
_Ac/* easeTo1 */ = function(_Ad/* sbir */, _Ae/* B2 */, _Af/* B1 */){
  return new F(function(){return _A9/* Core.Ease.easeTo2 */(_Ae/* B2 */, _Af/* B1 */);});
},
_Ag/* linear */ = function(_Ae/* B2 */, _Af/* B1 */){
  return new F(function(){return _lA/* Core.Ease.easeIn */(_Ae/* B2 */, _Af/* B1 */);});
},
_Ah/* a20 */ = 0.2,
_Ai/* lvl9 */ = new T1(0,_Ah/* Motion.Main.a20 */),
_Aj/* lvl10 */ = new T4(0,_yT/* Motion.Main.lvl4 */,_yT/* Motion.Main.lvl4 */,_yT/* Motion.Main.lvl4 */,_Ai/* Motion.Main.lvl9 */),
_Ak/* a21 */ = 1,
_Al/* lvl11 */ = new T1(0,_Ak/* Motion.Main.a21 */),
_Am/* lvl12 */ = new T4(0,_Ai/* Motion.Main.lvl9 */,_Ai/* Motion.Main.lvl9 */,_Ai/* Motion.Main.lvl9 */,_Al/* Motion.Main.lvl11 */),
_An/* lvl13 */ = "mplus",
_Ao/* lvl14 */ = 1.2,
_Ap/* lvl15 */ = new T1(0,_Ao/* Motion.Main.lvl14 */),
_Aq/* timesDouble */ = function(_Ar/* s18yK */, _As/* s18yL */){
  return E(_Ar/* s18yK */)*E(_As/* s18yL */);
},
_At/* lvl16 */ = new T(function(){
  return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, _yV/* Motion.Main.sz */, _Ap/* Motion.Main.lvl15 */));
}),
_Au/* lvl17 */ = 2,
_Av/* lvl18 */ = new T1(0,_Au/* Motion.Main.lvl17 */),
_Aw/* lvl19 */ = new T(function(){
  return B(_sg/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, _yV/* Motion.Main.sz */, _Av/* Motion.Main.lvl18 */));
}),
_Ax/* lvl2 */ = 6,
_Ay/* lvl20 */ = 0.3,
_Az/* lvl21 */ = new T1(0,_Ay/* Motion.Main.lvl20 */),
_AA/* lvl22 */ = new T(function(){
  return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, _yV/* Motion.Main.sz */, _Az/* Motion.Main.lvl21 */));
}),
_AB/* a22 */ = 0.5,
_AC/* lvl23 */ = new T1(0,_AB/* Motion.Main.a22 */),
_AD/* lvl24 */ = new T4(0,_AC/* Motion.Main.lvl23 */,_AC/* Motion.Main.lvl23 */,_AC/* Motion.Main.lvl23 */,_Al/* Motion.Main.lvl11 */),
_AE/* lvl25 */ = 0.6,
_AF/* lvl26 */ = new T1(0,_AE/* Motion.Main.lvl25 */),
_AG/* lvl27 */ = new T(function(){
  return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, _yV/* Motion.Main.sz */, _AF/* Motion.Main.lvl26 */));
}),
_AH/* lvl3 */ = 10,
_AI/* lvl28 */ = 0.15,
_AJ/* lvl29 */ = new T1(0,_AI/* Motion.Main.lvl28 */),
_AK/* lvl30 */ = new T(function(){
  return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, _yV/* Motion.Main.sz */, _AJ/* Motion.Main.lvl29 */));
}),
_AL/* lvl31 */ = 15,
_AM/* lvl32 */ = function(_AN/* s7JN */){
  var _AO/* s7JO */ = E(_AN/* s7JN */);
  return new T0(2);
},
_AP/* lvl33 */ = new T4(0,_Ax/* Motion.Main.lvl2 */,_Ax/* Motion.Main.lvl2 */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_AQ/* lvl34 */ = new T2(0,_Ax/* Motion.Main.lvl2 */,_AP/* Motion.Main.lvl33 */),
_AR/* lvl35 */ = new T2(0,_AQ/* Motion.Main.lvl34 */,_6/* GHC.Types.[] */),
_AS/* a16 */ = 3,
_AT/* lvl5 */ = new T1(0,_AS/* Motion.Main.a16 */),
_AU/* a18 */ = 0.75,
_AV/* lvl6 */ = new T1(0,_AU/* Motion.Main.a18 */),
_AW/* lvl7 */ = new T2(0,_AV/* Motion.Main.lvl6 */,_AV/* Motion.Main.lvl6 */),
_AX/* a19 */ = 5,
_AY/* lvl8 */ = new T1(0,_AX/* Motion.Main.a19 */),
_AZ/* $fAffineShape1 */ = function(_B0/* stnj */, _B1/* stnk */, _B2/* stnl */, _/* EXTERNAL */){
  var _B3/* stnu */ = __app2/* EXTERNAL */(E(_xT/* Core.Shape.Internal.$fAffineShape_f1 */), E(_B1/* stnk */), E(_B2/* stnl */));
  return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_B4/* $w$caffine */ = function(_B5/* stnx */, _B6/* stny */, _B7/* stnz */, _B8/* stnA */, _B9/* stnB */, _Ba/* stnC */, _Bb/* stnD */){
  var _Bc/* stpn */ = function(_Bd/* stoZ */, _Be/* stp0 */, _Bf/* stp1 */, _/* EXTERNAL */){
    var _Bg/* stpm */ = function(_Bh/* stp3 */, _Bi/* stp4 */, _Bj/* stp5 */, _/* EXTERNAL */){
      var _Bk/* stpl */ = function(_Bl/* stp7 */, _Bm/* stp8 */, _Bn/* stp9 */, _/* EXTERNAL */){
        var _Bo/* stpk */ = function(_Bp/* stpb */, _Bq/* stpc */, _Br/* stpd */, _/* EXTERNAL */){
          return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B9/* stnB */, function(_Bs/* stpf */, _Bt/* stpg */, _Bu/* stph */, _/* EXTERNAL */){
            return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_Ba/* stnC */, _AZ/* Core.Shape.Internal.$fAffineShape1 */, _Bt/* stpg */, _Bu/* stph */, _/* EXTERNAL */);});
          }, _Bq/* stpc */, _Br/* stpd */, _/* EXTERNAL */);});
        };
        return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B8/* stnA */, _Bo/* stpk */, _Bm/* stp8 */, _Bn/* stp9 */, _/* EXTERNAL */);});
      };
      return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B7/* stnz */, _Bk/* stpl */, _Bi/* stp4 */, _Bj/* stp5 */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B6/* stny */, _Bg/* stpm */, _Be/* stp0 */, _Bf/* stp1 */, _/* EXTERNAL */);});
  },
  _Bv/* stoY */ = function(_Bw/* stnE */, _/* EXTERNAL */){
    var _Bx/* stnG */ = E(_Bw/* stnE */),
    _By/* stnH */ = _Bx/* stnG */.a,
    _Bz/* stnI */ = _Bx/* stnG */.b,
    _BA/* stoX */ = function(_BB/* stnJ */, _/* EXTERNAL */){
      var _BC/* stoW */ = function(_BD/* stnL */, _/* EXTERNAL */){
        var _BE/* stoV */ = function(_BF/* stnN */, _/* EXTERNAL */){
          var _BG/* stoU */ = function(_BH/* stnP */, _/* EXTERNAL */){
            var _BI/* stoT */ = function(_BJ/* stnR */, _/* EXTERNAL */){
              var _BK/* stoS */ = function(_BL/* stnT */){
                var _BM/* stnU */ = new T(function(){
                  return E(_BD/* stnL */)*E(_BH/* stnP */)-E(_BB/* stnJ */)*E(_BJ/* stnR */);
                });
                return new F(function(){return A1(_Bb/* stnD */,new T2(0,new T(function(){
                  var _BN/* sto6 */ = E(_BD/* stnL */),
                  _BO/* stoc */ = E(_BJ/* stnR */);
                  return ( -(_BN/* sto6 */*E(_BL/* stnT */))+_BN/* sto6 */*E(_Bz/* stnI */)+_BO/* stoc */*E(_BF/* stnN */)-_BO/* stoc */*E(_By/* stnH */))/E(_BM/* stnU */);
                }),new T(function(){
                  var _BP/* stou */ = E(_BB/* stnJ */),
                  _BQ/* stoA */ = E(_BH/* stnP */);
                  return (_BP/* stou */*E(_BL/* stnT */)-_BP/* stou */*E(_Bz/* stnI */)-_BQ/* stoA */*E(_BF/* stnN */)+_BQ/* stoA */*E(_By/* stnH */))/E(_BM/* stnU */);
                })));});
              };
              return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_Ba/* stnC */, _BK/* stoS */, _/* EXTERNAL */);});
            };
            return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B9/* stnB */, _BI/* stoT */, _/* EXTERNAL */);});
          };
          return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B8/* stnA */, _BG/* stoU */, _/* EXTERNAL */);});
        };
        return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B7/* stnz */, _BE/* stoV */, _/* EXTERNAL */);});
      };
      return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B6/* stny */, _BC/* stoW */, _/* EXTERNAL */);});
    };
    return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B5/* stnx */, _BA/* stoX */, _/* EXTERNAL */);});
  };
  return new T3(0,_Bv/* stoY */,function(_lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B5/* stnx */, _Bc/* stpn */, _lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_BR/* $winsert */ = function(_BS/* s3sqy */, _BT/* s3sqz */, _BU/* s3sqA */){
  var _BV/* s3sqB */ = E(_BT/* s3sqz */),
  _BW/* s3sqC */ = E(_BU/* s3sqA */);
  switch(_BW/* s3sqC */._){
    case 0:
      var _BX/* s3sqD */ = _BW/* s3sqC */.a,
      _BY/* s3sqE */ = _BW/* s3sqC */.b,
      _BZ/* s3sqF */ = _BW/* s3sqC */.c,
      _C0/* s3sqG */ = _BW/* s3sqC */.d,
      _C1/* s3sqH */ = _BY/* s3sqE */>>>0;
      if(((_BS/* s3sqy */>>>0&((_C1/* s3sqH */-1>>>0^4294967295)>>>0^_C1/* s3sqH */)>>>0)>>>0&4294967295)==_BX/* s3sqD */){
        return ((_BS/* s3sqy */>>>0&_C1/* s3sqH */)>>>0==0) ? new T4(0,_BX/* s3sqD */,_BY/* s3sqE */,E(B(_BR/* Data.IntMap.Strict.$winsert */(_BS/* s3sqy */, _BV/* s3sqB */, _BZ/* s3sqF */))),E(_C0/* s3sqG */)) : new T4(0,_BX/* s3sqD */,_BY/* s3sqE */,E(_BZ/* s3sqF */),E(B(_BR/* Data.IntMap.Strict.$winsert */(_BS/* s3sqy */, _BV/* s3sqB */, _C0/* s3sqG */))));
      }else{
        var _C2/* s3sqU */ = (_BS/* s3sqy */>>>0^_BX/* s3sqD */>>>0)>>>0,
        _C3/* s3sqX */ = (_C2/* s3sqU */|_C2/* s3sqU */>>>1)>>>0,
        _C4/* s3sqZ */ = (_C3/* s3sqX */|_C3/* s3sqX */>>>2)>>>0,
        _C5/* s3sr1 */ = (_C4/* s3sqZ */|_C4/* s3sqZ */>>>4)>>>0,
        _C6/* s3sr3 */ = (_C5/* s3sr1 */|_C5/* s3sr1 */>>>8)>>>0,
        _C7/* s3sr5 */ = (_C6/* s3sr3 */|_C6/* s3sr3 */>>>16)>>>0,
        _C8/* s3sr7 */ = (_C7/* s3sr5 */^_C7/* s3sr5 */>>>1)>>>0&4294967295,
        _C9/* s3sra */ = _C8/* s3sr7 */>>>0;
        return ((_BS/* s3sqy */>>>0&_C9/* s3sra */)>>>0==0) ? new T4(0,(_BS/* s3sqy */>>>0&((_C9/* s3sra */-1>>>0^4294967295)>>>0^_C9/* s3sra */)>>>0)>>>0&4294967295,_C8/* s3sr7 */,E(new T2(1,_BS/* s3sqy */,_BV/* s3sqB */)),E(_BW/* s3sqC */)) : new T4(0,(_BS/* s3sqy */>>>0&((_C9/* s3sra */-1>>>0^4294967295)>>>0^_C9/* s3sra */)>>>0)>>>0&4294967295,_C8/* s3sr7 */,E(_BW/* s3sqC */),E(new T2(1,_BS/* s3sqy */,_BV/* s3sqB */)));
      }
      break;
    case 1:
      var _Ca/* s3srr */ = _BW/* s3sqC */.a;
      if(_BS/* s3sqy */!=_Ca/* s3srr */){
        var _Cb/* s3srv */ = (_BS/* s3sqy */>>>0^_Ca/* s3srr */>>>0)>>>0,
        _Cc/* s3sry */ = (_Cb/* s3srv */|_Cb/* s3srv */>>>1)>>>0,
        _Cd/* s3srA */ = (_Cc/* s3sry */|_Cc/* s3sry */>>>2)>>>0,
        _Ce/* s3srC */ = (_Cd/* s3srA */|_Cd/* s3srA */>>>4)>>>0,
        _Cf/* s3srE */ = (_Ce/* s3srC */|_Ce/* s3srC */>>>8)>>>0,
        _Cg/* s3srG */ = (_Cf/* s3srE */|_Cf/* s3srE */>>>16)>>>0,
        _Ch/* s3srI */ = (_Cg/* s3srG */^_Cg/* s3srG */>>>1)>>>0&4294967295,
        _Ci/* s3srL */ = _Ch/* s3srI */>>>0;
        return ((_BS/* s3sqy */>>>0&_Ci/* s3srL */)>>>0==0) ? new T4(0,(_BS/* s3sqy */>>>0&((_Ci/* s3srL */-1>>>0^4294967295)>>>0^_Ci/* s3srL */)>>>0)>>>0&4294967295,_Ch/* s3srI */,E(new T2(1,_BS/* s3sqy */,_BV/* s3sqB */)),E(_BW/* s3sqC */)) : new T4(0,(_BS/* s3sqy */>>>0&((_Ci/* s3srL */-1>>>0^4294967295)>>>0^_Ci/* s3srL */)>>>0)>>>0&4294967295,_Ch/* s3srI */,E(_BW/* s3sqC */),E(new T2(1,_BS/* s3sqy */,_BV/* s3sqB */)));
      }else{
        return new T2(1,_BS/* s3sqy */,_BV/* s3sqB */);
      }
      break;
    default:
      return new T2(1,_BS/* s3sqy */,_BV/* s3sqB */);
  }
},
_Cj/* Cancel */ = 6,
_Ck/* Drag */ = 4,
_Cl/* Enter */ = 0,
_Cm/* Move */ = 1,
_Cn/* Press */ = 3,
_Co/* Release */ = 5,
_Cp/* lvl23 */ = function(_Cq/* sXT6 */, _Cr/* sXT7 */){
  return new F(function(){return A1(_Cr/* sXT7 */,new T2(0,_7/* GHC.Tuple.() */,_Cq/* sXT6 */));});
},
_Cs/* lvl24 */ = new T1(1,_6/* GHC.Types.[] */),
_Ct/* lvl */ = 0,
_Cu/* lvl25 */ = new T4(0,_Ct/* Core.View.lvl */,_Ct/* Core.View.lvl */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_Cv/* lvl26 */ = new T2(0,_Ct/* Core.View.lvl */,_Cu/* Core.View.lvl25 */),
_Cw/* lvl27 */ = new T2(0,_Cv/* Core.View.lvl26 */,_6/* GHC.Types.[] */),
_Cx/* lvl1 */ = 1,
_Cy/* lvl28 */ = new T4(0,_Cx/* Core.View.lvl1 */,_Cx/* Core.View.lvl1 */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_Cz/* lvl29 */ = new T2(0,_Cx/* Core.View.lvl1 */,_Cy/* Core.View.lvl28 */),
_CA/* lvl30 */ = new T2(0,_Cz/* Core.View.lvl29 */,_6/* GHC.Types.[] */),
_CB/* fork */ = function(_CC/* srPv */){
  return E(E(_CC/* srPv */).c);
},
_CD/* lvl */ = new T1(1,_6/* GHC.Types.[] */),
_CE/* spawn1 */ = function(_CF/* sJti */){
  var _CG/* sJtp */ = function(_/* EXTERNAL */){
    var _CH/* sJtk */ = nMV/* EXTERNAL */(_CD/* Haste.Concurrent.lvl */);
    return new T(function(){
      return B(A1(_CF/* sJti */,_CH/* sJtk */));
    });
  };
  return new T1(0,_CG/* sJtp */);
},
_CI/* spawn */ = function(_CJ/* sJtK */, _CK/* sJtL */){
  var _CL/* sJtM */ = new T(function(){
    return B(_CB/* Haste.Concurrent.Monad.fork */(_CJ/* sJtK */));
  }),
  _CM/* sJtN */ = B(_9x/* Haste.Concurrent.Monad.$p1MonadConc */(_CJ/* sJtK */)),
  _CN/* sJtT */ = function(_CO/* sJtP */){
    var _CP/* sJtR */ = new T(function(){
      return B(A1(_CL/* sJtM */,new T(function(){
        return B(A1(_CK/* sJtL */,_CO/* sJtP */));
      })));
    });
    return new F(function(){return A3(_9z/* GHC.Base.>> */,_CM/* sJtN */, _CP/* sJtR */, new T(function(){
      return B(A2(_6T/* GHC.Base.return */,_CM/* sJtN */, _CO/* sJtP */));
    }));});
  };
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_CM/* sJtN */, new T(function(){
    return B(A2(_2V/* Haste.Concurrent.Monad.liftConc */,_CJ/* sJtK */, _CE/* Haste.Concurrent.spawn1 */));
  }), _CN/* sJtT */);});
},
_CQ/* makeView */ = function(_CR/* sXT9 */, _CS/* sXTa */, _CT/* sXTb */, _CU/* sXTc */){
  var _CV/* sXTd */ = new T(function(){
    return B(A1(_CR/* sXT9 */,_z6/* Core.View.Leave */));
  }),
  _CW/* sXTe */ = new T(function(){
    return B(A1(_CR/* sXT9 */,_Cl/* Core.View.Enter */));
  }),
  _CX/* sXTf */ = new T(function(){
    return B(A1(_CR/* sXT9 */,_Ck/* Core.View.Drag */));
  }),
  _CY/* sXTg */ = new T(function(){
    return B(_CI/* Haste.Concurrent.spawn */(_8l/* Core.World.Internal.$fMonadConcWorld */, _CU/* sXTc */));
  }),
  _CZ/* sXTh */ = new T(function(){
    return B(A1(_CR/* sXT9 */,_Cj/* Core.View.Cancel */));
  }),
  _D0/* sXTi */ = new T(function(){
    return B(A1(_CR/* sXT9 */,_Co/* Core.View.Release */));
  }),
  _D1/* sXTj */ = new T(function(){
    return B(A1(_CR/* sXT9 */,_Cn/* Core.View.Press */));
  }),
  _D2/* sXTk */ = new T(function(){
    return B(A1(_CR/* sXT9 */,_Cm/* Core.View.Move */));
  }),
  _D3/* sXYz */ = function(_D4/* sXTl */){
    var _D5/* sXTm */ = new T(function(){
      return B(A1(_CY/* sXTg */,_D4/* sXTl */));
    }),
    _D6/* sXYy */ = function(_D7/* sXTn */){
      var _D8/* sXYx */ = function(_D9/* sXTo */){
        var _Da/* sXTp */ = E(_D9/* sXTo */),
        _Db/* sXTq */ = _Da/* sXTp */.a,
        _Dc/* sXTr */ = _Da/* sXTp */.b,
        _Dd/* sXTs */ = new T(function(){
          var _De/* sXTt */ = E(_CV/* sXTd */);
          if(!_De/* sXTt */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sXTq */, _De/* sXTt */.a));
          }
        }),
        _Df/* sXTv */ = new T(function(){
          var _Dg/* sXTw */ = E(_CW/* sXTe */);
          if(!_Dg/* sXTw */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sXTq */, _Dg/* sXTw */.a));
          }
        }),
        _Dh/* sXTy */ = new T(function(){
          var _Di/* sXTz */ = E(_CX/* sXTf */);
          if(!_Di/* sXTz */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sXTq */, _Di/* sXTz */.a));
          }
        }),
        _Dj/* sXTB */ = new T(function(){
          var _Dk/* sXTC */ = E(_CZ/* sXTh */);
          if(!_Dk/* sXTC */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sXTq */, _Dk/* sXTC */.a));
          }
        }),
        _Dl/* sXTE */ = new T(function(){
          var _Dm/* sXTF */ = E(_D0/* sXTi */);
          if(!_Dm/* sXTF */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sXTq */, _Dm/* sXTF */.a));
          }
        }),
        _Dn/* sXTH */ = new T(function(){
          var _Do/* sXTI */ = E(_D1/* sXTj */);
          if(!_Do/* sXTI */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sXTq */, _Do/* sXTI */.a));
          }
        }),
        _Dp/* sXTK */ = new T(function(){
          var _Dq/* sXTL */ = E(_D2/* sXTk */);
          if(!_Dq/* sXTL */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sXTq */, _Dq/* sXTL */.a));
          }
        }),
        _Dr/* sXYw */ = function(_/* EXTERNAL */){
          var _Ds/* sXTO */ = nMV/* EXTERNAL */(_CA/* Core.View.lvl30 */),
          _Dt/* sXTQ */ = _Ds/* sXTO */,
          _Du/* sXYu */ = function(_/* EXTERNAL */){
            var _Dv/* sXTT */ = nMV/* EXTERNAL */(_Cw/* Core.View.lvl27 */),
            _Dw/* sXTV */ = _Dv/* sXTT */,
            _Dx/* sXYs */ = function(_/* EXTERNAL */){
              var _Dy/* sXTY */ = nMV/* EXTERNAL */(_Cw/* Core.View.lvl27 */),
              _Dz/* sXU0 */ = _Dy/* sXTY */,
              _DA/* sXYq */ = function(_/* EXTERNAL */){
                var _DB/* sXU3 */ = nMV/* EXTERNAL */(_Cw/* Core.View.lvl27 */),
                _DC/* sXU5 */ = _DB/* sXU3 */,
                _DD/* sXYo */ = function(_/* EXTERNAL */){
                  var _DE/* sXU8 */ = nMV/* EXTERNAL */(_CA/* Core.View.lvl30 */),
                  _DF/* sXUa */ = _DE/* sXU8 */,
                  _DG/* sXYm */ = function(_/* EXTERNAL */){
                    var _DH/* sXUd */ = nMV/* EXTERNAL */(_Cw/* Core.View.lvl27 */),
                    _DI/* sXUf */ = _DH/* sXUd */,
                    _DJ/* sXUh */ = new T(function(){
                      var _DK/* sXV4 */ = function(_DL/* sXUi */, _DM/* sXUj */, _DN/* sXUk */, _DO/* sXUl */, _DP/* sXUm */, _DQ/* sXUn */){
                        var _DR/* sXUo */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_Dt/* sXTQ */, _DL/* sXUi */));
                        }),
                        _DS/* sXUp */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_Dw/* sXTV */, _DM/* sXUj */));
                        }),
                        _DT/* sXUq */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_Dz/* sXU0 */, _DN/* sXUk */));
                        }),
                        _DU/* sXUr */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_DC/* sXU5 */, _DO/* sXUl */));
                        }),
                        _DV/* sXUs */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_DF/* sXUa */, _DP/* sXUm */));
                        }),
                        _DW/* sXUt */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_DI/* sXUf */, _DQ/* sXUn */));
                        }),
                        _DX/* sXV3 */ = function(_DY/* sXUu */){
                          var _DZ/* sXUv */ = new T(function(){
                            return B(A1(_DR/* sXUo */,_DY/* sXUu */));
                          }),
                          _E0/* sXV2 */ = function(_E1/* sXUw */){
                            var _E2/* sXUx */ = function(_E3/* sXUy */){
                              return new F(function(){return A1(_E1/* sXUw */,new T2(0,_7/* GHC.Tuple.() */,E(_E3/* sXUy */).b));});
                            },
                            _E4/* sXUD */ = function(_E5/* sXUE */){
                              return new F(function(){return A2(_DW/* sXUt */,E(_E5/* sXUE */).b, _E2/* sXUx */);});
                            },
                            _E6/* sXUI */ = function(_E7/* sXUJ */){
                              return new F(function(){return A2(_DV/* sXUs */,E(_E7/* sXUJ */).b, _E4/* sXUD */);});
                            },
                            _E8/* sXUN */ = function(_E9/* sXUO */){
                              return new F(function(){return A2(_DU/* sXUr */,E(_E9/* sXUO */).b, _E6/* sXUI */);});
                            },
                            _Ea/* sXUS */ = function(_Eb/* sXUT */){
                              return new F(function(){return A2(_DT/* sXUq */,E(_Eb/* sXUT */).b, _E8/* sXUN */);});
                            };
                            return new F(function(){return A1(_DZ/* sXUv */,function(_Ec/* sXUX */){
                              return new F(function(){return A2(_DS/* sXUp */,E(_Ec/* sXUX */).b, _Ea/* sXUS */);});
                            });});
                          };
                          return E(_E0/* sXV2 */);
                        };
                        return E(_DX/* sXV3 */);
                      };
                      return B(_rx/* Control.Monad.Skeleton.bone */(new T2(2,_DK/* sXV4 */,_7/* GHC.Tuple.() */)));
                    }),
                    _Ed/* sXV6 */ = new T(function(){
                      var _Ee/* sXV7 */ = E(_CT/* sXTb */);
                      return new T2(0,E(_Ee/* sXV7 */.a),E(new T2(2,_Ee/* sXV7 */.b,new T1(1,function(_Ef/* sXVa */){
                        return E(_DJ/* sXUh */);
                      }))));
                    }),
                    _Eg/* sXVe */ = new T(function(){
                      var _Eh/* sXVv */ = B(_B4/* Core.Shape.Internal.$w$caffine */(new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_Dt/* sXTQ */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_Dw/* sXTV */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_Dz/* sXU0 */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_DC/* sXU5 */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_DF/* sXUa */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_DI/* sXUf */),_2E/* GHC.Base.id */), E(_CS/* sXTa */).a));
                      return new T3(0,_Eh/* sXVv */.a,_Eh/* sXVv */.b,_Eh/* sXVv */.c);
                    }),
                    _Ei/* sXYk */ = function(_/* EXTERNAL */){
                      var _Ej/* sXVA */ = nMV/* EXTERNAL */(_Cs/* Core.View.lvl24 */),
                      _Ek/* sXVC */ = _Ej/* sXVA */,
                      _El/* sXYg */ = new T(function(){
                        var _Em/* sXWq */ = function(_En/* sXWY */){
                          return new F(function(){return _Eo/* sXWp */(E(_En/* sXWY */).b);});
                        },
                        _Ep/* sXWs */ = function(_Eq/* sXX6 */){
                          var _Er/* sXX7 */ = new T(function(){
                            return B(A2(_Dp/* sXTK */,_Eq/* sXX6 */, _Es/* sXWr */));
                          }),
                          _Et/* sXX8 */ = new T(function(){
                            return B(A2(_Dd/* sXTs */,_Eq/* sXX6 */, _Em/* sXWq */));
                          }),
                          _Eu/* sXX9 */ = new T(function(){
                            return B(A2(_Dn/* sXTH */,_Eq/* sXX6 */, _Ev/* sXWo */));
                          }),
                          _Ew/* sXXa */ = new T(function(){
                            return B(_Ep/* sXWs */(_Eq/* sXX6 */));
                          }),
                          _Ex/* sXXr */ = function(_Ey/* sXXb */){
                            var _Ez/* sXXc */ = E(_Ey/* sXXb */);
                            if(!_Ez/* sXXc */._){
                              return (!E(_Ez/* sXXc */.a)) ? E(_Ew/* sXXa */) : E(_Eu/* sXX9 */);
                            }else{
                              var _EA/* sXXq */ = function(_/* EXTERNAL */){
                                var _EB/* sXXl */ = B(A2(E(_Eg/* sXVe */).a,_Ez/* sXXc */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_EB/* sXXl */)){
                                    return E(_Et/* sXX8 */);
                                  }else{
                                    return E(_Er/* sXX7 */);
                                  }
                                });
                              };
                              return new T1(0,_EA/* sXXq */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ek/* sXVC */, _Ex/* sXXr */)));
                        },
                        _Es/* sXWr */ = function(_EC/* sXX2 */){
                          return new F(function(){return _Ep/* sXWs */(E(_EC/* sXX2 */).b);});
                        },
                        _Eo/* sXWp */ = function(_ED/* sXWD */){
                          var _EE/* sXWE */ = new T(function(){
                            return B(_Eo/* sXWp */(_ED/* sXWD */));
                          }),
                          _EF/* sXWF */ = new T(function(){
                            return B(A2(_Df/* sXTv */,_ED/* sXWD */, _Es/* sXWr */));
                          }),
                          _EG/* sXWV */ = function(_EH/* sXWG */){
                            var _EI/* sXWH */ = E(_EH/* sXWG */);
                            if(!_EI/* sXWH */._){
                              return E(_EE/* sXWE */);
                            }else{
                              var _EJ/* sXWU */ = function(_/* EXTERNAL */){
                                var _EK/* sXWP */ = B(A2(E(_Eg/* sXVe */).a,_EI/* sXWH */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_EK/* sXWP */)){
                                    return E(_EE/* sXWE */);
                                  }else{
                                    return E(_EF/* sXWF */);
                                  }
                                });
                              };
                              return new T1(0,_EJ/* sXWU */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ek/* sXVC */, _EG/* sXWV */)));
                        },
                        _EL/* sXWt */ = function(_EM/* sXXu */){
                          var _EN/* sXXv */ = new T(function(){
                            return B(A2(_Dh/* sXTy */,_EM/* sXXu */, _Ev/* sXWo */));
                          }),
                          _EO/* sXXw */ = new T(function(){
                            return B(A2(_Dd/* sXTs */,_EM/* sXXu */, _EP/* sXWn */));
                          }),
                          _EQ/* sXXx */ = new T(function(){
                            return B(_EL/* sXWt */(_EM/* sXXu */));
                          }),
                          _ER/* sXXy */ = new T(function(){
                            return B(A2(_Dl/* sXTE */,_EM/* sXXu */, _Es/* sXWr */));
                          }),
                          _ES/* sXXP */ = function(_ET/* sXXz */){
                            var _EU/* sXXA */ = E(_ET/* sXXz */);
                            if(!_EU/* sXXA */._){
                              return (!E(_EU/* sXXA */.a)) ? E(_ER/* sXXy */) : E(_EQ/* sXXx */);
                            }else{
                              var _EV/* sXXO */ = function(_/* EXTERNAL */){
                                var _EW/* sXXJ */ = B(A2(E(_Eg/* sXVe */).a,_EU/* sXXA */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_EW/* sXXJ */)){
                                    return E(_EO/* sXXw */);
                                  }else{
                                    return E(_EN/* sXXv */);
                                  }
                                });
                              };
                              return new T1(0,_EV/* sXXO */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ek/* sXVC */, _ES/* sXXP */)));
                        },
                        _Ev/* sXWo */ = function(_EX/* sXWz */){
                          return new F(function(){return _EL/* sXWt */(E(_EX/* sXWz */).b);});
                        },
                        _EY/* sXWu */ = function(_EZ/* sXXS */){
                          var _F0/* sXXT */ = new T(function(){
                            return B(A2(_Df/* sXTv */,_EZ/* sXXS */, _Ev/* sXWo */));
                          }),
                          _F1/* sXXU */ = new T(function(){
                            return B(A2(_Dh/* sXTy */,_EZ/* sXXS */, _EP/* sXWn */));
                          }),
                          _F2/* sXXV */ = new T(function(){
                            return B(_EY/* sXWu */(_EZ/* sXXS */));
                          }),
                          _F3/* sXXW */ = new T(function(){
                            return B(A2(_Dj/* sXTB */,_EZ/* sXXS */, _Em/* sXWq */));
                          }),
                          _F4/* sXYd */ = function(_F5/* sXXX */){
                            var _F6/* sXXY */ = E(_F5/* sXXX */);
                            if(!_F6/* sXXY */._){
                              return (!E(_F6/* sXXY */.a)) ? E(_F3/* sXXW */) : E(_F2/* sXXV */);
                            }else{
                              var _F7/* sXYc */ = function(_/* EXTERNAL */){
                                var _F8/* sXY7 */ = B(A2(E(_Eg/* sXVe */).a,_F6/* sXXY */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_F8/* sXY7 */)){
                                    return E(_F1/* sXXU */);
                                  }else{
                                    return E(_F0/* sXXT */);
                                  }
                                });
                              };
                              return new T1(0,_F7/* sXYc */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ek/* sXVC */, _F4/* sXYd */)));
                        },
                        _EP/* sXWn */ = function(_F9/* sXWv */){
                          return new F(function(){return _EY/* sXWu */(E(_F9/* sXWv */).b);});
                        };
                        return B(_Eo/* sXWp */(_Dc/* sXTr */));
                      }),
                      _Fa/* sXWm */ = new T(function(){
                        var _Fb/* sXWl */ = function(_Fc/* sXWb */){
                          var _Fd/* sXWc */ = E(_Fc/* sXWb */);
                          return new F(function(){return A1(_D7/* sXTn */,new T2(0,new T(function(){
                            return new T3(0,E(_Fd/* sXWc */.a),_Ed/* sXV6 */,E(_Db/* sXTq */));
                          }),_Fd/* sXWc */.b));});
                        },
                        _Fe/* sXWa */ = function(_Ff/* sXVE */, _Fg/* sXVF */, _Fh/* sXVG */){
                          var _Fi/* sXVH */ = new T(function(){
                            return E(E(_Ff/* sXVE */).d);
                          }),
                          _Fj/* sXVN */ = new T(function(){
                            return E(E(_Fi/* sXVH */).a);
                          }),
                          _Fk/* sXW7 */ = new T(function(){
                            var _Fl/* sXVR */ = E(_Ff/* sXVE */);
                            return new T4(0,E(_Fl/* sXVR */.a),_Fl/* sXVR */.b,E(_Fl/* sXVR */.c),E(new T2(0,new T(function(){
                              return E(_Fj/* sXVN */)+1|0;
                            }),new T(function(){
                              return B(_BR/* Data.IntMap.Strict.$winsert */(E(_Fj/* sXVN */), _Ek/* sXVC */, E(_Fi/* sXVH */).b));
                            }))));
                          });
                          return new F(function(){return A1(_Fh/* sXVG */,new T2(0,new T2(0,_Fj/* sXVN */,_Fk/* sXW7 */),_Fg/* sXVF */));});
                        };
                        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _Dc/* sXTr */, _Fe/* sXWa */, _Dc/* sXTr */, _Fb/* sXWl */]));
                      });
                      return new T1(1,new T2(1,_Fa/* sXWm */,new T2(1,_El/* sXYg */,_6/* GHC.Types.[] */)));
                    };
                    return new T1(0,_Ei/* sXYk */);
                  };
                  return new T1(0,_DG/* sXYm */);
                };
                return new T1(0,_DD/* sXYo */);
              };
              return new T1(0,_DA/* sXYq */);
            };
            return new T1(0,_Dx/* sXYs */);
          };
          return new T1(0,_Du/* sXYu */);
        };
        return new T1(0,_Dr/* sXYw */);
      };
      return new F(function(){return A1(_D5/* sXTm */,_D8/* sXYx */);});
    };
    return E(_D6/* sXYy */);
  };
  return E(_D3/* sXYz */);
},
_Fm/* consView */ = function(_Fn/* s7JR */, _Fo/* s7JS */, _Fp/* s7JT */, _Fq/* s7JU */){
  var _Fr/* s7JV */ = new T(function(){
    var _Fs/* s7Kg */ = new T(function(){
      var _Ft/* s7K2 */ = B(_rB/* Core.Render.Internal.fill1 */(_Am/* Motion.Main.lvl12 */, new T(function(){
        var _Fu/* s7JX */ = B(_y9/* Core.Shape.Internal.$wtext */(_An/* Motion.Main.lvl13 */, new T1(0,_Fp/* s7JT */), _yQ/* Core.Shape.Internal.LeftAlign */, _yN/* Core.Shape.Internal.BottomBase */, _At/* Motion.Main.lvl16 */, _Aw/* Motion.Main.lvl19 */, _AA/* Motion.Main.lvl22 */));
        return new T3(0,_Fu/* s7JX */.a,_Fu/* s7JX */.b,_Fu/* s7JX */.c);
      }))),
      _Fv/* s7K5 */ = new T(function(){
        return B(_rB/* Core.Render.Internal.fill1 */(_AD/* Motion.Main.lvl24 */, new T(function(){
          var _Fw/* s7K7 */ = B(_y9/* Core.Shape.Internal.$wtext */(_An/* Motion.Main.lvl13 */, new T1(0,_Fq/* s7JU */), _yQ/* Core.Shape.Internal.LeftAlign */, _yR/* Core.Shape.Internal.TopBase */, _At/* Motion.Main.lvl16 */, _AG/* Motion.Main.lvl27 */, _AK/* Motion.Main.lvl30 */));
          return new T3(0,_Fw/* s7K7 */.a,_Fw/* s7K7 */.b,_Fw/* s7K7 */.c);
        })));
      });
      return new T2(0,E(_Ft/* s7K2 */.a),E(new T2(2,_Ft/* s7K2 */.b,new T1(1,function(_Fx/* s7Kc */){
        return E(_Fv/* s7K5 */);
      }))));
    });
    return B(_xr/* Core.Render.Internal.$wshadowed */(_yT/* Motion.Main.lvl4 */, _AT/* Motion.Main.lvl5 */, _AY/* Motion.Main.lvl8 */, _Aj/* Motion.Main.lvl10 */, _Fs/* s7Kg */));
  }),
  _Fy/* s7Kh */ = function(_Fz/* s7Ki */){
    return E(_Fr/* s7JV */);
  },
  _FA/* s7Kk */ = new T(function(){
    return B(A1(_Fo/* s7JS */,_Fn/* s7JR */));
  }),
  _FB/* s7L7 */ = function(_FC/* s7Kl */){
    var _FD/* s7Km */ = new T(function(){
      return B(A1(_FA/* s7Kk */,_FC/* s7Kl */));
    }),
    _FE/* s7L6 */ = function(_FF/* s7Kn */){
      var _FG/* s7L5 */ = function(_FH/* s7Ko */){
        var _FI/* s7Kp */ = E(_FH/* s7Ko */),
        _FJ/* s7Ks */ = E(_FI/* s7Kp */.a),
        _FK/* s7Kv */ = new T(function(){
          var _FL/* s7Ky */ = B(_zY/* Core.Render.Internal.clip */(_yW/* Motion.Main.shape */, new T(function(){
            return B(_rx/* Control.Monad.Skeleton.bone */(new T3(7,_AW/* Motion.Main.lvl7 */,_FJ/* s7Ks */.a,_7/* GHC.Tuple.() */)));
          })));
          return new T2(0,E(_FL/* s7Ky */.a),E(new T2(2,_FL/* s7Ky */.b,new T1(1,_Fy/* s7Kh */))));
        }),
        _FM/* s7L4 */ = function(_/* EXTERNAL */){
          var _FN/* s7KD */ = nMV/* EXTERNAL */(_AR/* Motion.Main.lvl35 */);
          return new T(function(){
            var _FO/* s7KH */ = new T(function(){
              return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _AH/* Motion.Main.lvl3 */, _Ag/* Core.Ease.linear */, _FN/* s7KD */, _Ax/* Motion.Main.lvl2 */, _Ac/* Core.Ease.easeTo1 */));
            }),
            _FP/* s7KI */ = new T(function(){
              return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _AH/* Motion.Main.lvl3 */, _Ag/* Core.Ease.linear */, _FN/* s7KD */, _AL/* Motion.Main.lvl31 */, _Ac/* Core.Ease.easeTo1 */));
            }),
            _FQ/* s7L2 */ = function(_FR/* s7KT */){
              var _FS/* s7KU */ = new T(function(){
                return B(_zj/* Core.UI.button */(_FO/* s7KH */, _FP/* s7KI */, _z1/* Motion.Main.a23 */, _FR/* s7KT */));
              }),
              _FT/* s7L1 */ = function(_FU/* s7KV */, _FV/* s7KW */){
                return new T1(1,new T2(1,new T(function(){
                  return B(A2(_FS/* s7KU */,_FU/* s7KV */, _FV/* s7KW */));
                }),new T2(1,new T(function(){
                  return B(A2(_FJ/* s7Ks */.b,_FU/* s7KV */, _AM/* Motion.Main.lvl32 */));
                }),_6/* GHC.Types.[] */)));
              };
              return E(_FT/* s7L1 */);
            },
            _FW/* s7KS */ = new T(function(){
              var _FX/* s7KL */ = B(_xr/* Core.Render.Internal.$wshadowed */(_yT/* Motion.Main.lvl4 */, _AT/* Motion.Main.lvl5 */, new T2(2,new T3(0,_AH/* Motion.Main.lvl3 */,_Ag/* Core.Ease.linear */,_FN/* s7KD */),_2E/* GHC.Base.id */), _z5/* Core.Render.Internal.black */, _z0/* Motion.Main.a17 */));
              return new T2(0,E(_FX/* s7KL */.a),E(new T2(2,_FX/* s7KL */.b,new T1(1,function(_FY/* s7KO */){
                return E(_FK/* s7Kv */);
              }))));
            });
            return B(A(_CQ/* Core.View.makeView */,[_yO/* GHC.Base.Just */, _yW/* Motion.Main.shape */, _FW/* s7KS */, _FQ/* s7L2 */, _FI/* s7Kp */.b, _FF/* s7Kn */]));
          });
        };
        return new T1(0,_FM/* s7L4 */);
      };
      return new F(function(){return A1(_FD/* s7Km */,_FG/* s7L5 */);});
    };
    return E(_FE/* s7L6 */);
  };
  return E(_FB/* s7L7 */);
},
_FZ/* lvl36 */ = new T4(0,_yT/* Motion.Main.lvl4 */,_Az/* Motion.Main.lvl21 */,_Al/* Motion.Main.lvl11 */,_Al/* Motion.Main.lvl11 */),
_G0/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bounce"));
}),
_G1/* lvl38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Velocity & Acceleration"));
}),
_G2/* lvl39 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_FZ/* Motion.Main.lvl36 */, _wY/* Motion.Bounce.bounceMot1 */, _G0/* Motion.Main.lvl37 */, _G1/* Motion.Main.lvl38 */));
}),
_G3/* negateDouble */ = function(_G4/* s18yz */){
  return  -E(_G4/* s18yz */);
},
_G5/* $fAffineRender1 */ = function(_G6/* sFdU */, _G7/* sFdV */, _G8/* sFdW */, _G9/* sFdX */){
  var _Ga/* sFf1 */ = new T(function(){
    var _Gb/* sFeZ */ = new T(function(){
      var _Gc/* sFeW */ = new T(function(){
        var _Gd/* sFet */ = E(_G8/* sFdW */);
        switch(_Gd/* sFet */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_Gd/* sFet */.a);
            }));
            break;
          case 1:
            var _Ge/* sFeF */ = function(_/* EXTERNAL */){
              var _Gf/* sFeB */ = B(A1(_Gd/* sFet */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_G3/* GHC.Float.negateDouble */(_Gf/* sFeB */));
              });
            };
            return new T1(1,_Ge/* sFeF */);
            break;
          case 2:
            return new T2(2,_Gd/* sFet */.a,function(_Gg/* sFeI */){
              return  -B(A1(_Gd/* sFet */.b,_Gg/* sFeI */));
            });
            break;
          default:
            var _Gh/* sFeV */ = function(_Gi/* sFeP */, _/* EXTERNAL */){
              var _Gj/* sFeR */ = B(A2(_Gd/* sFet */.b,_Gi/* sFeP */, _/* EXTERNAL */));
              return new T(function(){
                return B(_G3/* GHC.Float.negateDouble */(_Gj/* sFeR */));
              });
            };
            return new T2(3,_Gd/* sFet */.a,_Gh/* sFeV */);
        }
      }),
      _Gk/* sFes */ = new T(function(){
        var _Gl/* sFdZ */ = E(_G7/* sFdV */);
        switch(_Gl/* sFdZ */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_Gl/* sFdZ */.a);
            }));
            break;
          case 1:
            var _Gm/* sFeb */ = function(_/* EXTERNAL */){
              var _Gn/* sFe7 */ = B(A1(_Gl/* sFdZ */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_G3/* GHC.Float.negateDouble */(_Gn/* sFe7 */));
              });
            };
            return new T1(1,_Gm/* sFeb */);
            break;
          case 2:
            return new T2(2,_Gl/* sFdZ */.a,function(_Go/* sFee */){
              return  -B(A1(_Gl/* sFdZ */.b,_Go/* sFee */));
            });
            break;
          default:
            var _Gp/* sFer */ = function(_Gq/* sFel */, _/* EXTERNAL */){
              var _Gr/* sFen */ = B(A2(_Gl/* sFdZ */.b,_Gq/* sFel */, _/* EXTERNAL */));
              return new T(function(){
                return B(_G3/* GHC.Float.negateDouble */(_Gr/* sFen */));
              });
            };
            return new T2(3,_Gl/* sFdZ */.a,_Gp/* sFer */);
        }
      });
      return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_Gk/* sFes */,_Gc/* sFeW */),_G9/* sFdX */,_7/* GHC.Tuple.() */)));
    });
    return B(_rx/* Control.Monad.Skeleton.bone */(new T3(7,_G6/* sFdU */,_Gb/* sFeZ */,_7/* GHC.Tuple.() */)));
  });
  return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_G7/* sFdV */,_G8/* sFdW */),_Ga/* sFf1 */,_7/* GHC.Tuple.() */));});
},
_Gs/* lvl */ = 0,
_Gt/* lvl1 */ = 40,
_Gu/* lvl2 */ = 0.9999999999999998,
_Gv/* lvl3 */ = new T4(0,_Gs/* Motion.Grow.lvl */,_Gs/* Motion.Grow.lvl */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_Gw/* lvl4 */ = new T2(0,_Gs/* Motion.Grow.lvl */,_Gv/* Motion.Grow.lvl3 */),
_Gx/* lvl5 */ = new T2(0,_Gw/* Motion.Grow.lvl4 */,_6/* GHC.Types.[] */),
_Gy/* $wa1 */ = function(_Gz/* sP3R */, _GA/* sP3S */, _GB/* sP3T */){
  return function(_/* EXTERNAL */){
    var _GC/* sP3V */ = nMV/* EXTERNAL */(_Gx/* Motion.Grow.lvl5 */);
    return new T(function(){
      var _GD/* sP3Y */ = function(_GE/* sP3Z */, _GF/* sP40 */){
        return 1-B(A1(_GE/* sP3Z */,new T(function(){
          var _GG/* sP43 */ = E(_GF/* sP40 */)/0.3-_Gz/* sP3R *//7*2.3333333333333335;
          if(1>_GG/* sP43 */){
            if(0>_GG/* sP43 */){
              return E(_Gu/* Motion.Grow.lvl2 */);
            }else{
              var _GH/* sP4c */ = 1-_GG/* sP43 */;
              return _GH/* sP4c */*_GH/* sP4c */*(2.70158*_GH/* sP4c */-1.70158);
            }
          }else{
            return E(_Gs/* Motion.Grow.lvl */);
          }
        })));
      },
      _GI/* sP4p */ = new T3(0,_Gt/* Motion.Grow.lvl1 */,function(_GJ/* sP4l */, _GK/* sP4m */){
        return new F(function(){return _GD/* sP3Y */(_GJ/* sP4l */, _GK/* sP4m */);});
      },_GC/* sP3V */),
      _GL/* sP4q */ = E(_Gz/* sP3R */);
      if(_GL/* sP4q */==7){
        return B(A1(_GB/* sP3T */,new T2(0,new T2(1,_GI/* sP4p */,_6/* GHC.Types.[] */),_GA/* sP3S */)));
      }else{
        return new T1(0,B(_Gy/* Motion.Grow.$wa1 */(_GL/* sP4q */+1|0, _GA/* sP3S */, function(_GM/* sP4s */){
          var _GN/* sP4t */ = E(_GM/* sP4s */);
          return new F(function(){return A1(_GB/* sP3T */,new T2(0,new T2(1,_GI/* sP4p */,_GN/* sP4t */.a),_GN/* sP4t */.b));});
        })));
      }
    });
  };
},
_GO/* $wcenterRect */ = function(_GP/* stCT */, _GQ/* stCU */, _GR/* stCV */, _GS/* stCW */){
  var _GT/* stF2 */ = function(_GU/* stDP */, _GV/* stDQ */, _GW/* stDR */, _/* EXTERNAL */){
    var _GX/* stF1 */ = function(_GY/* stDT */, _GZ/* stDU */, _H0/* stDV */, _/* EXTERNAL */){
      var _H1/* stF0 */ = function(_H2/* stDX */){
        var _H3/* stDY */ = new T(function(){
          return E(_H2/* stDX */)/2;
        }),
        _H4/* stEZ */ = function(_H5/* stE2 */, _H6/* stE3 */, _H7/* stE4 */, _/* EXTERNAL */){
          var _H8/* stE6 */ = E(_GU/* stDP */),
          _H9/* stE8 */ = E(_H3/* stDY */),
          _Ha/* stEa */ = _H8/* stE6 */+_H9/* stE8 */,
          _Hb/* stEg */ = _H8/* stE6 */-_H9/* stE8 */,
          _Hc/* stEj */ = E(_GY/* stDT */),
          _Hd/* stEn */ = E(_H5/* stE2 */)/2,
          _He/* stEr */ = _Hc/* stEj */+_Hd/* stEn */,
          _Hf/* stEu */ = _Hc/* stEj */-_Hd/* stEn */,
          _Hg/* stEx */ = E(_H6/* stE3 */),
          _Hh/* stEB */ = E(_H7/* stE4 */),
          _Hi/* stEE */ = __app4/* EXTERNAL */(E(_kz/* Core.Shape.Internal.bezier_f2 */), _Hb/* stEg */, _Hf/* stEu */, _Hg/* stEx */, _Hh/* stEB */),
          _Hj/* stEH */ = E(_kA/* Core.Shape.Internal.line_f1 */),
          _Hk/* stEK */ = __app4/* EXTERNAL */(_Hj/* stEH */, _Ha/* stEa */, _Hc/* stEj */-_Hd/* stEn */, _Hg/* stEx */, _Hh/* stEB */),
          _Hl/* stEO */ = __app4/* EXTERNAL */(_Hj/* stEH */, _Ha/* stEa */, _He/* stEr */, _Hg/* stEx */, _Hh/* stEB */),
          _Hm/* stES */ = __app4/* EXTERNAL */(_Hj/* stEH */, _H8/* stE6 */-_H9/* stE8 */, _He/* stEr */, _Hg/* stEx */, _Hh/* stEB */),
          _Hn/* stEW */ = __app4/* EXTERNAL */(_Hj/* stEH */, _Hb/* stEg */, _Hf/* stEu */, _Hg/* stEx */, _Hh/* stEB */);
          return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        };
        return function(_gd/* _fa_1 */, _ge/* _fa_2 */, _Ho/* _fa_3 */){
          return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_GS/* stCW */, _H4/* stEZ */, _gd/* _fa_1 */, _ge/* _fa_2 */, _Ho/* _fa_3 */);});
        };
      };
      return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_GR/* stCV */, _H1/* stF0 */, _GZ/* stDU */, _H0/* stDV */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_GQ/* stCU */, _GX/* stF1 */, _GV/* stDQ */, _GW/* stDR */, _/* EXTERNAL */);});
  },
  _Hp/* stDO */ = function(_Hq/* stCX */, _/* EXTERNAL */){
    var _Hr/* stCZ */ = E(_Hq/* stCX */),
    _Hs/* stDN */ = function(_Ht/* stD2 */, _/* EXTERNAL */){
      var _Hu/* stDM */ = function(_Hv/* stD4 */, _/* EXTERNAL */){
        var _Hw/* stDL */ = function(_Hx/* stD6 */, _/* EXTERNAL */){
          var _Hy/* stDK */ = function(_Hz/* stD8 */, _/* EXTERNAL */){
            return new T(function(){
              var _HA/* stDe */ = function(_HB/* stDf */){
                if(_HB/* stDf */>=E(_Hx/* stD6 */)/2){
                  return false;
                }else{
                  var _HC/* stDp */ = E(_Hr/* stCZ */.b)-E(_Hv/* stD4 */);
                  return (_HC/* stDp */==0) ? 0<E(_Hz/* stD8 */)/2 : (_HC/* stDp */<=0) ?  -_HC/* stDp */<E(_Hz/* stD8 */)/2 : _HC/* stDp */<E(_Hz/* stD8 */)/2;
                }
              },
              _HD/* stDF */ = E(_Hr/* stCZ */.a)-E(_Ht/* stD2 */);
              if(!_HD/* stDF */){
                return B(_HA/* stDe */(0));
              }else{
                if(_HD/* stDF */<=0){
                  return B(_HA/* stDe */( -_HD/* stDF */));
                }else{
                  return B(_HA/* stDe */(_HD/* stDF */));
                }
              }
            });
          };
          return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_GS/* stCW */, _Hy/* stDK */, _/* EXTERNAL */);});
        };
        return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_GR/* stCV */, _Hw/* stDL */, _/* EXTERNAL */);});
      };
      return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_GQ/* stCU */, _Hu/* stDM */, _/* EXTERNAL */);});
    };
    return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_GP/* stCT */, _Hs/* stDN */, _/* EXTERNAL */);});
  };
  return new T3(0,_Hp/* stDO */,function(_lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_GP/* stCT */, _GT/* stF2 */, _lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_HE/* a2 */ = 20,
_HF/* a3 */ = new T1(0,_/* EXTERNAL */),
_HG/* a4 */ = new T1(0,_6/* GHC.Types.[] */),
_HH/* a5 */ = new T2(0,E(_HG/* Motion.Grow.a4 */),E(_HF/* Motion.Grow.a3 */)),
_HI/* ds */ = 1,
_HJ/* a */ = function(_HK/* sP3O */, _HL/* sP3P */){
  return new F(function(){return A1(_HL/* sP3P */,new T2(0,_7/* GHC.Tuple.() */,_HK/* sP3O */));});
},
_HM/* go */ = function(_HN/* sP4F */){
  var _HO/* sP4G */ = E(_HN/* sP4F */);
  if(!_HO/* sP4G */._){
    return E(_HJ/* Motion.Grow.a */);
  }else{
    var _HP/* sP4J */ = new T(function(){
      var _HQ/* sP4K */ = E(_HO/* sP4G */.a);
      return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _HQ/* sP4K */.a, _HQ/* sP4K */.b, _HQ/* sP4K */.c, _HI/* Motion.Grow.ds */, _Ac/* Core.Ease.easeTo1 */));
    }),
    _HR/* sP4O */ = new T(function(){
      return B(_HM/* Motion.Grow.go */(_HO/* sP4G */.b));
    }),
    _HS/* sP4Y */ = function(_HT/* sP4P */){
      var _HU/* sP4Q */ = new T(function(){
        return B(A1(_HP/* sP4J */,_HT/* sP4P */));
      }),
      _HV/* sP4X */ = function(_HW/* sP4R */){
        return new F(function(){return A1(_HU/* sP4Q */,function(_HX/* sP4S */){
          return new F(function(){return A2(_HR/* sP4O */,E(_HX/* sP4S */).b, _HW/* sP4R */);});
        });});
      };
      return E(_HV/* sP4X */);
    };
    return E(_HS/* sP4Y */);
  }
},
_HY/* go1 */ = function(_HZ/* sP4Z */){
  var _I0/* sP50 */ = E(_HZ/* sP4Z */);
  if(!_I0/* sP50 */._){
    return E(_HJ/* Motion.Grow.a */);
  }else{
    var _I1/* sP53 */ = new T(function(){
      var _I2/* sP54 */ = E(_I0/* sP50 */.a),
      _I3/* sP5j */ = function(_I4/* sP58 */){
        var _I5/* sP59 */ = new T(function(){
          return B(A1(_I2/* sP54 */.b,_I4/* sP58 */));
        }),
        _I6/* sP5i */ = function(_I7/* sP5a */){
          return 1-B(A1(_I5/* sP59 */,new T(function(){
            return 1-E(_I7/* sP5a */);
          })));
        };
        return E(_I6/* sP5i */);
      };
      return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _I2/* sP54 */.a, _I3/* sP5j */, _I2/* sP54 */.c, _Gs/* Motion.Grow.lvl */, _Ac/* Core.Ease.easeTo1 */));
    }),
    _I8/* sP5k */ = new T(function(){
      return B(_HY/* Motion.Grow.go1 */(_I0/* sP50 */.b));
    }),
    _I9/* sP5u */ = function(_Ia/* sP5l */){
      var _Ib/* sP5m */ = new T(function(){
        return B(A1(_I1/* sP53 */,_Ia/* sP5l */));
      }),
      _Ic/* sP5t */ = function(_Id/* sP5n */){
        return new F(function(){return A1(_Ib/* sP5m */,function(_Ie/* sP5o */){
          return new F(function(){return A2(_I8/* sP5k */,E(_Ie/* sP5o */).b, _Id/* sP5n */);});
        });});
      };
      return E(_Ic/* sP5t */);
    };
    return E(_I9/* sP5u */);
  }
},
_If/* eftInt */ = function(_Ig/* smpW */, _Ih/* smpX */){
  if(_Ig/* smpW */<=_Ih/* smpX */){
    var _Ii/* smq0 */ = function(_Ij/* smq1 */){
      return new T2(1,_Ij/* smq1 */,new T(function(){
        if(_Ij/* smq1 */!=_Ih/* smpX */){
          return B(_Ii/* smq0 */(_Ij/* smq1 */+1|0));
        }else{
          return __Z/* EXTERNAL */;
        }
      }));
    };
    return new F(function(){return _Ii/* smq0 */(_Ig/* smpW */);});
  }else{
    return __Z/* EXTERNAL */;
  }
},
_Ik/* iforM1 */ = new T(function(){
  return B(_If/* GHC.Enum.eftInt */(0, 2147483647));
}),
_Il/* lvl10 */ = 3,
_Im/* lvl6 */ = new T1(0,_Gt/* Motion.Grow.lvl1 */),
_In/* lvl7 */ = new T1(0,_HE/* Motion.Grow.a2 */),
_Io/* lvl8 */ = -20,
_Ip/* lvl9 */ = 60,
_Iq/* morph */ = function(_Ir/* sb2x */){
  return new T2(2,_Ir/* sb2x */,_2E/* GHC.Base.id */);
},
_Is/* $wa */ = function(_It/* sP5v */, _Iu/* sP5w */, _Iv/* sP5x */){
  var _Iw/* sP5y */ = function(_Ix/* sP5z */, _Iy/* sP5A */){
    var _Iz/* sP5B */ = E(_Ix/* sP5z */);
    if(!_Iz/* sP5B */._){
      return E(_HH/* Motion.Grow.a5 */);
    }else{
      var _IA/* sP5C */ = _Iz/* sP5B */.a,
      _IB/* sP5E */ = E(_Iy/* sP5A */);
      if(!_IB/* sP5E */._){
        return E(_HH/* Motion.Grow.a5 */);
      }else{
        var _IC/* sP5F */ = _IB/* sP5E */.a,
        _ID/* sP5H */ = new T(function(){
          var _IE/* sP5I */ = E(_IA/* sP5C */);
          if(_IE/* sP5I */>=4){
            if(_IE/* sP5I */<=4){
              return E(_HI/* Motion.Grow.ds */);
            }else{
              return _IE/* sP5I */-4|0;
            }
          }else{
            return 4-_IE/* sP5I */|0;
          }
        }),
        _IF/* sP5S */ = new T(function(){
          var _IG/* sP5V */ = E(_IA/* sP5C */)-2|0;
          if(1>_IG/* sP5V */){
            return E(_HI/* Motion.Grow.ds */);
          }else{
            if(3>_IG/* sP5V */){
              return _IG/* sP5V */;
            }else{
              return E(_Il/* Motion.Grow.lvl10 */);
            }
          }
        }),
        _IH/* sP6A */ = new T(function(){
          var _II/* sP6z */ = new T(function(){
            var _IJ/* sP6v */ = B(_GO/* Core.Shape.Internal.$wcenterRect */(new T(function(){
              return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_IF/* sP5S */), _Im/* Motion.Grow.lvl6 */)), _In/* Motion.Grow.lvl7 */));
            }), new T(function(){
              return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_ID/* sP5H */), _Im/* Motion.Grow.lvl6 */)), _In/* Motion.Grow.lvl7 */));
            }), _Im/* Motion.Grow.lvl6 */, _Im/* Motion.Grow.lvl6 */));
            return new T3(0,_IJ/* sP6v */.a,_IJ/* sP6v */.b,_IJ/* sP6v */.c);
          });
          return B(_rB/* Core.Render.Internal.fill1 */(_It/* sP5v */, _II/* sP6z */));
        }),
        _IK/* sP6o */ = new T(function(){
          return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_ID/* sP5H */), _Im/* Motion.Grow.lvl6 */)), _In/* Motion.Grow.lvl7 */)), new T1(0,new T(function(){
            var _IL/* sP6g */ = E(_IA/* sP5C */);
            if(_IL/* sP6g */>=4){
              if(_IL/* sP6g */<=4){
                return E(_Gs/* Motion.Grow.lvl */);
              }else{
                return E(_Io/* Motion.Grow.lvl8 */);
              }
            }else{
              return E(_HE/* Motion.Grow.a2 */);
            }
          }))));
        }),
        _IM/* sP6c */ = new T(function(){
          return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_IF/* sP5S */), _Im/* Motion.Grow.lvl6 */)), _In/* Motion.Grow.lvl7 */)), new T1(0,new T(function(){
            switch(E(_IA/* sP5C */)){
              case 4:
                return E(_Io/* Motion.Grow.lvl8 */);
                break;
              case 5:
                return E(_Io/* Motion.Grow.lvl8 */);
                break;
              default:
                return E(_Gs/* Motion.Grow.lvl */);
            }
          }))));
        }),
        _IN/* sP6B */ = B(_G5/* Core.Render.Internal.$fAffineRender1 */(new T2(0,new T(function(){
          return B(_Iq/* Core.Ease.morph */(_IC/* sP5F */));
        }),new T(function(){
          return B(_Iq/* Core.Ease.morph */(_IC/* sP5F */));
        })), _IM/* sP6c */, _IK/* sP6o */, _IH/* sP6A */)),
        _IO/* sP6E */ = new T(function(){
          return B(_Iw/* sP5y */(_Iz/* sP5B */.b, _IB/* sP5E */.b));
        }),
        _IP/* sP6P */ = function(_IQ/* sP6F */){
          var _IR/* sP6G */ = E(_IO/* sP6E */);
          return new T2(0,E(_IR/* sP6G */.a),E(new T2(2,_IR/* sP6G */.b,new T1(1,function(_IS/* sP6J */){
            return new T2(0,E(new T1(0,new T2(1,_IQ/* sP6F */,_IS/* sP6J */))),E(_HF/* Motion.Grow.a3 */));
          }))));
        };
        return new T2(0,E(_IN/* sP6B */.a),E(new T2(2,_IN/* sP6B */.b,new T1(1,_IP/* sP6P */))));
      }
    }
  },
  _IT/* sP7r */ = function(_IU/* sP6S */){
    var _IV/* sP6T */ = E(_IU/* sP6S */),
    _IW/* sP6U */ = _IV/* sP6T */.a,
    _IX/* sP6W */ = new T(function(){
      return B(_HY/* Motion.Grow.go1 */(_IW/* sP6U */));
    }),
    _IY/* sP6X */ = new T(function(){
      return B(_HM/* Motion.Grow.go */(_IW/* sP6U */));
    }),
    _IZ/* sP6Y */ = function(_J0/* sP6Z */){
      var _J1/* sP70 */ = new T(function(){
        return B(A1(_IY/* sP6X */,_J0/* sP6Z */));
      }),
      _J2/* sP7m */ = function(_J3/* sP71 */){
        var _J4/* sP72 */ = function(_J5/* sP73 */){
          return new F(function(){return A2(_IZ/* sP6Y */,E(_J5/* sP73 */).b, _J3/* sP71 */);});
        },
        _J6/* sP77 */ = function(_J7/* sP78 */){
          return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_Ip/* Motion.Grow.lvl9 */, E(_J7/* sP78 */).b, _J4/* sP72 */);});
        },
        _J8/* sP7c */ = function(_J9/* sP7d */){
          return new F(function(){return A2(_IX/* sP6W */,E(_J9/* sP7d */).b, _J6/* sP77 */);});
        };
        return new F(function(){return A1(_J1/* sP70 */,function(_Ja/* sP7h */){
          return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_Ip/* Motion.Grow.lvl9 */, E(_Ja/* sP7h */).b, _J8/* sP7c */);});
        });});
      };
      return E(_J2/* sP7m */);
    },
    _Jb/* sP7o */ = new T(function(){
      return B(_rp/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
        return B(_Iw/* sP5y */(_Ik/* Core.Util.iforM1 */, _IW/* sP6U */));
      })));
    });
    return new F(function(){return A1(_Iv/* sP5x */,new T2(0,new T2(0,_Jb/* sP7o */,_IZ/* sP6Y */),_IV/* sP6T */.b));});
  };
  return new F(function(){return _Gy/* Motion.Grow.$wa1 */(0, _Iu/* sP5w */, _IT/* sP7r */);});
},
_Jc/* growMot1 */ = function(_Jd/* sP7s */, _Je/* sP7t */, _Jf/* sP7u */){
  return new T1(0,B(_Is/* Motion.Grow.$wa */(_Jd/* sP7s */, _Je/* sP7t */, _Jf/* sP7u */)));
},
_Jg/* lvl40 */ = 0.8,
_Jh/* lvl41 */ = new T1(0,_Jg/* Motion.Main.lvl40 */),
_Ji/* lvl42 */ = new T4(0,_Az/* Motion.Main.lvl21 */,_Jh/* Motion.Main.lvl41 */,_yT/* Motion.Main.lvl4 */,_Al/* Motion.Main.lvl11 */),
_Jj/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Grow"));
}),
_Jk/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sequential easeOutBack"));
}),
_Jl/* lvl45 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_Ji/* Motion.Main.lvl42 */, _Jc/* Motion.Grow.growMot1 */, _Jj/* Motion.Main.lvl43 */, _Jk/* Motion.Main.lvl44 */));
}),
_Jm/* lvl46 */ = new T4(0,_Al/* Motion.Main.lvl11 */,_Ai/* Motion.Main.lvl9 */,_yT/* Motion.Main.lvl4 */,_Al/* Motion.Main.lvl11 */),
_Jn/* lvl47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Speed"));
}),
_Jo/* lvl48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uniform Distr & Exponential Distr"));
}),
_Jp/* speedMot1 */ = function(_Jq/* sRx5 */, _Jr/* sRx6 */){
  return new F(function(){return A1(_Jr/* sRx6 */,new T2(0,_7/* GHC.Tuple.() */,_Jq/* sRx5 */));});
},
_Js/* speedMot14 */ = 0,
_Jt/* speedMot13 */ = new T1(0,_Js/* Motion.Speed.speedMot14 */),
_Ju/* speedMot12 */ = new T2(0,_Jt/* Motion.Speed.speedMot13 */,_Jt/* Motion.Speed.speedMot13 */),
_Jv/* intToInt64# */ = function(_Jw/* sf6 */){
  var _Jx/* sf8 */ = hs_intToInt64/* EXTERNAL */(_Jw/* sf6 */);
  return E(_Jx/* sf8 */);
},
_Jy/* integerToInt64 */ = function(_Jz/* s1S1 */){
  var _JA/* s1S2 */ = E(_Jz/* s1S1 */);
  if(!_JA/* s1S2 */._){
    return new F(function(){return _Jv/* GHC.IntWord64.intToInt64# */(_JA/* s1S2 */.a);});
  }else{
    return new F(function(){return I_toInt64/* EXTERNAL */(_JA/* s1S2 */.a);});
  }
},
_JB/* $cfromInteger3 */ = function(_JC/* s2dWF */){
  return new F(function(){return _Jy/* GHC.Integer.Type.integerToInt64 */(_JC/* s2dWF */);});
},
_JD/* $fNumInt64_$c* */ = function(_JE/* s2dXh */, _JF/* s2dXi */){
  return new F(function(){return hs_timesInt64/* EXTERNAL */(E(_JE/* s2dXh */), E(_JF/* s2dXi */));});
},
_JG/* $fNumInt64_$c+ */ = function(_JH/* s2dXB */, _JI/* s2dXC */){
  return new F(function(){return hs_plusInt64/* EXTERNAL */(E(_JH/* s2dXB */), E(_JI/* s2dXC */));});
},
_JJ/* $fNumInt64_$c- */ = function(_JK/* s2dXr */, _JL/* s2dXs */){
  return new F(function(){return hs_minusInt64/* EXTERNAL */(E(_JK/* s2dXr */), E(_JL/* s2dXs */));});
},
_JM/* $w$cabs */ = function(_JN/* s2dWW */){
  var _JO/* s2dWY */ = hs_geInt64/* EXTERNAL */(_JN/* s2dWW */, new Long/* EXTERNAL */(0, 0));
  if(!_JO/* s2dWY */){
    var _JP/* s2dX3 */ = hs_negateInt64/* EXTERNAL */(_JN/* s2dWW */);
    return E(_JP/* s2dX3 */);
  }else{
    return E(_JN/* s2dWW */);
  }
},
_JQ/* $fNumInt64_$cabs */ = function(_JR/* s2dX6 */){
  return new F(function(){return _JM/* GHC.Int.$w$cabs */(E(_JR/* s2dX6 */));});
},
_JS/* $fNumInt64_$cnegate */ = function(_JT/* s2dXa */){
  return new F(function(){return hs_negateInt64/* EXTERNAL */(E(_JT/* s2dXa */));});
},
_JU/* $w$csignum */ = function(_JV/* s2dWH */){
  var _JW/* s2dWJ */ = hs_gtInt64/* EXTERNAL */(_JV/* s2dWH */, new Long/* EXTERNAL */(0, 0));
  if(!_JW/* s2dWJ */){
    var _JX/* s2dWO */ = hs_eqInt64/* EXTERNAL */(_JV/* s2dWH */, new Long/* EXTERNAL */(0, 0));
    if(!_JX/* s2dWO */){
      return new F(function(){return new Long/* EXTERNAL */(4294967295, -1);});
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return new F(function(){return new Long/* EXTERNAL */(1, 0);});
  }
},
_JY/* $fNumInt64_$csignum */ = function(_JZ/* s2dWS */){
  return new F(function(){return _JU/* GHC.Int.$w$csignum */(E(_JZ/* s2dWS */));});
},
_K0/* $fNumInt64 */ = {_:0,a:_JG/* GHC.Int.$fNumInt64_$c+ */,b:_JJ/* GHC.Int.$fNumInt64_$c- */,c:_JD/* GHC.Int.$fNumInt64_$c* */,d:_JS/* GHC.Int.$fNumInt64_$cnegate */,e:_JQ/* GHC.Int.$fNumInt64_$cabs */,f:_JY/* GHC.Int.$fNumInt64_$csignum */,g:_JB/* GHC.Int.$cfromInteger3 */},
_K1/* lvl */ = new T1(0,0),
_K2/* orInteger */ = function(_K3/* s1KS */, _K4/* s1KT */){
  while(1){
    var _K5/* s1KU */ = E(_K3/* s1KS */);
    if(!_K5/* s1KU */._){
      var _K6/* s1KV */ = _K5/* s1KU */.a,
      _K7/* s1KW */ = E(_K4/* s1KT */);
      if(!_K7/* s1KW */._){
        return new T1(0,(_K6/* s1KV */>>>0|_K7/* s1KW */.a>>>0)>>>0&4294967295);
      }else{
        _K3/* s1KS */ = new T1(1,I_fromInt/* EXTERNAL */(_K6/* s1KV */));
        _K4/* s1KT */ = _K7/* s1KW */;
        continue;
      }
    }else{
      var _K8/* s1L7 */ = E(_K4/* s1KT */);
      if(!_K8/* s1L7 */._){
        _K3/* s1KS */ = _K5/* s1KU */;
        _K4/* s1KT */ = new T1(1,I_fromInt/* EXTERNAL */(_K8/* s1L7 */.a));
        continue;
      }else{
        return new T1(1,I_or/* EXTERNAL */(_K5/* s1KU */.a, _K8/* s1L7 */.a));
      }
    }
  }
},
_K9/* shiftLInteger */ = function(_Ka/* s1Jk */, _Kb/* s1Jl */){
  while(1){
    var _Kc/* s1Jm */ = E(_Ka/* s1Jk */);
    if(!_Kc/* s1Jm */._){
      _Ka/* s1Jk */ = new T1(1,I_fromInt/* EXTERNAL */(_Kc/* s1Jm */.a));
      continue;
    }else{
      return new T1(1,I_shiftLeft/* EXTERNAL */(_Kc/* s1Jm */.a, _Kb/* s1Jl */));
    }
  }
},
_Kd/* mkInteger_f */ = function(_Ke/* s1S6 */){
  var _Kf/* s1S7 */ = E(_Ke/* s1S6 */);
  if(!_Kf/* s1S7 */._){
    return E(_K1/* GHC.Integer.Type.lvl */);
  }else{
    return new F(function(){return _K2/* GHC.Integer.Type.orInteger */(new T1(0,E(_Kf/* s1S7 */.a)), B(_K9/* GHC.Integer.Type.shiftLInteger */(B(_Kd/* GHC.Integer.Type.mkInteger_f */(_Kf/* s1S7 */.b)), 31)));});
  }
},
_Kg/* log2I1 */ = new T1(0,1),
_Kh/* lvl2 */ = new T1(0,2147483647),
_Ki/* plusInteger */ = function(_Kj/* s1Qe */, _Kk/* s1Qf */){
  while(1){
    var _Kl/* s1Qg */ = E(_Kj/* s1Qe */);
    if(!_Kl/* s1Qg */._){
      var _Km/* s1Qh */ = _Kl/* s1Qg */.a,
      _Kn/* s1Qi */ = E(_Kk/* s1Qf */);
      if(!_Kn/* s1Qi */._){
        var _Ko/* s1Qj */ = _Kn/* s1Qi */.a,
        _Kp/* s1Qk */ = addC/* EXTERNAL */(_Km/* s1Qh */, _Ko/* s1Qj */);
        if(!E(_Kp/* s1Qk */.b)){
          return new T1(0,_Kp/* s1Qk */.a);
        }else{
          _Kj/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_Km/* s1Qh */));
          _Kk/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_Ko/* s1Qj */));
          continue;
        }
      }else{
        _Kj/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_Km/* s1Qh */));
        _Kk/* s1Qf */ = _Kn/* s1Qi */;
        continue;
      }
    }else{
      var _Kq/* s1Qz */ = E(_Kk/* s1Qf */);
      if(!_Kq/* s1Qz */._){
        _Kj/* s1Qe */ = _Kl/* s1Qg */;
        _Kk/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_Kq/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_Kl/* s1Qg */.a, _Kq/* s1Qz */.a));
      }
    }
  }
},
_Kr/* lvl3 */ = new T(function(){
  return B(_Ki/* GHC.Integer.Type.plusInteger */(_Kh/* GHC.Integer.Type.lvl2 */, _Kg/* GHC.Integer.Type.log2I1 */));
}),
_Ks/* negateInteger */ = function(_Kt/* s1QH */){
  var _Ku/* s1QI */ = E(_Kt/* s1QH */);
  if(!_Ku/* s1QI */._){
    var _Kv/* s1QK */ = E(_Ku/* s1QI */.a);
    return (_Kv/* s1QK */==(-2147483648)) ? E(_Kr/* GHC.Integer.Type.lvl3 */) : new T1(0, -_Kv/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_Ku/* s1QI */.a));
  }
},
_Kw/* mkInteger */ = function(_Kx/* s1Sf */, _Ky/* s1Sg */){
  if(!E(_Kx/* s1Sf */)){
    return new F(function(){return _Ks/* GHC.Integer.Type.negateInteger */(B(_Kd/* GHC.Integer.Type.mkInteger_f */(_Ky/* s1Sg */)));});
  }else{
    return new F(function(){return _Kd/* GHC.Integer.Type.mkInteger_f */(_Ky/* s1Sg */);});
  }
},
_Kz/* sfn3 */ = 2147483647,
_KA/* sfn4 */ = 2147483647,
_KB/* sfn5 */ = 1,
_KC/* sfn6 */ = new T2(1,_KB/* sfn5 */,_6/* GHC.Types.[] */),
_KD/* sfn7 */ = new T2(1,_KA/* sfn4 */,_KC/* sfn6 */),
_KE/* sfn8 */ = new T2(1,_Kz/* sfn3 */,_KD/* sfn7 */),
_KF/* $fRandomCLLong3 */ = new T(function(){
  return B(_Kw/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _KE/* sfn8 */));
}),
_KG/* sfn9 */ = 0,
_KH/* sfna */ = 0,
_KI/* sfnb */ = 2,
_KJ/* sfnc */ = new T2(1,_KI/* sfnb */,_6/* GHC.Types.[] */),
_KK/* sfnd */ = new T2(1,_KH/* sfna */,_KJ/* sfnc */),
_KL/* sfne */ = new T2(1,_KG/* sfn9 */,_KK/* sfnd */),
_KM/* $fRandomCLLong4 */ = new T(function(){
  return B(_Kw/* GHC.Integer.Type.mkInteger */(_av/* GHC.Types.False */, _KL/* sfne */));
}),
_KN/* $fRandomDouble4 */ = new Long/* EXTERNAL */(2, 0),
_KO/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_KP/* $fRandomDouble5 */ = new T(function(){
  return B(err/* EXTERNAL */(_KO/* System.Random.lvl1 */));
}),
_KQ/* $fRandomDouble6 */ = new Long/* EXTERNAL */(1, 0),
_KR/* $fBoundedInt64_$cmaxBound */ = new Long/* EXTERNAL */(4294967295, 2147483647),
_KS/* $fBoundedInt64_$cminBound */ = new Long/* EXTERNAL */(0, -2147483648),
_KT/* $fBoundedInt64 */ = new T2(0,_KS/* GHC.Int.$fBoundedInt64_$cminBound */,_KR/* GHC.Int.$fBoundedInt64_$cmaxBound */),
_KU/* $fEnumRatio1 */ = new T1(0,1),
_KV/* $p1Integral */ = function(_KW/* sveb */){
  return E(E(_KW/* sveb */).a);
},
_KX/* $p1Real */ = function(_KY/* svfM */){
  return E(E(_KY/* svfM */).a);
},
_KZ/* fromInteger */ = function(_L0/* s6Gq */){
  return E(E(_L0/* s6Gq */).g);
},
_L1/* gtInteger */ = function(_L2/* s1G4 */, _L3/* s1G5 */){
  var _L4/* s1G6 */ = E(_L2/* s1G4 */);
  if(!_L4/* s1G6 */._){
    var _L5/* s1G7 */ = _L4/* s1G6 */.a,
    _L6/* s1G8 */ = E(_L3/* s1G5 */);
    return (_L6/* s1G8 */._==0) ? _L5/* s1G7 */>_L6/* s1G8 */.a : I_compareInt/* EXTERNAL */(_L6/* s1G8 */.a, _L5/* s1G7 */)<0;
  }else{
    var _L7/* s1Gf */ = _L4/* s1G6 */.a,
    _L8/* s1Gg */ = E(_L3/* s1G5 */);
    return (_L8/* s1Gg */._==0) ? I_compareInt/* EXTERNAL */(_L7/* s1Gf */, _L8/* s1Gg */.a)>0 : I_compare/* EXTERNAL */(_L7/* s1Gf */, _L8/* s1Gg */.a)>0;
  }
},
_L9/* maxBound */ = function(_La/* smmz */){
  return E(E(_La/* smmz */).b);
},
_Lb/* toInteger */ = function(_Lc/* svfB */){
  return E(E(_Lc/* svfB */).i);
},
_Ld/* integralEnumFrom */ = function(_Le/* svkx */, _Lf/* svky */, _Lg/* svkz */){
  var _Lh/* svkC */ = new T(function(){
    return B(_KZ/* GHC.Num.fromInteger */(new T(function(){
      return B(_KX/* GHC.Real.$p1Real */(new T(function(){
        return B(_KV/* GHC.Real.$p1Integral */(_Le/* svkx */));
      })));
    })));
  }),
  _Li/* svkE */ = new T(function(){
    return B(_L9/* GHC.Enum.maxBound */(_Lf/* svky */));
  }),
  _Lj/* svkF */ = function(_Lk/* svkG */){
    return (!B(_L1/* GHC.Integer.Type.gtInteger */(_Lk/* svkG */, B(A2(_Lb/* GHC.Real.toInteger */,_Le/* svkx */, _Li/* svkE */))))) ? new T2(1,new T(function(){
      return B(A1(_Lh/* svkC */,_Lk/* svkG */));
    }),new T(function(){
      return B(_Lj/* svkF */(B(_Ki/* GHC.Integer.Type.plusInteger */(_Lk/* svkG */, _KU/* GHC.Real.$fEnumRatio1 */))));
    })) : __Z/* EXTERNAL */;
  };
  return new F(function(){return _Lj/* svkF */(B(A2(_Lb/* GHC.Real.toInteger */,_Le/* svkx */, _Lg/* svkz */)));});
},
_Ll/* $fEnumInt64_$cenumFrom */ = function(_Lm/* B1 */){
  return new F(function(){return _Ld/* GHC.Real.integralEnumFrom */(_Ln/* GHC.Int.$fIntegralInt64 */, _KT/* GHC.Int.$fBoundedInt64 */, _Lm/* B1 */);});
},
_Lo/* $fEnumInteger1 */ = new T1(0,0),
_Lp/* geInteger */ = function(_Lq/* s1Fo */, _Lr/* s1Fp */){
  var _Ls/* s1Fq */ = E(_Lq/* s1Fo */);
  if(!_Ls/* s1Fq */._){
    var _Lt/* s1Fr */ = _Ls/* s1Fq */.a,
    _Lu/* s1Fs */ = E(_Lr/* s1Fp */);
    return (_Lu/* s1Fs */._==0) ? _Lt/* s1Fr */>=_Lu/* s1Fs */.a : I_compareInt/* EXTERNAL */(_Lu/* s1Fs */.a, _Lt/* s1Fr */)<=0;
  }else{
    var _Lv/* s1Fz */ = _Ls/* s1Fq */.a,
    _Lw/* s1FA */ = E(_Lr/* s1Fp */);
    return (_Lw/* s1FA */._==0) ? I_compareInt/* EXTERNAL */(_Lv/* s1Fz */, _Lw/* s1FA */.a)>=0 : I_compare/* EXTERNAL */(_Lv/* s1Fz */, _Lw/* s1FA */.a)>=0;
  }
},
_Lx/* ltInteger */ = function(_Ly/* s1FJ */, _Lz/* s1FK */){
  var _LA/* s1FL */ = E(_Ly/* s1FJ */);
  if(!_LA/* s1FL */._){
    var _LB/* s1FM */ = _LA/* s1FL */.a,
    _LC/* s1FN */ = E(_Lz/* s1FK */);
    return (_LC/* s1FN */._==0) ? _LB/* s1FM */<_LC/* s1FN */.a : I_compareInt/* EXTERNAL */(_LC/* s1FN */.a, _LB/* s1FM */)>0;
  }else{
    var _LD/* s1FU */ = _LA/* s1FL */.a,
    _LE/* s1FV */ = E(_Lz/* s1FK */);
    return (_LE/* s1FV */._==0) ? I_compareInt/* EXTERNAL */(_LD/* s1FU */, _LE/* s1FV */.a)<0 : I_compare/* EXTERNAL */(_LD/* s1FU */, _LE/* s1FV */.a)<0;
  }
},
_LF/* up_fb */ = function(_LG/* smnV */, _LH/* smnW */, _LI/* smnX */, _LJ/* smnY */, _LK/* smnZ */){
  var _LL/* smo0 */ = function(_LM/* smo1 */){
    if(!B(_L1/* GHC.Integer.Type.gtInteger */(_LM/* smo1 */, _LK/* smnZ */))){
      return new F(function(){return A2(_LG/* smnV */,_LM/* smo1 */, new T(function(){
        return B(_LL/* smo0 */(B(_Ki/* GHC.Integer.Type.plusInteger */(_LM/* smo1 */, _LJ/* smnY */))));
      }));});
    }else{
      return E(_LH/* smnW */);
    }
  };
  return new F(function(){return _LL/* smo0 */(_LI/* smnX */);});
},
_LN/* enumDeltaToIntegerFB */ = function(_LO/* smK3 */, _LP/* smK4 */, _LQ/* smK5 */, _LR/* smK6 */, _LS/* smK7 */){
  if(!B(_Lp/* GHC.Integer.Type.geInteger */(_LR/* smK6 */, _Lo/* GHC.Enum.$fEnumInteger1 */))){
    var _LT/* smK9 */ = function(_LU/* smKa */){
      if(!B(_Lx/* GHC.Integer.Type.ltInteger */(_LU/* smKa */, _LS/* smK7 */))){
        return new F(function(){return A2(_LO/* smK3 */,_LU/* smKa */, new T(function(){
          return B(_LT/* smK9 */(B(_Ki/* GHC.Integer.Type.plusInteger */(_LU/* smKa */, _LR/* smK6 */))));
        }));});
      }else{
        return E(_LP/* smK4 */);
      }
    };
    return new F(function(){return _LT/* smK9 */(_LQ/* smK5 */);});
  }else{
    return new F(function(){return _LF/* GHC.Enum.up_fb */(_LO/* smK3 */, _LP/* smK4 */, _LQ/* smK5 */, _LR/* smK6 */, _LS/* smK7 */);});
  }
},
_LV/* minBound */ = function(_LW/* smmv */){
  return E(E(_LW/* smmv */).a);
},
_LX/* minusInteger */ = function(_LY/* s1P0 */, _LZ/* s1P1 */){
  while(1){
    var _M0/* s1P2 */ = E(_LY/* s1P0 */);
    if(!_M0/* s1P2 */._){
      var _M1/* s1P3 */ = _M0/* s1P2 */.a,
      _M2/* s1P4 */ = E(_LZ/* s1P1 */);
      if(!_M2/* s1P4 */._){
        var _M3/* s1P5 */ = _M2/* s1P4 */.a,
        _M4/* s1P6 */ = subC/* EXTERNAL */(_M1/* s1P3 */, _M3/* s1P5 */);
        if(!E(_M4/* s1P6 */.b)){
          return new T1(0,_M4/* s1P6 */.a);
        }else{
          _LY/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_M1/* s1P3 */));
          _LZ/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_M3/* s1P5 */));
          continue;
        }
      }else{
        _LY/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_M1/* s1P3 */));
        _LZ/* s1P1 */ = _M2/* s1P4 */;
        continue;
      }
    }else{
      var _M5/* s1Pl */ = E(_LZ/* s1P1 */);
      if(!_M5/* s1Pl */._){
        _LY/* s1P0 */ = _M0/* s1P2 */;
        _LZ/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_M5/* s1Pl */.a));
        continue;
      }else{
        return new T1(1,I_sub/* EXTERNAL */(_M0/* s1P2 */.a, _M5/* s1Pl */.a));
      }
    }
  }
},
_M6/* integralEnumFromThen */ = function(_M7/* svk6 */, _M8/* svk7 */, _M9/* svk8 */, _Ma/* svk9 */){
  var _Mb/* svka */ = B(A2(_Lb/* GHC.Real.toInteger */,_M7/* svk6 */, _Ma/* svk9 */)),
  _Mc/* svkb */ = B(A2(_Lb/* GHC.Real.toInteger */,_M7/* svk6 */, _M9/* svk8 */));
  if(!B(_Lp/* GHC.Integer.Type.geInteger */(_Mb/* svka */, _Mc/* svkb */))){
    var _Md/* svkf */ = new T(function(){
      return B(_KZ/* GHC.Num.fromInteger */(new T(function(){
        return B(_KX/* GHC.Real.$p1Real */(new T(function(){
          return B(_KV/* GHC.Real.$p1Integral */(_M7/* svk6 */));
        })));
      })));
    }),
    _Me/* svkj */ = function(_Mf/* svkg */, _Mg/* svkh */){
      return new T2(1,new T(function(){
        return B(A1(_Md/* svkf */,_Mf/* svkg */));
      }),_Mg/* svkh */);
    };
    return new F(function(){return _LN/* GHC.Enum.enumDeltaToIntegerFB */(_Me/* svkj */, _6/* GHC.Types.[] */, _Mc/* svkb */, B(_LX/* GHC.Integer.Type.minusInteger */(_Mb/* svka */, _Mc/* svkb */)), B(A2(_Lb/* GHC.Real.toInteger */,_M7/* svk6 */, new T(function(){
      return B(_LV/* GHC.Enum.minBound */(_M8/* svk7 */));
    }))));});
  }else{
    var _Mh/* svkp */ = new T(function(){
      return B(_KZ/* GHC.Num.fromInteger */(new T(function(){
        return B(_KX/* GHC.Real.$p1Real */(new T(function(){
          return B(_KV/* GHC.Real.$p1Integral */(_M7/* svk6 */));
        })));
      })));
    }),
    _Mi/* svkt */ = function(_Mj/* svkq */, _Mk/* svkr */){
      return new T2(1,new T(function(){
        return B(A1(_Mh/* svkp */,_Mj/* svkq */));
      }),_Mk/* svkr */);
    };
    return new F(function(){return _LN/* GHC.Enum.enumDeltaToIntegerFB */(_Mi/* svkt */, _6/* GHC.Types.[] */, _Mc/* svkb */, B(_LX/* GHC.Integer.Type.minusInteger */(_Mb/* svka */, _Mc/* svkb */)), B(A2(_Lb/* GHC.Real.toInteger */,_M7/* svk6 */, new T(function(){
      return B(_L9/* GHC.Enum.maxBound */(_M8/* svk7 */));
    }))));});
  }
},
_Ml/* $fEnumInt64_$cenumFromThen */ = function(_Mm/* B2 */, _Lm/* B1 */){
  return new F(function(){return _M6/* GHC.Real.integralEnumFromThen */(_Ln/* GHC.Int.$fIntegralInt64 */, _KT/* GHC.Int.$fBoundedInt64 */, _Mm/* B2 */, _Lm/* B1 */);});
},
_Mn/* integralEnumFromThenTo */ = function(_Mo/* svjD */, _Mp/* svjE */, _Mq/* svjF */, _Mr/* svjG */){
  var _Ms/* svjH */ = B(A2(_Lb/* GHC.Real.toInteger */,_Mo/* svjD */, _Mp/* svjE */)),
  _Mt/* svjK */ = new T(function(){
    return B(_KZ/* GHC.Num.fromInteger */(new T(function(){
      return B(_KX/* GHC.Real.$p1Real */(new T(function(){
        return B(_KV/* GHC.Real.$p1Integral */(_Mo/* svjD */));
      })));
    })));
  }),
  _Mu/* svjO */ = function(_Mv/* svjL */, _Mw/* svjM */){
    return new T2(1,new T(function(){
      return B(A1(_Mt/* svjK */,_Mv/* svjL */));
    }),_Mw/* svjM */);
  };
  return new F(function(){return _LN/* GHC.Enum.enumDeltaToIntegerFB */(_Mu/* svjO */, _6/* GHC.Types.[] */, _Ms/* svjH */, B(_LX/* GHC.Integer.Type.minusInteger */(B(A2(_Lb/* GHC.Real.toInteger */,_Mo/* svjD */, _Mq/* svjF */)), _Ms/* svjH */)), B(A2(_Lb/* GHC.Real.toInteger */,_Mo/* svjD */, _Mr/* svjG */)));});
},
_Mx/* $fEnumInt64_$cenumFromThenTo */ = function(_My/* B3 */, _Mm/* B2 */, _Lm/* B1 */){
  return new F(function(){return _Mn/* GHC.Real.integralEnumFromThenTo */(_Ln/* GHC.Int.$fIntegralInt64 */, _My/* B3 */, _Mm/* B2 */, _Lm/* B1 */);});
},
_Mz/* integralEnumFromTo */ = function(_MA/* svjS */, _MB/* svjT */, _MC/* svjU */){
  var _MD/* svjX */ = new T(function(){
    return B(_KZ/* GHC.Num.fromInteger */(new T(function(){
      return B(_KX/* GHC.Real.$p1Real */(new T(function(){
        return B(_KV/* GHC.Real.$p1Integral */(_MA/* svjS */));
      })));
    })));
  }),
  _ME/* svjZ */ = function(_MF/* svk0 */){
    return (!B(_L1/* GHC.Integer.Type.gtInteger */(_MF/* svk0 */, B(A2(_Lb/* GHC.Real.toInteger */,_MA/* svjS */, _MC/* svjU */))))) ? new T2(1,new T(function(){
      return B(A1(_MD/* svjX */,_MF/* svk0 */));
    }),new T(function(){
      return B(_ME/* svjZ */(B(_Ki/* GHC.Integer.Type.plusInteger */(_MF/* svk0 */, _KU/* GHC.Real.$fEnumRatio1 */))));
    })) : __Z/* EXTERNAL */;
  };
  return new F(function(){return _ME/* svjZ */(B(A2(_Lb/* GHC.Real.toInteger */,_MA/* svjS */, _MB/* svjT */)));});
},
_MG/* $fEnumInt64_$cenumFromTo */ = function(_Mm/* B2 */, _Lm/* B1 */){
  return new F(function(){return _Mz/* GHC.Real.integralEnumFromTo */(_Ln/* GHC.Int.$fIntegralInt64 */, _Mm/* B2 */, _Lm/* B1 */);});
},
_MH/* $fEnumInt6 */ = new T(function(){
  return hs_intToInt64/* EXTERNAL */(2147483647);
}),
_MI/* smallInteger */ = function(_MJ/* B1 */){
  return new T1(0,_MJ/* B1 */);
},
_MK/* int64ToInteger */ = function(_ML/* s1RA */){
  var _MM/* s1RC */ = hs_intToInt64/* EXTERNAL */(2147483647),
  _MN/* s1RG */ = hs_leInt64/* EXTERNAL */(_ML/* s1RA */, _MM/* s1RC */);
  if(!_MN/* s1RG */){
    return new T1(1,I_fromInt64/* EXTERNAL */(_ML/* s1RA */));
  }else{
    var _MO/* s1RN */ = hs_intToInt64/* EXTERNAL */(-2147483648),
    _MP/* s1RR */ = hs_geInt64/* EXTERNAL */(_ML/* s1RA */, _MO/* s1RN */);
    if(!_MP/* s1RR */){
      return new T1(1,I_fromInt64/* EXTERNAL */(_ML/* s1RA */));
    }else{
      var _MQ/* s1RY */ = hs_int64ToInt/* EXTERNAL */(_ML/* s1RA */);
      return new F(function(){return _MI/* GHC.Integer.Type.smallInteger */(_MQ/* s1RY */);});
    }
  }
},
_MR/* $fIntegralInt64_$ctoInteger */ = function(_MS/* s2dYm */){
  return new F(function(){return _MK/* GHC.Integer.Type.int64ToInteger */(E(_MS/* s2dYm */));});
},
_MT/* integerToJSString */ = function(_MU/* s1Iv */){
  while(1){
    var _MV/* s1Iw */ = E(_MU/* s1Iv */);
    if(!_MV/* s1Iw */._){
      _MU/* s1Iv */ = new T1(1,I_fromInt/* EXTERNAL */(_MV/* s1Iw */.a));
      continue;
    }else{
      return new F(function(){return I_toString/* EXTERNAL */(_MV/* s1Iw */.a);});
    }
  }
},
_MW/* integerToString */ = function(_MX/* sfbi */, _MY/* sfbj */){
  return new F(function(){return _2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_MT/* GHC.Integer.Type.integerToJSString */(_MX/* sfbi */))), _MY/* sfbj */);});
},
_MZ/* shows9 */ = new T1(0,0),
_N0/* $w$cshowsPrec1 */ = function(_N1/* sfcx */, _N2/* sfcy */, _N3/* sfcz */){
  if(_N1/* sfcx */<=6){
    return new F(function(){return _MW/* GHC.Show.integerToString */(_N2/* sfcy */, _N3/* sfcz */);});
  }else{
    if(!B(_Lx/* GHC.Integer.Type.ltInteger */(_N2/* sfcy */, _MZ/* GHC.Show.shows9 */))){
      return new F(function(){return _MW/* GHC.Show.integerToString */(_N2/* sfcy */, _N3/* sfcz */);});
    }else{
      return new T2(1,_3c/* GHC.Show.shows8 */,new T(function(){
        return B(_2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_MT/* GHC.Integer.Type.integerToJSString */(_N2/* sfcy */))), new T2(1,_3b/* GHC.Show.shows7 */,_N3/* sfcz */)));
      }));
    }
  }
},
_N4/* $fShowInt64_$cshow */ = function(_N5/* s2dYy */){
  return new F(function(){return _N0/* GHC.Show.$w$cshowsPrec1 */(0, B(_MR/* GHC.Int.$fIntegralInt64_$ctoInteger */(_N5/* s2dYy */)), _6/* GHC.Types.[] */);});
},
_N6/* $fShowInt3 */ = function(_N7/* s2dYA */, _N8/* s2dYB */){
  return new F(function(){return _N0/* GHC.Show.$w$cshowsPrec1 */(0, B(_MK/* GHC.Integer.Type.int64ToInteger */(E(_N7/* s2dYA */))), _N8/* s2dYB */);});
},
_N9/* $fShowInt64_$cshowList */ = function(_Na/* s2dYF */, _Nb/* s2dYG */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_N6/* GHC.Int.$fShowInt3 */, _Na/* s2dYF */, _Nb/* s2dYG */);});
},
_Nc/* $fShowInt64_$cshowsPrec */ = function(_Nd/* s2dYp */, _Ne/* s2dYq */){
  var _Nf/* s2dYr */ = new T(function(){
    return B(_MK/* GHC.Integer.Type.int64ToInteger */(E(_Ne/* s2dYq */)));
  });
  return function(_Ng/* s2dYu */){
    return new F(function(){return _N0/* GHC.Show.$w$cshowsPrec1 */(E(_Nd/* s2dYp */), _Nf/* s2dYr */, _Ng/* s2dYu */);});
  };
},
_Nh/* $fShowInt64 */ = new T3(0,_Nc/* GHC.Int.$fShowInt64_$cshowsPrec */,_N4/* GHC.Int.$fShowInt64_$cshow */,_N9/* GHC.Int.$fShowInt64_$cshowList */),
_Ni/* lvl */ = new T2(1,_3b/* GHC.Show.shows7 */,_6/* GHC.Types.[] */),
_Nj/* $fShow(,)1 */ = function(_Nk/* sfg4 */, _Nl/* sfg5 */, _Nm/* sfg6 */){
  return new F(function(){return A1(_Nk/* sfg4 */,new T2(1,_23/* GHC.Show.showList__1 */,new T(function(){
    return B(A1(_Nl/* sfg5 */,_Nm/* sfg6 */));
  })));});
},
_Nn/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_No/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_Np/* errorEmptyList */ = function(_Nq/* s9t7 */){
  return new F(function(){return err/* EXTERNAL */(B(_2/* GHC.Base.++ */(_No/* GHC.List.prel_list_str */, new T(function(){
    return B(_2/* GHC.Base.++ */(_Nq/* s9t7 */, _Nn/* GHC.List.lvl */));
  },1))));});
},
_Nr/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("foldr1"));
}),
_Ns/* lvl8 */ = new T(function(){
  return B(_Np/* GHC.List.errorEmptyList */(_Nr/* GHC.List.lvl7 */));
}),
_Nt/* foldr1 */ = function(_Nu/* s9Ah */, _Nv/* s9Ai */){
  var _Nw/* s9Aj */ = E(_Nv/* s9Ai */);
  if(!_Nw/* s9Aj */._){
    return E(_Ns/* GHC.List.lvl8 */);
  }else{
    var _Nx/* s9Ak */ = _Nw/* s9Aj */.a,
    _Ny/* s9Am */ = E(_Nw/* s9Aj */.b);
    if(!_Ny/* s9Am */._){
      return E(_Nx/* s9Ak */);
    }else{
      return new F(function(){return A2(_Nu/* s9Ah */,_Nx/* s9Ak */, new T(function(){
        return B(_Nt/* GHC.List.foldr1 */(_Nu/* s9Ah */, _Ny/* s9Am */));
      }));});
    }
  }
},
_Nz/* lvl14 */ = function(_NA/* smEb */){
  return new F(function(){return _3d/* GHC.Show.$wshowSignedInt */(0, -2147483648, _NA/* smEb */);});
},
_NB/* lvl15 */ = function(_NC/* smEc */){
  return new F(function(){return _3d/* GHC.Show.$wshowSignedInt */(0, 2147483647, _NC/* smEc */);});
},
_ND/* lvl16 */ = new T2(1,_NB/* GHC.Enum.lvl15 */,_6/* GHC.Types.[] */),
_NE/* lvl17 */ = new T2(1,_Nz/* GHC.Enum.lvl14 */,_ND/* GHC.Enum.lvl16 */),
_NF/* lvl18 */ = new T(function(){
  return B(_Nt/* GHC.List.foldr1 */(_Nj/* GHC.Show.$fShow(,)1 */, _NE/* GHC.Enum.lvl17 */));
}),
_NG/* lvl19 */ = new T(function(){
  return B(A1(_NF/* GHC.Enum.lvl18 */,_Ni/* GHC.Enum.lvl */));
}),
_NH/* lvl20 */ = new T2(1,_3c/* GHC.Show.shows8 */,_NG/* GHC.Enum.lvl19 */),
_NI/* lvl21 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */(") is outside of Int\'s bounds ", _NH/* GHC.Enum.lvl20 */));
}),
_NJ/* show */ = function(_NK/* sfb3 */){
  return E(E(_NK/* sfb3 */).b);
},
_NL/* lvl22 */ = function(_NM/* smEd */, _NN/* smEe */, _NO/* smEf */){
  var _NP/* smEj */ = new T(function(){
    var _NQ/* smEi */ = new T(function(){
      return B(unAppCStr/* EXTERNAL */("}: value (", new T(function(){
        return B(_2/* GHC.Base.++ */(B(A2(_NJ/* GHC.Show.show */,_NO/* smEf */, _NN/* smEe */)), _NI/* GHC.Enum.lvl21 */));
      })));
    },1);
    return B(_2/* GHC.Base.++ */(_NM/* smEd */, _NQ/* smEi */));
  });
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.fromEnum{", _NP/* smEj */)));});
},
_NR/* fromEnumError */ = function(_NS/* smEl */, _NT/* smEm */, _NU/* smEn */){
  return new F(function(){return _NL/* GHC.Enum.lvl22 */(_NT/* smEm */, _NU/* smEn */, _NS/* smEl */);});
},
_NV/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Int64"));
}),
_NW/* lvl13 */ = function(_NX/* s2dYH */){
  return new F(function(){return _NR/* GHC.Enum.fromEnumError */(_Nh/* GHC.Int.$fShowInt64 */, _NV/* GHC.Int.lvl1 */, _NX/* s2dYH */);});
},
_NY/* $fEnumInt7 */ = function(_NZ/* s2dYI */){
  return new F(function(){return _NW/* GHC.Int.lvl13 */(_NZ/* s2dYI */);});
},
_O0/* $fEnumInt9 */ = new T(function(){
  return hs_intToInt64/* EXTERNAL */(-2147483648);
}),
_O1/* $w$cfromEnum */ = function(_O2/* s2dYK */){
  var _O3/* s2dYO */ = hs_geInt64/* EXTERNAL */(_O2/* s2dYK */, E(_O0/* GHC.Int.$fEnumInt9 */));
  if(!_O3/* s2dYO */){
    return new F(function(){return _NY/* GHC.Int.$fEnumInt7 */(_O2/* s2dYK */);});
  }else{
    var _O4/* s2dYW */ = hs_leInt64/* EXTERNAL */(_O2/* s2dYK */, E(_MH/* GHC.Int.$fEnumInt6 */));
    if(!_O4/* s2dYW */){
      return new F(function(){return _NY/* GHC.Int.$fEnumInt7 */(_O2/* s2dYK */);});
    }else{
      var _O5/* s2dZ2 */ = hs_int64ToInt/* EXTERNAL */(_O2/* s2dYK */);
      return E(_O5/* s2dZ2 */);
    }
  }
},
_O6/* $fEnumInt64_$cfromEnum */ = function(_O7/* s2dZ5 */){
  return new F(function(){return _O1/* GHC.Int.$w$cfromEnum */(E(_O7/* s2dZ5 */));});
},
_O8/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}: tried to take `pred\' of minBound"));
}),
_O9/* lvl2 */ = function(_Oa/* smrD */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.pred{", new T(function(){
    return B(_2/* GHC.Base.++ */(_Oa/* smrD */, _O8/* GHC.Enum.lvl1 */));
  }))));});
},
_Ob/* predError */ = function(_Oc/* B1 */){
  return new F(function(){return _O9/* GHC.Enum.lvl2 */(_Oc/* B1 */);});
},
_Od/* $fEnumInt10 */ = new T(function(){
  return B(_Ob/* GHC.Enum.predError */(_NV/* GHC.Int.lvl1 */));
}),
_Oe/* $w$cpred */ = function(_Of/* s2dXS */){
  var _Og/* s2dXU */ = hs_neInt64/* EXTERNAL */(_Of/* s2dXS */, new Long/* EXTERNAL */(0, -2147483648));
  if(!_Og/* s2dXU */){
    return E(_Od/* GHC.Int.$fEnumInt10 */);
  }else{
    var _Oh/* s2dY0 */ = hs_minusInt64/* EXTERNAL */(_Of/* s2dXS */, new Long/* EXTERNAL */(1, 0));
    return E(_Oh/* s2dY0 */);
  }
},
_Oi/* $fEnumInt64_$cpred */ = function(_Oj/* s2dY3 */){
  return new F(function(){return _Oe/* GHC.Int.$w$cpred */(E(_Oj/* s2dY3 */));});
},
_Ok/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}: tried to take `succ\' of maxBound"));
}),
_Ol/* lvl4 */ = function(_Om/* smrG */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.succ{", new T(function(){
    return B(_2/* GHC.Base.++ */(_Om/* smrG */, _Ok/* GHC.Enum.lvl3 */));
  }))));});
},
_On/* succError */ = function(_Oc/* B1 */){
  return new F(function(){return _Ol/* GHC.Enum.lvl4 */(_Oc/* B1 */);});
},
_Oo/* $fEnumInt11 */ = new T(function(){
  return B(_On/* GHC.Enum.succError */(_NV/* GHC.Int.lvl1 */));
}),
_Op/* $w$csucc */ = function(_Oq/* s2dY7 */){
  var _Or/* s2dY9 */ = hs_neInt64/* EXTERNAL */(_Oq/* s2dY7 */, new Long/* EXTERNAL */(4294967295, 2147483647));
  if(!_Or/* s2dY9 */){
    return E(_Oo/* GHC.Int.$fEnumInt11 */);
  }else{
    var _Os/* s2dYf */ = hs_plusInt64/* EXTERNAL */(_Oq/* s2dY7 */, new Long/* EXTERNAL */(1, 0));
    return E(_Os/* s2dYf */);
  }
},
_Ot/* $fEnumInt64_$csucc */ = function(_Ou/* s2dYi */){
  return new F(function(){return _Op/* GHC.Int.$w$csucc */(E(_Ou/* s2dYi */));});
},
_Ov/* $fEnumInt64_$ctoEnum */ = function(_Ow/* s2dXL */){
  return new F(function(){return hs_intToInt64/* EXTERNAL */(E(_Ow/* s2dXL */));});
},
_Ox/* $fEnumInt64 */ = new T(function(){
  return {_:0,a:_Ot/* GHC.Int.$fEnumInt64_$csucc */,b:_Oi/* GHC.Int.$fEnumInt64_$cpred */,c:_Ov/* GHC.Int.$fEnumInt64_$ctoEnum */,d:_O6/* GHC.Int.$fEnumInt64_$cfromEnum */,e:_Ll/* GHC.Int.$fEnumInt64_$cenumFrom */,f:_Ml/* GHC.Int.$fEnumInt64_$cenumFromThen */,g:_MG/* GHC.Int.$fEnumInt64_$cenumFromTo */,h:_Mx/* GHC.Int.$fEnumInt64_$cenumFromThenTo */};
}),
_Oy/* minusInt64# */ = function(_Oz/* sdC */, _OA/* sdD */){
  var _OB/* sdF */ = hs_minusInt64/* EXTERNAL */(_Oz/* sdC */, _OA/* sdD */);
  return E(_OB/* sdF */);
},
_OC/* quotInt64# */ = function(_OD/* sdk */, _OE/* sdl */){
  var _OF/* sdn */ = hs_quotInt64/* EXTERNAL */(_OD/* sdk */, _OE/* sdl */);
  return E(_OF/* sdn */);
},
_OG/* divInt64# */ = function(_OH/* s2dwk */, _OI/* s2dwl */){
  var _OJ/* s2dwn */ = hs_intToInt64/* EXTERNAL */(1),
  _OK/* s2dwp */ = _OJ/* s2dwn */,
  _OL/* s2dwr */ = hs_intToInt64/* EXTERNAL */(0),
  _OM/* s2dwt */ = _OL/* s2dwr */,
  _ON/* s2dwv */ = hs_gtInt64/* EXTERNAL */(_OH/* s2dwk */, _OM/* s2dwt */),
  _OO/* s2dwy */ = function(_OP/* s2dwz */){
    var _OQ/* s2dwB */ = hs_ltInt64/* EXTERNAL */(_OH/* s2dwk */, _OM/* s2dwt */);
    if(!_OQ/* s2dwB */){
      return new F(function(){return _OC/* GHC.IntWord64.quotInt64# */(_OH/* s2dwk */, _OI/* s2dwl */);});
    }else{
      var _OR/* s2dwG */ = hs_gtInt64/* EXTERNAL */(_OI/* s2dwl */, _OM/* s2dwt */);
      if(!_OR/* s2dwG */){
        return new F(function(){return _OC/* GHC.IntWord64.quotInt64# */(_OH/* s2dwk */, _OI/* s2dwl */);});
      }else{
        var _OS/* s2dwL */ = hs_plusInt64/* EXTERNAL */(_OH/* s2dwk */, _OK/* s2dwp */),
        _OT/* s2dwP */ = hs_quotInt64/* EXTERNAL */(_OS/* s2dwL */, _OI/* s2dwl */);
        return new F(function(){return _Oy/* GHC.IntWord64.minusInt64# */(_OT/* s2dwP */, _OK/* s2dwp */);});
      }
    }
  };
  if(!_ON/* s2dwv */){
    return new F(function(){return _OO/* s2dwy */(_/* EXTERNAL */);});
  }else{
    var _OU/* s2dwU */ = hs_ltInt64/* EXTERNAL */(_OI/* s2dwl */, _OM/* s2dwt */);
    if(!_OU/* s2dwU */){
      return new F(function(){return _OO/* s2dwy */(_/* EXTERNAL */);});
    }else{
      var _OV/* s2dwZ */ = hs_minusInt64/* EXTERNAL */(_OH/* s2dwk */, _OK/* s2dwp */),
      _OW/* s2dx3 */ = hs_quotInt64/* EXTERNAL */(_OV/* s2dwZ */, _OI/* s2dwl */);
      return new F(function(){return _Oy/* GHC.IntWord64.minusInt64# */(_OW/* s2dx3 */, _OK/* s2dwp */);});
    }
  }
},
_OX/* $fExceptionArithException_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_OY/* $fExceptionArithException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.Exception"));
}),
_OZ/* $fExceptionArithException_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ArithException"));
}),
_P0/* $fExceptionArithException_wild */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_OX/* GHC.Exception.$fExceptionArithException_ww2 */,_OY/* GHC.Exception.$fExceptionArithException_ww4 */,_OZ/* GHC.Exception.$fExceptionArithException_ww5 */),
_P1/* $fExceptionArithException8 */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_P0/* GHC.Exception.$fExceptionArithException_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_P2/* $fExceptionArithException7 */ = function(_P3/* s2S2z */){
  return E(_P1/* GHC.Exception.$fExceptionArithException8 */);
},
_P4/* $fExceptionArithException_$cfromException */ = function(_P5/* s2S35 */){
  var _P6/* s2S36 */ = E(_P5/* s2S35 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_P6/* s2S36 */.a)), _P2/* GHC.Exception.$fExceptionArithException7 */, _P6/* s2S36 */.b);});
},
_P7/* $fExceptionArithException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ratio has zero denominator"));
}),
_P8/* $fExceptionArithException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("denormal"));
}),
_P9/* $fExceptionArithException3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("divide by zero"));
}),
_Pa/* $fExceptionArithException4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("loss of precision"));
}),
_Pb/* $fExceptionArithException5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic underflow"));
}),
_Pc/* $fExceptionArithException6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic overflow"));
}),
_Pd/* $w$cshowsPrec */ = function(_Pe/* s2S3a */, _Pf/* s2S3b */){
  switch(E(_Pe/* s2S3a */)){
    case 0:
      return new F(function(){return _2/* GHC.Base.++ */(_Pc/* GHC.Exception.$fExceptionArithException6 */, _Pf/* s2S3b */);});
      break;
    case 1:
      return new F(function(){return _2/* GHC.Base.++ */(_Pb/* GHC.Exception.$fExceptionArithException5 */, _Pf/* s2S3b */);});
      break;
    case 2:
      return new F(function(){return _2/* GHC.Base.++ */(_Pa/* GHC.Exception.$fExceptionArithException4 */, _Pf/* s2S3b */);});
      break;
    case 3:
      return new F(function(){return _2/* GHC.Base.++ */(_P9/* GHC.Exception.$fExceptionArithException3 */, _Pf/* s2S3b */);});
      break;
    case 4:
      return new F(function(){return _2/* GHC.Base.++ */(_P8/* GHC.Exception.$fExceptionArithException2 */, _Pf/* s2S3b */);});
      break;
    default:
      return new F(function(){return _2/* GHC.Base.++ */(_P7/* GHC.Exception.$fExceptionArithException1 */, _Pf/* s2S3b */);});
  }
},
_Pg/* $fExceptionArithException_$cshow */ = function(_Ph/* s2S3g */){
  return new F(function(){return _Pd/* GHC.Exception.$w$cshowsPrec */(_Ph/* s2S3g */, _6/* GHC.Types.[] */);});
},
_Pi/* $fExceptionArithException_$cshowsPrec */ = function(_Pj/* s2S3d */, _Pk/* s2S3e */, _Pl/* s2S3f */){
  return new F(function(){return _Pd/* GHC.Exception.$w$cshowsPrec */(_Pk/* s2S3e */, _Pl/* s2S3f */);});
},
_Pm/* $fShowArithException_$cshowList */ = function(_Pn/* s2S3h */, _Po/* s2S3i */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_Pd/* GHC.Exception.$w$cshowsPrec */, _Pn/* s2S3h */, _Po/* s2S3i */);});
},
_Pp/* $fShowArithException */ = new T3(0,_Pi/* GHC.Exception.$fExceptionArithException_$cshowsPrec */,_Pg/* GHC.Exception.$fExceptionArithException_$cshow */,_Pm/* GHC.Exception.$fShowArithException_$cshowList */),
_Pq/* $fExceptionArithException */ = new T(function(){
  return new T5(0,_P2/* GHC.Exception.$fExceptionArithException7 */,_Pp/* GHC.Exception.$fShowArithException */,_Pr/* GHC.Exception.$fExceptionArithException_$ctoException */,_P4/* GHC.Exception.$fExceptionArithException_$cfromException */,_Pg/* GHC.Exception.$fExceptionArithException_$cshow */);
}),
_Pr/* $fExceptionArithException_$ctoException */ = function(_Ps/* B1 */){
  return new T2(0,_Pq/* GHC.Exception.$fExceptionArithException */,_Ps/* B1 */);
},
_Pt/* DivideByZero */ = 3,
_Pu/* divZeroException */ = new T(function(){
  return B(_Pr/* GHC.Exception.$fExceptionArithException_$ctoException */(_Pt/* GHC.Exception.DivideByZero */));
}),
_Pv/* divZeroError */ = new T(function(){
  return die/* EXTERNAL */(_Pu/* GHC.Exception.divZeroException */);
}),
_Pw/* Overflow */ = 0,
_Px/* overflowException */ = new T(function(){
  return B(_Pr/* GHC.Exception.$fExceptionArithException_$ctoException */(_Pw/* GHC.Exception.Overflow */));
}),
_Py/* overflowError */ = new T(function(){
  return die/* EXTERNAL */(_Px/* GHC.Exception.overflowException */);
}),
_Pz/* $w$cdiv2 */ = function(_PA/* s2e0N */, _PB/* s2e0O */){
  var _PC/* s2e0Q */ = hs_eqInt64/* EXTERNAL */(_PB/* s2e0O */, new Long/* EXTERNAL */(0, 0));
  if(!_PC/* s2e0Q */){
    var _PD/* s2e0V */ = hs_eqInt64/* EXTERNAL */(_PB/* s2e0O */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_PD/* s2e0V */){
      return new F(function(){return _OG/* GHC.Int.divInt64# */(_PA/* s2e0N */, _PB/* s2e0O */);});
    }else{
      var _PE/* s2e10 */ = hs_eqInt64/* EXTERNAL */(_PA/* s2e0N */, new Long/* EXTERNAL */(0, -2147483648));
      if(!_PE/* s2e10 */){
        return new F(function(){return _OG/* GHC.Int.divInt64# */(_PA/* s2e0N */, _PB/* s2e0O */);});
      }else{
        return E(_Py/* GHC.Real.overflowError */);
      }
    }
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_PF/* $fIntegralInt64_$cdiv */ = function(_PG/* s2e16 */, _PH/* s2e17 */){
  return new F(function(){return _Pz/* GHC.Int.$w$cdiv2 */(E(_PG/* s2e16 */), E(_PH/* s2e17 */));});
},
_PI/* $fIntegralInt1 */ = new Long/* EXTERNAL */(0, 0),
_PJ/* plusInt64# */ = function(_PK/* sdw */, _PL/* sdx */){
  var _PM/* sdz */ = hs_plusInt64/* EXTERNAL */(_PK/* sdw */, _PL/* sdx */);
  return E(_PM/* sdz */);
},
_PN/* modInt64# */ = function(_PO/* s2dvH */, _PP/* s2dvI */){
  var _PQ/* s2dvK */ = hs_remInt64/* EXTERNAL */(_PO/* s2dvH */, _PP/* s2dvI */),
  _PR/* s2dvM */ = _PQ/* s2dvK */,
  _PS/* s2dvO */ = hs_intToInt64/* EXTERNAL */(0),
  _PT/* s2dvQ */ = _PS/* s2dvO */,
  _PU/* s2dvS */ = hs_gtInt64/* EXTERNAL */(_PO/* s2dvH */, _PT/* s2dvQ */),
  _PV/* s2dvV */ = function(_PW/* s2dvW */){
    var _PX/* s2dvY */ = hs_neInt64/* EXTERNAL */(_PR/* s2dvM */, _PT/* s2dvQ */);
    if(!_PX/* s2dvY */){
      return E(_PT/* s2dvQ */);
    }else{
      return new F(function(){return _PJ/* GHC.IntWord64.plusInt64# */(_PR/* s2dvM */, _PP/* s2dvI */);});
    }
  },
  _PY/* s2dw2 */ = function(_PZ/* s2dw3 */){
    var _Q0/* s2dw5 */ = hs_ltInt64/* EXTERNAL */(_PO/* s2dvH */, _PT/* s2dvQ */);
    if(!_Q0/* s2dw5 */){
      return E(_PR/* s2dvM */);
    }else{
      var _Q1/* s2dwa */ = hs_gtInt64/* EXTERNAL */(_PP/* s2dvI */, _PT/* s2dvQ */);
      if(!_Q1/* s2dwa */){
        return E(_PR/* s2dvM */);
      }else{
        return new F(function(){return _PV/* s2dvV */(_/* EXTERNAL */);});
      }
    }
  };
  if(!_PU/* s2dvS */){
    return new F(function(){return _PY/* s2dw2 */(_/* EXTERNAL */);});
  }else{
    var _Q2/* s2dwg */ = hs_ltInt64/* EXTERNAL */(_PP/* s2dvI */, _PT/* s2dvQ */);
    if(!_Q2/* s2dwg */){
      return new F(function(){return _PY/* s2dw2 */(_/* EXTERNAL */);});
    }else{
      return new F(function(){return _PV/* s2dvV */(_/* EXTERNAL */);});
    }
  }
},
_Q3/* $w$cdivMod2 */ = function(_Q4/* s2dZ9 */, _Q5/* s2dZa */){
  var _Q6/* s2dZc */ = hs_eqInt64/* EXTERNAL */(_Q5/* s2dZa */, new Long/* EXTERNAL */(0, 0));
  if(!_Q6/* s2dZc */){
    var _Q7/* s2dZh */ = hs_eqInt64/* EXTERNAL */(_Q5/* s2dZa */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Q7/* s2dZh */){
      return new T2(0,new T(function(){
        return B(_OG/* GHC.Int.divInt64# */(_Q4/* s2dZ9 */, _Q5/* s2dZa */));
      }),new T(function(){
        return B(_PN/* GHC.Int.modInt64# */(_Q4/* s2dZ9 */, _Q5/* s2dZa */));
      }));
    }else{
      var _Q8/* s2dZq */ = hs_eqInt64/* EXTERNAL */(_Q4/* s2dZ9 */, new Long/* EXTERNAL */(0, -2147483648));
      return (!_Q8/* s2dZq */) ? new T2(0,new T(function(){
        return B(_OG/* GHC.Int.divInt64# */(_Q4/* s2dZ9 */, _Q5/* s2dZa */));
      }),new T(function(){
        return B(_PN/* GHC.Int.modInt64# */(_Q4/* s2dZ9 */, _Q5/* s2dZa */));
      })) : new T2(0,_Py/* GHC.Real.overflowError */,_PI/* GHC.Int.$fIntegralInt1 */);
    }
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_Q9/* $fIntegralInt64_$cdivMod */ = function(_Qa/* s2dZz */, _Qb/* s2dZA */){
  var _Qc/* s2dZF */ = B(_Q3/* GHC.Int.$w$cdivMod2 */(E(_Qa/* s2dZz */), E(_Qb/* s2dZA */)));
  return new T2(0,_Qc/* s2dZF */.a,_Qc/* s2dZF */.b);
},
_Qd/* $w$cmod */ = function(_Qe/* s2e0t */, _Qf/* s2e0u */){
  var _Qg/* s2e0w */ = hs_eqInt64/* EXTERNAL */(_Qf/* s2e0u */, new Long/* EXTERNAL */(0, 0));
  if(!_Qg/* s2e0w */){
    var _Qh/* s2e0B */ = hs_eqInt64/* EXTERNAL */(_Qf/* s2e0u */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Qh/* s2e0B */){
      return new F(function(){return _PN/* GHC.Int.modInt64# */(_Qe/* s2e0t */, _Qf/* s2e0u */);});
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_Qi/* $fIntegralInt64_$cmod */ = function(_Qj/* s2e0G */, _Qk/* s2e0H */){
  return new F(function(){return _Qd/* GHC.Int.$w$cmod */(E(_Qj/* s2e0G */), E(_Qk/* s2e0H */));});
},
_Ql/* $w$cquot */ = function(_Qm/* s2e1B */, _Qn/* s2e1C */){
  var _Qo/* s2e1E */ = hs_eqInt64/* EXTERNAL */(_Qn/* s2e1C */, new Long/* EXTERNAL */(0, 0));
  if(!_Qo/* s2e1E */){
    var _Qp/* s2e1J */ = hs_eqInt64/* EXTERNAL */(_Qn/* s2e1C */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Qp/* s2e1J */){
      var _Qq/* s2e1O */ = hs_quotInt64/* EXTERNAL */(_Qm/* s2e1B */, _Qn/* s2e1C */);
      return E(_Qq/* s2e1O */);
    }else{
      var _Qr/* s2e1S */ = hs_eqInt64/* EXTERNAL */(_Qm/* s2e1B */, new Long/* EXTERNAL */(0, -2147483648));
      if(!_Qr/* s2e1S */){
        var _Qs/* s2e1X */ = hs_quotInt64/* EXTERNAL */(_Qm/* s2e1B */, _Qn/* s2e1C */);
        return E(_Qs/* s2e1X */);
      }else{
        return E(_Py/* GHC.Real.overflowError */);
      }
    }
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_Qt/* $fIntegralInt64_$cquot */ = function(_Qu/* s2e22 */, _Qv/* s2e23 */){
  return new F(function(){return _Ql/* GHC.Int.$w$cquot */(E(_Qu/* s2e22 */), E(_Qv/* s2e23 */));});
},
_Qw/* $w$cquotRem */ = function(_Qx/* s2dZI */, _Qy/* s2dZJ */){
  var _Qz/* s2dZL */ = hs_eqInt64/* EXTERNAL */(_Qy/* s2dZJ */, new Long/* EXTERNAL */(0, 0));
  if(!_Qz/* s2dZL */){
    var _QA/* s2dZQ */ = hs_eqInt64/* EXTERNAL */(_Qy/* s2dZJ */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_QA/* s2dZQ */){
      return new T2(0,new T(function(){
        return hs_quotInt64/* EXTERNAL */(_Qx/* s2dZI */, _Qy/* s2dZJ */);
      }),new T(function(){
        return hs_remInt64/* EXTERNAL */(_Qx/* s2dZI */, _Qy/* s2dZJ */);
      }));
    }else{
      var _QB/* s2e05 */ = hs_eqInt64/* EXTERNAL */(_Qx/* s2dZI */, new Long/* EXTERNAL */(0, -2147483648));
      return (!_QB/* s2e05 */) ? new T2(0,new T(function(){
        return hs_quotInt64/* EXTERNAL */(_Qx/* s2dZI */, _Qy/* s2dZJ */);
      }),new T(function(){
        return hs_remInt64/* EXTERNAL */(_Qx/* s2dZI */, _Qy/* s2dZJ */);
      })) : new T2(0,_Py/* GHC.Real.overflowError */,_PI/* GHC.Int.$fIntegralInt1 */);
    }
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_QC/* $fIntegralInt64_$cquotRem */ = function(_QD/* s2e0k */, _QE/* s2e0l */){
  var _QF/* s2e0q */ = B(_Qw/* GHC.Int.$w$cquotRem */(E(_QD/* s2e0k */), E(_QE/* s2e0l */)));
  return new T2(0,_QF/* s2e0q */.a,_QF/* s2e0q */.b);
},
_QG/* $w$crem */ = function(_QH/* s2e1d */, _QI/* s2e1e */){
  var _QJ/* s2e1g */ = hs_eqInt64/* EXTERNAL */(_QI/* s2e1e */, new Long/* EXTERNAL */(0, 0));
  if(!_QJ/* s2e1g */){
    var _QK/* s2e1l */ = hs_eqInt64/* EXTERNAL */(_QI/* s2e1e */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_QK/* s2e1l */){
      var _QL/* s2e1q */ = hs_remInt64/* EXTERNAL */(_QH/* s2e1d */, _QI/* s2e1e */);
      return E(_QL/* s2e1q */);
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_QM/* $fIntegralInt64_$crem */ = function(_QN/* s2e1u */, _QO/* s2e1v */){
  return new F(function(){return _QG/* GHC.Int.$w$crem */(E(_QN/* s2e1u */), E(_QO/* s2e1v */));});
},
_QP/* $fBitsInt64_$c/= */ = function(_QQ/* s2dV3 */, _QR/* s2dV4 */){
  return new F(function(){return hs_neInt64/* EXTERNAL */(E(_QQ/* s2dV3 */), E(_QR/* s2dV4 */));});
},
_QS/* $fEqInt64_$c== */ = function(_QT/* s2dVd */, _QU/* s2dVe */){
  return new F(function(){return hs_eqInt64/* EXTERNAL */(E(_QT/* s2dVd */), E(_QU/* s2dVe */));});
},
_QV/* $fEqInt64 */ = new T2(0,_QS/* GHC.Int.$fEqInt64_$c== */,_QP/* GHC.Int.$fBitsInt64_$c/= */),
_QW/* $fOrdInt64_$c< */ = function(_QX/* s2dWd */, _QY/* s2dWe */){
  return new F(function(){return hs_ltInt64/* EXTERNAL */(E(_QX/* s2dWd */), E(_QY/* s2dWe */));});
},
_QZ/* $fOrdInt64_$c<= */ = function(_R0/* s2dW3 */, _R1/* s2dW4 */){
  return new F(function(){return hs_leInt64/* EXTERNAL */(E(_R0/* s2dW3 */), E(_R1/* s2dW4 */));});
},
_R2/* $fOrdInt64_$c> */ = function(_R3/* s2dVT */, _R4/* s2dVU */){
  return new F(function(){return hs_gtInt64/* EXTERNAL */(E(_R3/* s2dVT */), E(_R4/* s2dVU */));});
},
_R5/* $fOrdInt64_$c>= */ = function(_R6/* s2dVJ */, _R7/* s2dVK */){
  return new F(function(){return hs_geInt64/* EXTERNAL */(E(_R6/* s2dVJ */), E(_R7/* s2dVK */));});
},
_R8/* $w$ccompare */ = function(_R9/* s2dWn */, _Ra/* s2dWo */){
  var _Rb/* s2dWq */ = hs_eqInt64/* EXTERNAL */(_R9/* s2dWn */, _Ra/* s2dWo */);
  if(!_Rb/* s2dWq */){
    var _Rc/* s2dWv */ = hs_leInt64/* EXTERNAL */(_R9/* s2dWn */, _Ra/* s2dWo */);
    return (!_Rc/* s2dWv */) ? 2 : 0;
  }else{
    return 1;
  }
},
_Rd/* $fOrdInt64_$ccompare */ = function(_Re/* s2dWz */, _Rf/* s2dWA */){
  return new F(function(){return _R8/* GHC.Int.$w$ccompare */(E(_Re/* s2dWz */), E(_Rf/* s2dWA */));});
},
_Rg/* $fOrdInt64_$cmax */ = function(_Rh/* s2dVy */, _Ri/* s2dVz */){
  var _Rj/* s2dVA */ = E(_Rh/* s2dVy */),
  _Rk/* s2dVC */ = E(_Ri/* s2dVz */),
  _Rl/* s2dVF */ = hs_leInt64/* EXTERNAL */(_Rj/* s2dVA */, _Rk/* s2dVC */);
  return (!_Rl/* s2dVF */) ? E(_Rj/* s2dVA */) : E(_Rk/* s2dVC */);
},
_Rm/* $fOrdInt64_$cmin */ = function(_Rn/* s2dVn */, _Ro/* s2dVo */){
  var _Rp/* s2dVp */ = E(_Rn/* s2dVn */),
  _Rq/* s2dVr */ = E(_Ro/* s2dVo */),
  _Rr/* s2dVu */ = hs_leInt64/* EXTERNAL */(_Rp/* s2dVp */, _Rq/* s2dVr */);
  return (!_Rr/* s2dVu */) ? E(_Rq/* s2dVr */) : E(_Rp/* s2dVp */);
},
_Rs/* $fOrdInt64 */ = {_:0,a:_QV/* GHC.Int.$fEqInt64 */,b:_Rd/* GHC.Int.$fOrdInt64_$ccompare */,c:_QW/* GHC.Int.$fOrdInt64_$c< */,d:_QZ/* GHC.Int.$fOrdInt64_$c<= */,e:_R2/* GHC.Int.$fOrdInt64_$c> */,f:_R5/* GHC.Int.$fOrdInt64_$c>= */,g:_Rg/* GHC.Int.$fOrdInt64_$cmax */,h:_Rm/* GHC.Int.$fOrdInt64_$cmin */},
_Rt/* $fRealInt1 */ = new T1(0,1),
_Ru/* eqInteger */ = function(_Rv/* s1H2 */, _Rw/* s1H3 */){
  var _Rx/* s1H4 */ = E(_Rv/* s1H2 */);
  if(!_Rx/* s1H4 */._){
    var _Ry/* s1H5 */ = _Rx/* s1H4 */.a,
    _Rz/* s1H6 */ = E(_Rw/* s1H3 */);
    return (_Rz/* s1H6 */._==0) ? _Ry/* s1H5 */==_Rz/* s1H6 */.a : (I_compareInt/* EXTERNAL */(_Rz/* s1H6 */.a, _Ry/* s1H5 */)==0) ? true : false;
  }else{
    var _RA/* s1Hc */ = _Rx/* s1H4 */.a,
    _RB/* s1Hd */ = E(_Rw/* s1H3 */);
    return (_RB/* s1Hd */._==0) ? (I_compareInt/* EXTERNAL */(_RA/* s1Hc */, _RB/* s1Hd */.a)==0) ? true : false : (I_compare/* EXTERNAL */(_RA/* s1Hc */, _RB/* s1Hd */.a)==0) ? true : false;
  }
},
_RC/* even1 */ = new T1(0,0),
_RD/* remInteger */ = function(_RE/* s1NY */, _RF/* s1NZ */){
  while(1){
    var _RG/* s1O0 */ = E(_RE/* s1NY */);
    if(!_RG/* s1O0 */._){
      var _RH/* s1O2 */ = E(_RG/* s1O0 */.a);
      if(_RH/* s1O2 */==(-2147483648)){
        _RE/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _RI/* s1O3 */ = E(_RF/* s1NZ */);
        if(!_RI/* s1O3 */._){
          return new T1(0,_RH/* s1O2 */%_RI/* s1O3 */.a);
        }else{
          _RE/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(_RH/* s1O2 */));
          _RF/* s1NZ */ = _RI/* s1O3 */;
          continue;
        }
      }
    }else{
      var _RJ/* s1Od */ = _RG/* s1O0 */.a,
      _RK/* s1Oe */ = E(_RF/* s1NZ */);
      return (_RK/* s1Oe */._==0) ? new T1(1,I_rem/* EXTERNAL */(_RJ/* s1Od */, I_fromInt/* EXTERNAL */(_RK/* s1Oe */.a))) : new T1(1,I_rem/* EXTERNAL */(_RJ/* s1Od */, _RK/* s1Oe */.a));
    }
  }
},
_RL/* $fIntegralInteger_$crem */ = function(_RM/* svus */, _RN/* svut */){
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_RN/* svut */, _RC/* GHC.Real.even1 */))){
    return new F(function(){return _RD/* GHC.Integer.Type.remInteger */(_RM/* svus */, _RN/* svut */);});
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_RO/* $fEnumRatio_gcd' */ = function(_RP/* svuv */, _RQ/* svuw */){
  while(1){
    if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_RQ/* svuw */, _RC/* GHC.Real.even1 */))){
      var _RR/*  svuv */ = _RQ/* svuw */,
      _RS/*  svuw */ = B(_RL/* GHC.Real.$fIntegralInteger_$crem */(_RP/* svuv */, _RQ/* svuw */));
      _RP/* svuv */ = _RR/*  svuv */;
      _RQ/* svuw */ = _RS/*  svuw */;
      continue;
    }else{
      return E(_RP/* svuv */);
    }
  }
},
_RT/* absInteger */ = function(_RU/* s1QP */){
  var _RV/* s1QQ */ = E(_RU/* s1QP */);
  if(!_RV/* s1QQ */._){
    var _RW/* s1QS */ = E(_RV/* s1QQ */.a);
    return (_RW/* s1QS */==(-2147483648)) ? E(_Kr/* GHC.Integer.Type.lvl3 */) : (_RW/* s1QS */<0) ? new T1(0, -_RW/* s1QS */) : E(_RV/* s1QQ */);
  }else{
    var _RX/* s1QW */ = _RV/* s1QQ */.a;
    return (I_compareInt/* EXTERNAL */(_RX/* s1QW */, 0)>=0) ? E(_RV/* s1QQ */) : new T1(1,I_negate/* EXTERNAL */(_RX/* s1QW */));
  }
},
_RY/* quotInteger */ = function(_RZ/* s1On */, _S0/* s1Oo */){
  while(1){
    var _S1/* s1Op */ = E(_RZ/* s1On */);
    if(!_S1/* s1Op */._){
      var _S2/* s1Or */ = E(_S1/* s1Op */.a);
      if(_S2/* s1Or */==(-2147483648)){
        _RZ/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _S3/* s1Os */ = E(_S0/* s1Oo */);
        if(!_S3/* s1Os */._){
          return new T1(0,quot/* EXTERNAL */(_S2/* s1Or */, _S3/* s1Os */.a));
        }else{
          _RZ/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(_S2/* s1Or */));
          _S0/* s1Oo */ = _S3/* s1Os */;
          continue;
        }
      }
    }else{
      var _S4/* s1OC */ = _S1/* s1Op */.a,
      _S5/* s1OD */ = E(_S0/* s1Oo */);
      return (_S5/* s1OD */._==0) ? new T1(0,I_toInt/* EXTERNAL */(I_quot/* EXTERNAL */(_S4/* s1OC */, I_fromInt/* EXTERNAL */(_S5/* s1OD */.a)))) : new T1(1,I_quot/* EXTERNAL */(_S4/* s1OC */, _S5/* s1OD */.a));
    }
  }
},
_S6/* RatioZeroDenominator */ = 5,
_S7/* ratioZeroDenomException */ = new T(function(){
  return B(_Pr/* GHC.Exception.$fExceptionArithException_$ctoException */(_S6/* GHC.Exception.RatioZeroDenominator */));
}),
_S8/* ratioZeroDenominatorError */ = new T(function(){
  return die/* EXTERNAL */(_S7/* GHC.Exception.ratioZeroDenomException */);
}),
_S9/* $w$sreduce */ = function(_Sa/* svvD */, _Sb/* svvE */){
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_Sb/* svvE */, _RC/* GHC.Real.even1 */))){
    var _Sc/* svvG */ = B(_RO/* GHC.Real.$fEnumRatio_gcd' */(B(_RT/* GHC.Integer.Type.absInteger */(_Sa/* svvD */)), B(_RT/* GHC.Integer.Type.absInteger */(_Sb/* svvE */))));
    return (!B(_Ru/* GHC.Integer.Type.eqInteger */(_Sc/* svvG */, _RC/* GHC.Real.even1 */))) ? new T2(0,B(_RY/* GHC.Integer.Type.quotInteger */(_Sa/* svvD */, _Sc/* svvG */)),B(_RY/* GHC.Integer.Type.quotInteger */(_Sb/* svvE */, _Sc/* svvG */))) : E(_Pv/* GHC.Real.divZeroError */);
  }else{
    return E(_S8/* GHC.Real.ratioZeroDenominatorError */);
  }
},
_Sd/* timesInteger */ = function(_Se/* s1PN */, _Sf/* s1PO */){
  while(1){
    var _Sg/* s1PP */ = E(_Se/* s1PN */);
    if(!_Sg/* s1PP */._){
      var _Sh/* s1PQ */ = _Sg/* s1PP */.a,
      _Si/* s1PR */ = E(_Sf/* s1PO */);
      if(!_Si/* s1PR */._){
        var _Sj/* s1PS */ = _Si/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_Sh/* s1PQ */, _Sj/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_Sh/* s1PQ */, _Sj/* s1PS */)|0);
        }else{
          _Se/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Sh/* s1PQ */));
          _Sf/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Sj/* s1PS */));
          continue;
        }
      }else{
        _Se/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Sh/* s1PQ */));
        _Sf/* s1PO */ = _Si/* s1PR */;
        continue;
      }
    }else{
      var _Sk/* s1Q6 */ = E(_Sf/* s1PO */);
      if(!_Sk/* s1Q6 */._){
        _Se/* s1PN */ = _Sg/* s1PP */;
        _Sf/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Sk/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_Sg/* s1PP */.a, _Sk/* s1Q6 */.a));
      }
    }
  }
},
_Sl/* $fRealInt64_$ctoRational */ = function(_Sm/* s2e6O */){
  var _Sn/* s2e6T */ = B(_S9/* GHC.Real.$w$sreduce */(B(_Sd/* GHC.Integer.Type.timesInteger */(B(_MK/* GHC.Integer.Type.int64ToInteger */(E(_Sm/* s2e6O */))), _Rt/* GHC.Int.$fRealInt1 */)), _Rt/* GHC.Int.$fRealInt1 */));
  return new T2(0,E(_Sn/* s2e6T */.a),E(_Sn/* s2e6T */.b));
},
_So/* $fRealInt64 */ = new T3(0,_K0/* GHC.Int.$fNumInt64 */,_Rs/* GHC.Int.$fOrdInt64 */,_Sl/* GHC.Int.$fRealInt64_$ctoRational */),
_Ln/* $fIntegralInt64 */ = new T(function(){
  return {_:0,a:_So/* GHC.Int.$fRealInt64 */,b:_Ox/* GHC.Int.$fEnumInt64 */,c:_Qt/* GHC.Int.$fIntegralInt64_$cquot */,d:_QM/* GHC.Int.$fIntegralInt64_$crem */,e:_PF/* GHC.Int.$fIntegralInt64_$cdiv */,f:_Qi/* GHC.Int.$fIntegralInt64_$cmod */,g:_QC/* GHC.Int.$fIntegralInt64_$cquotRem */,h:_Q9/* GHC.Int.$fIntegralInt64_$cdivMod */,i:_MR/* GHC.Int.$fIntegralInt64_$ctoInteger */};
}),
_Sp/* $p1Ord */ = function(_Sq/* scBR */){
  return E(E(_Sq/* scBR */).a);
},
_Sr/* $p2Real */ = function(_Ss/* svfR */){
  return E(E(_Ss/* svfR */).b);
},
_St/* == */ = function(_Su/* scBJ */){
  return E(E(_Su/* scBJ */).a);
},
_Sv/* even2 */ = new T1(0,2),
_Sw/* rem */ = function(_Sx/* sveI */){
  return E(E(_Sx/* sveI */).d);
},
_Sy/* even */ = function(_Sz/* svre */, _SA/* svrf */){
  var _SB/* svrg */ = B(_KV/* GHC.Real.$p1Integral */(_Sz/* svre */)),
  _SC/* svrh */ = new T(function(){
    return B(_KX/* GHC.Real.$p1Real */(_SB/* svrg */));
  }),
  _SD/* svrl */ = new T(function(){
    return B(A3(_Sw/* GHC.Real.rem */,_Sz/* svre */, _SA/* svrf */, new T(function(){
      return B(A2(_KZ/* GHC.Num.fromInteger */,_SC/* svrh */, _Sv/* GHC.Real.even2 */));
    })));
  });
  return new F(function(){return A3(_St/* GHC.Classes.== */,B(_Sp/* GHC.Classes.$p1Ord */(B(_Sr/* GHC.Real.$p2Real */(_SB/* svrg */)))), _SD/* svrl */, new T(function(){
    return B(A2(_KZ/* GHC.Num.fromInteger */,_SC/* svrh */, _RC/* GHC.Real.even1 */));
  }));});
},
_SE/* $wg1 */ = function(_SF/*  sfnl */, _SG/*  sfnm */, _SH/*  sfnn */){
  while(1){
    var _SI/*  $wg1 */ = B((function(_SJ/* sfnl */, _SK/* sfnm */, _SL/* sfnn */){
      if(!B(_Sy/* GHC.Real.even */(_Ln/* GHC.Int.$fIntegralInt64 */, _SK/* sfnm */))){
        var _SM/* sfnr */ = hs_eqInt64/* EXTERNAL */(_SK/* sfnm */, new Long/* EXTERNAL */(1, 0));
        if(!_SM/* sfnr */){
          var _SN/* sfnw */ = hs_minusInt64/* EXTERNAL */(_SK/* sfnm */, new Long/* EXTERNAL */(1, 0));
          _SF/*  sfnl */ = new T(function(){
            return B(_JD/* GHC.Int.$fNumInt64_$c* */(_SJ/* sfnl */, _SJ/* sfnl */));
          });
          _SG/*  sfnm */ = B(_Ql/* GHC.Int.$w$cquot */(_SN/* sfnw */, new Long/* EXTERNAL */(2, 0)));
          _SH/*  sfnn */ = new T(function(){
            return B(_JD/* GHC.Int.$fNumInt64_$c* */(_SJ/* sfnl */, _SL/* sfnn */));
          },1);
          return __continue/* EXTERNAL */;
        }else{
          var _SO/* sfnH */ = hs_timesInt64/* EXTERNAL */(E(_SJ/* sfnl */), E(_SL/* sfnn */));
          return E(_SO/* sfnH */);
        }
      }else{
        var _SP/*   sfnm */ = B(_Ql/* GHC.Int.$w$cquot */(_SK/* sfnm */, new Long/* EXTERNAL */(2, 0))),
        _SQ/*   sfnn */ = _SL/* sfnn */;
        _SF/*  sfnl */ = new T(function(){
          return B(_JD/* GHC.Int.$fNumInt64_$c* */(_SJ/* sfnl */, _SJ/* sfnl */));
        });
        _SG/*  sfnm */ = _SP/*   sfnm */;
        _SH/*  sfnn */ = _SQ/*   sfnn */;
        return __continue/* EXTERNAL */;
      }
    })(_SF/*  sfnl */, _SG/*  sfnm */, _SH/*  sfnn */));
    if(_SI/*  $wg1 */!=__continue/* EXTERNAL */){
      return _SI/*  $wg1 */;
    }
  }
},
_SR/* $wf1 */ = function(_SS/*  sfnM */, _ST/*  sfnN */){
  while(1){
    var _SU/*  $wf1 */ = B((function(_SV/* sfnM */, _SW/* sfnN */){
      if(!B(_Sy/* GHC.Real.even */(_Ln/* GHC.Int.$fIntegralInt64 */, _SW/* sfnN */))){
        var _SX/* sfnR */ = hs_eqInt64/* EXTERNAL */(_SW/* sfnN */, new Long/* EXTERNAL */(1, 0));
        if(!_SX/* sfnR */){
          var _SY/* sfnW */ = hs_minusInt64/* EXTERNAL */(_SW/* sfnN */, new Long/* EXTERNAL */(1, 0));
          return new F(function(){return _SE/* System.Random.$wg1 */(new T(function(){
            return B(_JD/* GHC.Int.$fNumInt64_$c* */(_SV/* sfnM */, _SV/* sfnM */));
          }), B(_Ql/* GHC.Int.$w$cquot */(_SY/* sfnW */, new Long/* EXTERNAL */(2, 0))), _SV/* sfnM */);});
        }else{
          return E(_SV/* sfnM */);
        }
      }else{
        var _SZ/*   sfnN */ = B(_Ql/* GHC.Int.$w$cquot */(_SW/* sfnN */, new Long/* EXTERNAL */(2, 0)));
        _SS/*  sfnM */ = new T(function(){
          return B(_JD/* GHC.Int.$fNumInt64_$c* */(_SV/* sfnM */, _SV/* sfnM */));
        });
        _ST/*  sfnN */ = _SZ/*   sfnN */;
        return __continue/* EXTERNAL */;
      }
    })(_SS/*  sfnM */, _ST/*  sfnN */));
    if(_SU/*  $wf1 */!=__continue/* EXTERNAL */){
      return _SU/*  $wf1 */;
    }
  }
},
_T0/* $w$s^ */ = function(_T1/* sfoq */, _T2/* sfor */){
  var _T3/* sfot */ = hs_ltInt64/* EXTERNAL */(_T2/* sfor */, new Long/* EXTERNAL */(0, 0));
  if(!_T3/* sfot */){
    var _T4/* sfoy */ = hs_eqInt64/* EXTERNAL */(_T2/* sfor */, new Long/* EXTERNAL */(0, 0));
    if(!_T4/* sfoy */){
      return new F(function(){return _SR/* System.Random.$wf1 */(_T1/* sfoq */, _T2/* sfor */);});
    }else{
      return E(_KQ/* System.Random.$fRandomDouble6 */);
    }
  }else{
    return E(_KP/* System.Random.$fRandomDouble5 */);
  }
},
_T5/* $fRandomDouble_twoto53 */ = new T(function(){
  return B(_T0/* System.Random.$w$s^ */(_KN/* System.Random.$fRandomDouble4 */, new Long/* EXTERNAL */(53, 0)));
}),
_T6/* doubleFromInteger */ = function(_T7/* s1M0 */){
  var _T8/* s1M1 */ = E(_T7/* s1M0 */);
  if(!_T8/* s1M1 */._){
    return _T8/* s1M1 */.a;
  }else{
    return new F(function(){return I_toNumber/* EXTERNAL */(_T8/* s1M1 */.a);});
  }
},
_T9/* $fRandomDouble3 */ = new T(function(){
  return B(_T6/* GHC.Integer.Type.doubleFromInteger */(B(_MK/* GHC.Integer.Type.int64ToInteger */(E(_T5/* System.Random.$fRandomDouble_twoto53 */)))));
}),
_Ta/* $fRandomDouble7 */ = new T(function(){
  return hs_minusInt64/* EXTERNAL */(E(_T5/* System.Random.$fRandomDouble_twoto53 */), new Long/* EXTERNAL */(1, 0));
}),
_Tb/* $w$c.&. */ = function(_Tc/* s2e5n */, _Td/* s2e5o */){
  var _Te/* s2e5q */ = hs_int64ToWord64/* EXTERNAL */(_Td/* s2e5o */),
  _Tf/* s2e5u */ = hs_int64ToWord64/* EXTERNAL */(_Tc/* s2e5n */),
  _Tg/* s2e5y */ = hs_and64/* EXTERNAL */(_Tf/* s2e5u */, _Te/* s2e5q */),
  _Th/* s2e5C */ = hs_word64ToInt64/* EXTERNAL */(_Tg/* s2e5y */);
  return E(_Th/* s2e5C */);
},
_Ti/* $fRandomBool3 */ = new T1(0,1),
_Tj/* $WStdGen */ = function(_Tk/* sfmR */, _Tl/* sfmS */){
  return new T2(0,E(_Tk/* sfmR */),E(_Tl/* sfmS */));
},
_Tm/* $w$cnext */ = function(_Tn/* sfqJ */, _To/* sfqK */){
  var _Tp/* sfqL */ = quot/* EXTERNAL */(_To/* sfqK */, 52774),
  _Tq/* sfqM */ = (imul/* EXTERNAL */(40692, _To/* sfqK */-(imul/* EXTERNAL */(_Tp/* sfqL */, 52774)|0)|0)|0)-(imul/* EXTERNAL */(_Tp/* sfqL */, 3791)|0)|0,
  _Tr/* sfqR */ = new T(function(){
    if(_Tq/* sfqM */>=0){
      return _Tq/* sfqM */;
    }else{
      return _Tq/* sfqM */+2147483399|0;
    }
  }),
  _Ts/* sfqV */ = quot/* EXTERNAL */(_Tn/* sfqJ */, 53668),
  _Tt/* sfqW */ = (imul/* EXTERNAL */(40014, _Tn/* sfqJ */-(imul/* EXTERNAL */(_Ts/* sfqV */, 53668)|0)|0)|0)-(imul/* EXTERNAL */(_Ts/* sfqV */, 12211)|0)|0,
  _Tu/* sfr1 */ = new T(function(){
    if(_Tt/* sfqW */>=0){
      return _Tt/* sfqW */;
    }else{
      return _Tt/* sfqW */+2147483563|0;
    }
  });
  return new T2(0,new T(function(){
    var _Tv/* sfr9 */ = E(_Tu/* sfr1 */)-E(_Tr/* sfqR */)|0;
    if(_Tv/* sfr9 */>=1){
      return _Tv/* sfr9 */;
    }else{
      return _Tv/* sfr9 */+2147483562|0;
    }
  }),new T(function(){
    return B(_Tj/* System.Random.$WStdGen */(_Tu/* sfr1 */, _Tr/* sfqR */));
  }));
},
_Tw/* b */ = new T1(0,2147483562),
_Tx/* getStdRandom4 */ = new T1(0,0),
_Ty/* lvl5 */ = new T1(0,1000),
_Tz/* modInt# */ = function(_TA/* scEd */, _TB/* scEe */){
  var _TC/* scEf */ = _TA/* scEd */%_TB/* scEe */;
  if(_TA/* scEd */<=0){
    if(_TA/* scEd */>=0){
      return E(_TC/* scEf */);
    }else{
      if(_TB/* scEe */<=0){
        return E(_TC/* scEf */);
      }else{
        var _TD/* scEm */ = E(_TC/* scEf */);
        return (_TD/* scEm */==0) ? 0 : _TD/* scEm */+_TB/* scEe */|0;
      }
    }
  }else{
    if(_TB/* scEe */>=0){
      if(_TA/* scEd */>=0){
        return E(_TC/* scEf */);
      }else{
        if(_TB/* scEe */<=0){
          return E(_TC/* scEf */);
        }else{
          var _TE/* scEt */ = E(_TC/* scEf */);
          return (_TE/* scEt */==0) ? 0 : _TE/* scEt */+_TB/* scEe */|0;
        }
      }
    }else{
      var _TF/* scEu */ = E(_TC/* scEf */);
      return (_TF/* scEu */==0) ? 0 : _TF/* scEu */+_TB/* scEe */|0;
    }
  }
},
_TG/* modInteger */ = function(_TH/* s1Na */, _TI/* s1Nb */){
  while(1){
    var _TJ/* s1Nc */ = E(_TH/* s1Na */);
    if(!_TJ/* s1Nc */._){
      var _TK/* s1Ne */ = E(_TJ/* s1Nc */.a);
      if(_TK/* s1Ne */==(-2147483648)){
        _TH/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _TL/* s1Nf */ = E(_TI/* s1Nb */);
        if(!_TL/* s1Nf */._){
          return new T1(0,B(_Tz/* GHC.Classes.modInt# */(_TK/* s1Ne */, _TL/* s1Nf */.a)));
        }else{
          _TH/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(_TK/* s1Ne */));
          _TI/* s1Nb */ = _TL/* s1Nf */;
          continue;
        }
      }
    }else{
      var _TM/* s1Np */ = _TJ/* s1Nc */.a,
      _TN/* s1Nq */ = E(_TI/* s1Nb */);
      return (_TN/* s1Nq */._==0) ? new T1(1,I_mod/* EXTERNAL */(_TM/* s1Np */, I_fromInt/* EXTERNAL */(_TN/* s1Nq */.a))) : new T1(1,I_mod/* EXTERNAL */(_TM/* s1Np */, _TN/* s1Nq */.a));
    }
  }
},
_TO/* $w$srandomIvalInteger */ = function(_TP/*  sfs7 */, _TQ/*  sfs8 */, _TR/*  sfs9 */, _TS/*  sfsa */){
  while(1){
    var _TT/*  $w$srandomIvalInteger */ = B((function(_TU/* sfs7 */, _TV/* sfs8 */, _TW/* sfs9 */, _TX/* sfsa */){
      if(!B(_L1/* GHC.Integer.Type.gtInteger */(_TV/* sfs8 */, _TW/* sfs9 */))){
        var _TY/* sfsc */ = B(_Ki/* GHC.Integer.Type.plusInteger */(B(_LX/* GHC.Integer.Type.minusInteger */(_TW/* sfs9 */, _TV/* sfs8 */)), _Ti/* System.Random.$fRandomBool3 */)),
        _TZ/* sfsf */ = function(_U0/* sfsg */, _U1/* sfsh */, _U2/* sfsi */){
          while(1){
            if(!B(_Lp/* GHC.Integer.Type.geInteger */(_U0/* sfsg */, B(_Sd/* GHC.Integer.Type.timesInteger */(_TY/* sfsc */, _Ty/* System.Random.lvl5 */))))){
              var _U3/* sfsk */ = E(_U2/* sfsi */),
              _U4/* sfsn */ = B(_Tm/* System.Random.$w$cnext */(_U3/* sfsk */.a, _U3/* sfsk */.b)),
              _U5/*  sfsg */ = B(_Sd/* GHC.Integer.Type.timesInteger */(_U0/* sfsg */, _Tw/* System.Random.b */)),
              _U6/*  sfsh */ = B(_Ki/* GHC.Integer.Type.plusInteger */(B(_Sd/* GHC.Integer.Type.timesInteger */(_U1/* sfsh */, _Tw/* System.Random.b */)), B(_LX/* GHC.Integer.Type.minusInteger */(B(_MI/* GHC.Integer.Type.smallInteger */(E(_U4/* sfsn */.a))), _Ti/* System.Random.$fRandomBool3 */))));
              _U0/* sfsg */ = _U5/*  sfsg */;
              _U1/* sfsh */ = _U6/*  sfsh */;
              _U2/* sfsi */ = _U4/* sfsn */.b;
              continue;
            }else{
              return new T2(0,_U1/* sfsh */,_U2/* sfsi */);
            }
          }
        },
        _U7/* sfsx */ = B(_TZ/* sfsf */(_Ti/* System.Random.$fRandomBool3 */, _Tx/* System.Random.getStdRandom4 */, _TX/* sfsa */)),
        _U8/* sfsE */ = new T(function(){
          return B(A2(_KZ/* GHC.Num.fromInteger */,_TU/* sfs7 */, new T(function(){
            if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_TY/* sfsc */, _Tx/* System.Random.getStdRandom4 */))){
              return B(_Ki/* GHC.Integer.Type.plusInteger */(_TV/* sfs8 */, B(_TG/* GHC.Integer.Type.modInteger */(_U7/* sfsx */.a, _TY/* sfsc */))));
            }else{
              return E(_Pv/* GHC.Real.divZeroError */);
            }
          })));
        });
        return new T2(0,_U8/* sfsE */,_U7/* sfsx */.b);
      }else{
        var _U9/*   sfs7 */ = _TU/* sfs7 */,
        _Ua/*   sfs8 */ = _TW/* sfs9 */,
        _Ub/*   sfs9 */ = _TV/* sfs8 */,
        _Uc/*   sfsa */ = _TX/* sfsa */;
        _TP/*  sfs7 */ = _U9/*   sfs7 */;
        _TQ/*  sfs8 */ = _Ua/*   sfs8 */;
        _TR/*  sfs9 */ = _Ub/*   sfs9 */;
        _TS/*  sfsa */ = _Uc/*   sfsa */;
        return __continue/* EXTERNAL */;
      }
    })(_TP/*  sfs7 */, _TQ/*  sfs8 */, _TR/*  sfs9 */, _TS/*  sfsa */));
    if(_TT/*  $w$srandomIvalInteger */!=__continue/* EXTERNAL */){
      return _TT/*  $w$srandomIvalInteger */;
    }
  }
},
_Ud/* $w$s$crandom */ = function(_Ue/* sfSt */){
  var _Uf/* sfSu */ = B(_TO/* System.Random.$w$srandomIvalInteger */(_K0/* GHC.Int.$fNumInt64 */, _KM/* System.Random.$fRandomCLLong4 */, _KF/* System.Random.$fRandomCLLong3 */, _Ue/* sfSt */));
  return new T2(0,new T(function(){
    return B(_T6/* GHC.Integer.Type.doubleFromInteger */(B(_MK/* GHC.Integer.Type.int64ToInteger */(B(_Tb/* GHC.Int.$w$c.&. */(E(_Ta/* System.Random.$fRandomDouble7 */), E(_Uf/* sfSu */.a)))))))/E(_T9/* System.Random.$fRandomDouble3 */);
  }),_Uf/* sfSu */.b);
},
_Ug/* $w$srandomRFloating2 */ = function(_Uh/*  sfSX */, _Ui/*  sfSY */, _Uj/*  sfSZ */){
  while(1){
    var _Uk/*  $w$srandomRFloating2 */ = B((function(_Ul/* sfSX */, _Um/* sfSY */, _Un/* sfSZ */){
      if(_Ul/* sfSX */<=_Um/* sfSY */){
        var _Uo/* sfT2 */ = new T(function(){
          var _Up/* sfT3 */ = B(_Ud/* System.Random.$w$s$crandom */(_Un/* sfSZ */));
          return new T2(0,_Up/* sfT3 */.a,_Up/* sfT3 */.b);
        });
        return new T2(0,new T(function(){
          var _Uq/* sfT9 */ = E(E(_Uo/* sfT2 */).a);
          return 0.5*_Ul/* sfSX */+_Uq/* sfT9 */*(0.5*_Um/* sfSY */-0.5*_Ul/* sfSX */)+0.5*_Ul/* sfSX */+_Uq/* sfT9 */*(0.5*_Um/* sfSY */-0.5*_Ul/* sfSX */);
        }),new T(function(){
          return E(E(_Uo/* sfT2 */).b);
        }));
      }else{
        var _Ur/*   sfSX */ = _Um/* sfSY */,
        _Us/*   sfSY */ = _Ul/* sfSX */,
        _Ut/*   sfSZ */ = _Un/* sfSZ */;
        _Uh/*  sfSX */ = _Ur/*   sfSX */;
        _Ui/*  sfSY */ = _Us/*   sfSY */;
        _Uj/*  sfSZ */ = _Ut/*   sfSZ */;
        return __continue/* EXTERNAL */;
      }
    })(_Uh/*  sfSX */, _Ui/*  sfSY */, _Uj/*  sfSZ */));
    if(_Uk/*  $w$srandomRFloating2 */!=__continue/* EXTERNAL */){
      return _Uk/*  $w$srandomRFloating2 */;
    }
  }
},
_Uu/* s6SwZ */ = 1420103680,
_Uv/* s6Sx0 */ = 465,
_Uw/* s6Sx1 */ = new T2(1,_Uv/* s6Sx0 */,_6/* GHC.Types.[] */),
_Ux/* s6Sx2 */ = new T2(1,_Uu/* s6SwZ */,_Uw/* s6Sx1 */),
_Uy/* $fHasResolutionE5 */ = new T(function(){
  return B(_Kw/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _Ux/* s6Sx2 */));
}),
_Uz/* $fBitsInt4 */ = 0,
_UA/* $w$cdivMod1 */ = function(_UB/* s2dPw */, _UC/* s2dPx */){
  var _UD/* s2dPy */ = E(_UC/* s2dPx */);
  if(!_UD/* s2dPy */){
    return E(_Pv/* GHC.Real.divZeroError */);
  }else{
    var _UE/* s2dPz */ = function(_UF/* s2dPA */){
      if(_UB/* s2dPw */<=0){
        if(_UB/* s2dPw */>=0){
          var _UG/* s2dPF */ = quotRemI/* EXTERNAL */(_UB/* s2dPw */, _UD/* s2dPy */);
          return new T2(0,_UG/* s2dPF */.a,_UG/* s2dPF */.b);
        }else{
          if(_UD/* s2dPy */<=0){
            var _UH/* s2dPM */ = quotRemI/* EXTERNAL */(_UB/* s2dPw */, _UD/* s2dPy */);
            return new T2(0,_UH/* s2dPM */.a,_UH/* s2dPM */.b);
          }else{
            var _UI/* s2dPS */ = quotRemI/* EXTERNAL */(_UB/* s2dPw */+1|0, _UD/* s2dPy */);
            return new T2(0,_UI/* s2dPS */.a-1|0,(_UI/* s2dPS */.b+_UD/* s2dPy */|0)-1|0);
          }
        }
      }else{
        if(_UD/* s2dPy */>=0){
          if(_UB/* s2dPw */>=0){
            var _UJ/* s2dQ4 */ = quotRemI/* EXTERNAL */(_UB/* s2dPw */, _UD/* s2dPy */);
            return new T2(0,_UJ/* s2dQ4 */.a,_UJ/* s2dQ4 */.b);
          }else{
            if(_UD/* s2dPy */<=0){
              var _UK/* s2dQb */ = quotRemI/* EXTERNAL */(_UB/* s2dPw */, _UD/* s2dPy */);
              return new T2(0,_UK/* s2dQb */.a,_UK/* s2dQb */.b);
            }else{
              var _UL/* s2dQh */ = quotRemI/* EXTERNAL */(_UB/* s2dPw */+1|0, _UD/* s2dPy */);
              return new T2(0,_UL/* s2dQh */.a-1|0,(_UL/* s2dQh */.b+_UD/* s2dPy */|0)-1|0);
            }
          }
        }else{
          var _UM/* s2dQq */ = quotRemI/* EXTERNAL */(_UB/* s2dPw */-1|0, _UD/* s2dPy */);
          return new T2(0,_UM/* s2dQq */.a-1|0,(_UM/* s2dQq */.b+_UD/* s2dPy */|0)+1|0);
        }
      }
    };
    if(E(_UD/* s2dPy */)==(-1)){
      if(E(_UB/* s2dPw */)==(-2147483648)){
        return new T2(0,_Py/* GHC.Real.overflowError */,_Uz/* GHC.Int.$fBitsInt4 */);
      }else{
        return new F(function(){return _UE/* s2dPz */(_/* EXTERNAL */);});
      }
    }else{
      return new F(function(){return _UE/* s2dPz */(_/* EXTERNAL */);});
    }
  }
},
_UN/* lvl1 */ = new T1(0,-1),
_UO/* signumInteger */ = function(_UP/* s1OO */){
  var _UQ/* s1OP */ = E(_UP/* s1OO */);
  if(!_UQ/* s1OP */._){
    var _UR/* s1OQ */ = _UQ/* s1OP */.a;
    return (_UR/* s1OQ */>=0) ? (E(_UR/* s1OQ */)==0) ? E(_K1/* GHC.Integer.Type.lvl */) : E(_Kg/* GHC.Integer.Type.log2I1 */) : E(_UN/* GHC.Integer.Type.lvl1 */);
  }else{
    var _US/* s1OW */ = I_compareInt/* EXTERNAL */(_UQ/* s1OP */.a, 0);
    return (_US/* s1OW */<=0) ? (E(_US/* s1OW */)==0) ? E(_K1/* GHC.Integer.Type.lvl */) : E(_UN/* GHC.Integer.Type.lvl1 */) : E(_Kg/* GHC.Integer.Type.log2I1 */);
  }
},
_UT/* $w$s$c/ */ = function(_UU/* svwb */, _UV/* svwc */, _UW/* svwd */, _UX/* svwe */){
  var _UY/* svwf */ = B(_Sd/* GHC.Integer.Type.timesInteger */(_UV/* svwc */, _UW/* svwd */));
  return new F(function(){return _S9/* GHC.Real.$w$sreduce */(B(_Sd/* GHC.Integer.Type.timesInteger */(B(_Sd/* GHC.Integer.Type.timesInteger */(_UU/* svwb */, _UX/* svwe */)), B(_UO/* GHC.Integer.Type.signumInteger */(_UY/* svwf */)))), B(_RT/* GHC.Integer.Type.absInteger */(_UY/* svwf */)));});
},
_UZ/* $fHasResolutionE12_$cresolution */ = function(_V0/* s6Sx3 */){
  return E(_Uy/* Data.Fixed.$fHasResolutionE5 */);
},
_V1/* $fEnumInteger2 */ = new T1(0,1),
_V2/* $wenumDeltaInteger */ = function(_V3/* smJm */, _V4/* smJn */){
  var _V5/* smJo */ = E(_V3/* smJm */);
  return new T2(0,_V5/* smJo */,new T(function(){
    var _V6/* smJq */ = B(_V2/* GHC.Enum.$wenumDeltaInteger */(B(_Ki/* GHC.Integer.Type.plusInteger */(_V5/* smJo */, _V4/* smJn */)), _V4/* smJn */));
    return new T2(1,_V6/* smJq */.a,_V6/* smJq */.b);
  }));
},
_V7/* $fEnumInteger_$cenumFrom */ = function(_V8/* smJF */){
  var _V9/* smJG */ = B(_V2/* GHC.Enum.$wenumDeltaInteger */(_V8/* smJF */, _V1/* GHC.Enum.$fEnumInteger2 */));
  return new T2(1,_V9/* smJG */.a,_V9/* smJG */.b);
},
_Va/* $fEnumInteger_$cenumFromThen */ = function(_Vb/* smJJ */, _Vc/* smJK */){
  var _Vd/* smJM */ = B(_V2/* GHC.Enum.$wenumDeltaInteger */(_Vb/* smJJ */, new T(function(){
    return B(_LX/* GHC.Integer.Type.minusInteger */(_Vc/* smJK */, _Vb/* smJJ */));
  })));
  return new T2(1,_Vd/* smJM */.a,_Vd/* smJM */.b);
},
_Ve/* enumDeltaToInteger */ = function(_Vf/* smJP */, _Vg/* smJQ */, _Vh/* smJR */){
  if(!B(_Lp/* GHC.Integer.Type.geInteger */(_Vg/* smJQ */, _Lo/* GHC.Enum.$fEnumInteger1 */))){
    var _Vi/* smJT */ = function(_Vj/* smJU */){
      return (!B(_Lx/* GHC.Integer.Type.ltInteger */(_Vj/* smJU */, _Vh/* smJR */))) ? new T2(1,_Vj/* smJU */,new T(function(){
        return B(_Vi/* smJT */(B(_Ki/* GHC.Integer.Type.plusInteger */(_Vj/* smJU */, _Vg/* smJQ */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _Vi/* smJT */(_Vf/* smJP */);});
  }else{
    var _Vk/* smJY */ = function(_Vl/* smJZ */){
      return (!B(_L1/* GHC.Integer.Type.gtInteger */(_Vl/* smJZ */, _Vh/* smJR */))) ? new T2(1,_Vl/* smJZ */,new T(function(){
        return B(_Vk/* smJY */(B(_Ki/* GHC.Integer.Type.plusInteger */(_Vl/* smJZ */, _Vg/* smJQ */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _Vk/* smJY */(_Vf/* smJP */);});
  }
},
_Vm/* $fEnumInteger_$cenumFromThenTo */ = function(_Vn/* smKg */, _Vo/* smKh */, _Vp/* smKi */){
  return new F(function(){return _Ve/* GHC.Enum.enumDeltaToInteger */(_Vn/* smKg */, B(_LX/* GHC.Integer.Type.minusInteger */(_Vo/* smKh */, _Vn/* smKg */)), _Vp/* smKi */);});
},
_Vq/* $fEnumInteger_$cenumFromTo */ = function(_Vr/* smKe */, _Vs/* smKf */){
  return new F(function(){return _Ve/* GHC.Enum.enumDeltaToInteger */(_Vr/* smKe */, _V1/* GHC.Enum.$fEnumInteger2 */, _Vs/* smKf */);});
},
_Vt/* integerToInt */ = function(_Vu/* s1Rv */){
  var _Vv/* s1Rw */ = E(_Vu/* s1Rv */);
  if(!_Vv/* s1Rw */._){
    return E(_Vv/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_Vv/* s1Rw */.a);});
  }
},
_Vw/* $fEnumInteger_$cfromEnum */ = function(_Vx/* smJf */){
  return new F(function(){return _Vt/* GHC.Integer.Type.integerToInt */(_Vx/* smJf */);});
},
_Vy/* $fEnumInteger_$cpred */ = function(_Vz/* smJl */){
  return new F(function(){return _LX/* GHC.Integer.Type.minusInteger */(_Vz/* smJl */, _V1/* GHC.Enum.$fEnumInteger2 */);});
},
_VA/* $fEnumInteger_$csucc */ = function(_VB/* smJk */){
  return new F(function(){return _Ki/* GHC.Integer.Type.plusInteger */(_VB/* smJk */, _V1/* GHC.Enum.$fEnumInteger2 */);});
},
_VC/* $fEnumInteger_$ctoEnum */ = function(_VD/* smJh */){
  return new F(function(){return _MI/* GHC.Integer.Type.smallInteger */(E(_VD/* smJh */));});
},
_VE/* $fEnumInteger */ = {_:0,a:_VA/* GHC.Enum.$fEnumInteger_$csucc */,b:_Vy/* GHC.Enum.$fEnumInteger_$cpred */,c:_VC/* GHC.Enum.$fEnumInteger_$ctoEnum */,d:_Vw/* GHC.Enum.$fEnumInteger_$cfromEnum */,e:_V7/* GHC.Enum.$fEnumInteger_$cenumFrom */,f:_Va/* GHC.Enum.$fEnumInteger_$cenumFromThen */,g:_Vq/* GHC.Enum.$fEnumInteger_$cenumFromTo */,h:_Vm/* GHC.Enum.$fEnumInteger_$cenumFromThenTo */},
_VF/* divInt# */ = function(_VG/* scDT */, _VH/* scDU */){
  if(_VG/* scDT */<=0){
    if(_VG/* scDT */>=0){
      return new F(function(){return quot/* EXTERNAL */(_VG/* scDT */, _VH/* scDU */);});
    }else{
      if(_VH/* scDU */<=0){
        return new F(function(){return quot/* EXTERNAL */(_VG/* scDT */, _VH/* scDU */);});
      }else{
        return quot/* EXTERNAL */(_VG/* scDT */+1|0, _VH/* scDU */)-1|0;
      }
    }
  }else{
    if(_VH/* scDU */>=0){
      if(_VG/* scDT */>=0){
        return new F(function(){return quot/* EXTERNAL */(_VG/* scDT */, _VH/* scDU */);});
      }else{
        if(_VH/* scDU */<=0){
          return new F(function(){return quot/* EXTERNAL */(_VG/* scDT */, _VH/* scDU */);});
        }else{
          return quot/* EXTERNAL */(_VG/* scDT */+1|0, _VH/* scDU */)-1|0;
        }
      }
    }else{
      return quot/* EXTERNAL */(_VG/* scDT */-1|0, _VH/* scDU */)-1|0;
    }
  }
},
_VI/* divInteger */ = function(_VJ/* s1Nz */, _VK/* s1NA */){
  while(1){
    var _VL/* s1NB */ = E(_VJ/* s1Nz */);
    if(!_VL/* s1NB */._){
      var _VM/* s1ND */ = E(_VL/* s1NB */.a);
      if(_VM/* s1ND */==(-2147483648)){
        _VJ/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _VN/* s1NE */ = E(_VK/* s1NA */);
        if(!_VN/* s1NE */._){
          return new T1(0,B(_VF/* GHC.Classes.divInt# */(_VM/* s1ND */, _VN/* s1NE */.a)));
        }else{
          _VJ/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(_VM/* s1ND */));
          _VK/* s1NA */ = _VN/* s1NE */;
          continue;
        }
      }
    }else{
      var _VO/* s1NO */ = _VL/* s1NB */.a,
      _VP/* s1NP */ = E(_VK/* s1NA */);
      return (_VP/* s1NP */._==0) ? new T1(1,I_div/* EXTERNAL */(_VO/* s1NO */, I_fromInt/* EXTERNAL */(_VP/* s1NP */.a))) : new T1(1,I_div/* EXTERNAL */(_VO/* s1NO */, _VP/* s1NP */.a));
    }
  }
},
_VQ/* $fIntegralInteger_$cdiv */ = function(_VR/* svup */, _VS/* svuq */){
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_VS/* svuq */, _RC/* GHC.Real.even1 */))){
    return new F(function(){return _VI/* GHC.Integer.Type.divInteger */(_VR/* svup */, _VS/* svuq */);});
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_VT/* divModInteger */ = function(_VU/* s1MF */, _VV/* s1MG */){
  while(1){
    var _VW/* s1MH */ = E(_VU/* s1MF */);
    if(!_VW/* s1MH */._){
      var _VX/* s1MJ */ = E(_VW/* s1MH */.a);
      if(_VX/* s1MJ */==(-2147483648)){
        _VU/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _VY/* s1MK */ = E(_VV/* s1MG */);
        if(!_VY/* s1MK */._){
          var _VZ/* s1ML */ = _VY/* s1MK */.a;
          return new T2(0,new T1(0,B(_VF/* GHC.Classes.divInt# */(_VX/* s1MJ */, _VZ/* s1ML */))),new T1(0,B(_Tz/* GHC.Classes.modInt# */(_VX/* s1MJ */, _VZ/* s1ML */))));
        }else{
          _VU/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(_VX/* s1MJ */));
          _VV/* s1MG */ = _VY/* s1MK */;
          continue;
        }
      }
    }else{
      var _W0/* s1MY */ = E(_VV/* s1MG */);
      if(!_W0/* s1MY */._){
        _VU/* s1MF */ = _VW/* s1MH */;
        _VV/* s1MG */ = new T1(1,I_fromInt/* EXTERNAL */(_W0/* s1MY */.a));
        continue;
      }else{
        var _W1/* s1N5 */ = I_divMod/* EXTERNAL */(_VW/* s1MH */.a, _W0/* s1MY */.a);
        return new T2(0,new T1(1,_W1/* s1N5 */.a),new T1(1,_W1/* s1N5 */.b));
      }
    }
  }
},
_W2/* $fIntegralInteger_$cdivMod */ = function(_W3/* svua */, _W4/* svub */){
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_W4/* svub */, _RC/* GHC.Real.even1 */))){
    var _W5/* svud */ = B(_VT/* GHC.Integer.Type.divModInteger */(_W3/* svua */, _W4/* svub */));
    return new T2(0,_W5/* svud */.a,_W5/* svud */.b);
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_W6/* $fIntegralInteger_$cmod */ = function(_W7/* svum */, _W8/* svun */){
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_W8/* svun */, _RC/* GHC.Real.even1 */))){
    return new F(function(){return _TG/* GHC.Integer.Type.modInteger */(_W7/* svum */, _W8/* svun */);});
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_W9/* $fIntegralInteger_$cquot */ = function(_Wa/* svvA */, _Wb/* svvB */){
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_Wb/* svvB */, _RC/* GHC.Real.even1 */))){
    return new F(function(){return _RY/* GHC.Integer.Type.quotInteger */(_Wa/* svvA */, _Wb/* svvB */);});
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_Wc/* quotRemInteger */ = function(_Wd/* s1Ma */, _We/* s1Mb */){
  while(1){
    var _Wf/* s1Mc */ = E(_Wd/* s1Ma */);
    if(!_Wf/* s1Mc */._){
      var _Wg/* s1Me */ = E(_Wf/* s1Mc */.a);
      if(_Wg/* s1Me */==(-2147483648)){
        _Wd/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _Wh/* s1Mf */ = E(_We/* s1Mb */);
        if(!_Wh/* s1Mf */._){
          var _Wi/* s1Mg */ = _Wh/* s1Mf */.a;
          return new T2(0,new T1(0,quot/* EXTERNAL */(_Wg/* s1Me */, _Wi/* s1Mg */)),new T1(0,_Wg/* s1Me */%_Wi/* s1Mg */));
        }else{
          _Wd/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(_Wg/* s1Me */));
          _We/* s1Mb */ = _Wh/* s1Mf */;
          continue;
        }
      }
    }else{
      var _Wj/* s1Mt */ = E(_We/* s1Mb */);
      if(!_Wj/* s1Mt */._){
        _Wd/* s1Ma */ = _Wf/* s1Mc */;
        _We/* s1Mb */ = new T1(1,I_fromInt/* EXTERNAL */(_Wj/* s1Mt */.a));
        continue;
      }else{
        var _Wk/* s1MA */ = I_quotRem/* EXTERNAL */(_Wf/* s1Mc */.a, _Wj/* s1Mt */.a);
        return new T2(0,new T1(1,_Wk/* s1MA */.a),new T1(1,_Wk/* s1MA */.b));
      }
    }
  }
},
_Wl/* $fIntegralInteger_$cquotRem */ = function(_Wm/* svug */, _Wn/* svuh */){
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_Wn/* svuh */, _RC/* GHC.Real.even1 */))){
    var _Wo/* svuj */ = B(_Wc/* GHC.Integer.Type.quotRemInteger */(_Wm/* svug */, _Wn/* svuh */));
    return new T2(0,_Wo/* svuj */.a,_Wo/* svuj */.b);
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_Wp/* $fIntegralInteger_$ctoInteger */ = function(_Wq/* svu9 */){
  return E(_Wq/* svu9 */);
},
_Wr/* $fNumInteger_$cfromInteger */ = function(_Ws/* s6HU */){
  return E(_Ws/* s6HU */);
},
_Wt/* $fNumInteger */ = {_:0,a:_Ki/* GHC.Integer.Type.plusInteger */,b:_LX/* GHC.Integer.Type.minusInteger */,c:_Sd/* GHC.Integer.Type.timesInteger */,d:_Ks/* GHC.Integer.Type.negateInteger */,e:_RT/* GHC.Integer.Type.absInteger */,f:_UO/* GHC.Integer.Type.signumInteger */,g:_Wr/* GHC.Num.$fNumInteger_$cfromInteger */},
_Wu/* neqInteger */ = function(_Wv/* s1GK */, _Ww/* s1GL */){
  var _Wx/* s1GM */ = E(_Wv/* s1GK */);
  if(!_Wx/* s1GM */._){
    var _Wy/* s1GN */ = _Wx/* s1GM */.a,
    _Wz/* s1GO */ = E(_Ww/* s1GL */);
    return (_Wz/* s1GO */._==0) ? _Wy/* s1GN */!=_Wz/* s1GO */.a : (I_compareInt/* EXTERNAL */(_Wz/* s1GO */.a, _Wy/* s1GN */)==0) ? false : true;
  }else{
    var _WA/* s1GU */ = _Wx/* s1GM */.a,
    _WB/* s1GV */ = E(_Ww/* s1GL */);
    return (_WB/* s1GV */._==0) ? (I_compareInt/* EXTERNAL */(_WA/* s1GU */, _WB/* s1GV */.a)==0) ? false : true : (I_compare/* EXTERNAL */(_WA/* s1GU */, _WB/* s1GV */.a)==0) ? false : true;
  }
},
_WC/* $fEqInteger */ = new T2(0,_Ru/* GHC.Integer.Type.eqInteger */,_Wu/* GHC.Integer.Type.neqInteger */),
_WD/* leInteger */ = function(_WE/* s1Gp */, _WF/* s1Gq */){
  var _WG/* s1Gr */ = E(_WE/* s1Gp */);
  if(!_WG/* s1Gr */._){
    var _WH/* s1Gs */ = _WG/* s1Gr */.a,
    _WI/* s1Gt */ = E(_WF/* s1Gq */);
    return (_WI/* s1Gt */._==0) ? _WH/* s1Gs */<=_WI/* s1Gt */.a : I_compareInt/* EXTERNAL */(_WI/* s1Gt */.a, _WH/* s1Gs */)>=0;
  }else{
    var _WJ/* s1GA */ = _WG/* s1Gr */.a,
    _WK/* s1GB */ = E(_WF/* s1Gq */);
    return (_WK/* s1GB */._==0) ? I_compareInt/* EXTERNAL */(_WJ/* s1GA */, _WK/* s1GB */.a)<=0 : I_compare/* EXTERNAL */(_WJ/* s1GA */, _WK/* s1GB */.a)<=0;
  }
},
_WL/* $fOrdInteger_$cmax */ = function(_WM/* s1HU */, _WN/* s1HV */){
  return (!B(_WD/* GHC.Integer.Type.leInteger */(_WM/* s1HU */, _WN/* s1HV */))) ? E(_WM/* s1HU */) : E(_WN/* s1HV */);
},
_WO/* $fOrdInteger_$cmin */ = function(_WP/* s1HR */, _WQ/* s1HS */){
  return (!B(_WD/* GHC.Integer.Type.leInteger */(_WP/* s1HR */, _WQ/* s1HS */))) ? E(_WQ/* s1HS */) : E(_WP/* s1HR */);
},
_WR/* compareInteger */ = function(_WS/* s1Hk */, _WT/* s1Hl */){
  var _WU/* s1Hm */ = E(_WS/* s1Hk */);
  if(!_WU/* s1Hm */._){
    var _WV/* s1Hn */ = _WU/* s1Hm */.a,
    _WW/* s1Ho */ = E(_WT/* s1Hl */);
    if(!_WW/* s1Ho */._){
      var _WX/* s1Hp */ = _WW/* s1Ho */.a;
      return (_WV/* s1Hn */!=_WX/* s1Hp */) ? (_WV/* s1Hn */>_WX/* s1Hp */) ? 2 : 0 : 1;
    }else{
      var _WY/* s1Hw */ = I_compareInt/* EXTERNAL */(_WW/* s1Ho */.a, _WV/* s1Hn */);
      return (_WY/* s1Hw */<=0) ? (_WY/* s1Hw */>=0) ? 1 : 2 : 0;
    }
  }else{
    var _WZ/* s1HB */ = _WU/* s1Hm */.a,
    _X0/* s1HC */ = E(_WT/* s1Hl */);
    if(!_X0/* s1HC */._){
      var _X1/* s1HF */ = I_compareInt/* EXTERNAL */(_WZ/* s1HB */, _X0/* s1HC */.a);
      return (_X1/* s1HF */>=0) ? (_X1/* s1HF */<=0) ? 1 : 2 : 0;
    }else{
      var _X2/* s1HM */ = I_compare/* EXTERNAL */(_WZ/* s1HB */, _X0/* s1HC */.a);
      return (_X2/* s1HM */>=0) ? (_X2/* s1HM */<=0) ? 1 : 2 : 0;
    }
  }
},
_X3/* $fOrdInteger */ = {_:0,a:_WC/* GHC.Integer.Type.$fEqInteger */,b:_WR/* GHC.Integer.Type.compareInteger */,c:_Lx/* GHC.Integer.Type.ltInteger */,d:_WD/* GHC.Integer.Type.leInteger */,e:_L1/* GHC.Integer.Type.gtInteger */,f:_Lp/* GHC.Integer.Type.geInteger */,g:_WL/* GHC.Integer.Type.$fOrdInteger_$cmax */,h:_WO/* GHC.Integer.Type.$fOrdInteger_$cmin */},
_X4/* $fRealInteger_$s$cfromInteger */ = function(_X5/* svmz */){
  return new T2(0,E(_X5/* svmz */),E(_KU/* GHC.Real.$fEnumRatio1 */));
},
_X6/* $fRealInteger */ = new T3(0,_Wt/* GHC.Num.$fNumInteger */,_X3/* GHC.Integer.Type.$fOrdInteger */,_X4/* GHC.Real.$fRealInteger_$s$cfromInteger */),
_X7/* $fIntegralInteger */ = {_:0,a:_X6/* GHC.Real.$fRealInteger */,b:_VE/* GHC.Enum.$fEnumInteger */,c:_W9/* GHC.Real.$fIntegralInteger_$cquot */,d:_RL/* GHC.Real.$fIntegralInteger_$crem */,e:_VQ/* GHC.Real.$fIntegralInteger_$cdiv */,f:_W6/* GHC.Real.$fIntegralInteger_$cmod */,g:_Wl/* GHC.Real.$fIntegralInteger_$cquotRem */,h:_W2/* GHC.Real.$fIntegralInteger_$cdivMod */,i:_Wp/* GHC.Real.$fIntegralInteger_$ctoInteger */},
_X8/* $fFractionalFixed1 */ = new T1(0,0),
_X9/* $fNumFixed5 */ = function(_Xa/* s6SxT */, _Xb/* s6SxU */, _Xc/* s6SxV */){
  var _Xd/* s6SxW */ = B(A1(_Xa/* s6SxT */,_Xb/* s6SxU */));
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_Xd/* s6SxW */, _X8/* Data.Fixed.$fFractionalFixed1 */))){
    return new F(function(){return _VI/* GHC.Integer.Type.divInteger */(B(_Sd/* GHC.Integer.Type.timesInteger */(_Xb/* s6SxU */, _Xc/* s6SxV */)), _Xd/* s6SxW */);});
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_Xe/* $w$s$cproperFraction */ = function(_Xf/* svn0 */, _Xg/* svn1 */, _Xh/* svn2 */){
  var _Xi/* svn3 */ = new T(function(){
    if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_Xh/* svn2 */, _RC/* GHC.Real.even1 */))){
      var _Xj/* svn5 */ = B(_Wc/* GHC.Integer.Type.quotRemInteger */(_Xg/* svn1 */, _Xh/* svn2 */));
      return new T2(0,_Xj/* svn5 */.a,_Xj/* svn5 */.b);
    }else{
      return E(_Pv/* GHC.Real.divZeroError */);
    }
  }),
  _Xk/* svne */ = new T(function(){
    return B(A2(_KZ/* GHC.Num.fromInteger */,B(_KX/* GHC.Real.$p1Real */(B(_KV/* GHC.Real.$p1Integral */(_Xf/* svn0 */)))), new T(function(){
      return E(E(_Xi/* svn3 */).a);
    })));
  });
  return new T2(0,_Xk/* svne */,new T(function(){
    return new T2(0,E(E(_Xi/* svn3 */).b),E(_Xh/* svn2 */));
  }));
},
_Xl/* - */ = function(_Xm/* s6FH */){
  return E(E(_Xm/* s6FH */).b);
},
_Xn/* $w$s$cfloor */ = function(_Xo/* svJO */, _Xp/* svJP */, _Xq/* svJQ */){
  var _Xr/* svJR */ = B(_Xe/* GHC.Real.$w$s$cproperFraction */(_Xo/* svJO */, _Xp/* svJP */, _Xq/* svJQ */)),
  _Xs/* svJS */ = _Xr/* svJR */.a,
  _Xt/* svJU */ = E(_Xr/* svJR */.b);
  if(!B(_Lx/* GHC.Integer.Type.ltInteger */(B(_Sd/* GHC.Integer.Type.timesInteger */(_Xt/* svJU */.a, _KU/* GHC.Real.$fEnumRatio1 */)), B(_Sd/* GHC.Integer.Type.timesInteger */(_RC/* GHC.Real.even1 */, _Xt/* svJU */.b))))){
    return E(_Xs/* svJS */);
  }else{
    var _Xu/* svK1 */ = B(_KX/* GHC.Real.$p1Real */(B(_KV/* GHC.Real.$p1Integral */(_Xo/* svJO */))));
    return new F(function(){return A3(_Xl/* GHC.Num.- */,_Xu/* svK1 */, _Xs/* svJS */, new T(function(){
      return B(A2(_KZ/* GHC.Num.fromInteger */,_Xu/* svK1 */, _KU/* GHC.Real.$fEnumRatio1 */));
    }));});
  }
},
_Xv/* slaT */ = 479723520,
_Xw/* slaU */ = 40233135,
_Xx/* slaV */ = new T2(1,_Xw/* slaU */,_6/* GHC.Types.[] */),
_Xy/* slaW */ = new T2(1,_Xv/* slaT */,_Xx/* slaV */),
_Xz/* posixDayLength1 */ = new T(function(){
  return B(_Kw/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _Xy/* slaW */));
}),
_XA/* posixSecondsToUTCTime1 */ = new T1(0,40587),
_XB/* $wposixSecondsToUTCTime */ = function(_XC/* slaX */){
  var _XD/* slaY */ = new T(function(){
    var _XE/* slaZ */ = B(_UT/* GHC.Real.$w$s$c/ */(_XC/* slaX */, _KU/* GHC.Real.$fEnumRatio1 */, _Uy/* Data.Fixed.$fHasResolutionE5 */, _KU/* GHC.Real.$fEnumRatio1 */)),
    _XF/* slb2 */ = B(_UT/* GHC.Real.$w$s$c/ */(_Xz/* Data.Time.Clock.POSIX.posixDayLength1 */, _KU/* GHC.Real.$fEnumRatio1 */, _Uy/* Data.Fixed.$fHasResolutionE5 */, _KU/* GHC.Real.$fEnumRatio1 */)),
    _XG/* slb5 */ = B(_UT/* GHC.Real.$w$s$c/ */(_XE/* slaZ */.a, _XE/* slaZ */.b, _XF/* slb2 */.a, _XF/* slb2 */.b));
    return B(_Xn/* GHC.Real.$w$s$cfloor */(_X7/* GHC.Real.$fIntegralInteger */, _XG/* slb5 */.a, _XG/* slb5 */.b));
  });
  return new T2(0,new T(function(){
    return B(_Ki/* GHC.Integer.Type.plusInteger */(_XA/* Data.Time.Clock.POSIX.posixSecondsToUTCTime1 */, _XD/* slaY */));
  }),new T(function(){
    return B(_LX/* GHC.Integer.Type.minusInteger */(_XC/* slaX */, B(_X9/* Data.Fixed.$fNumFixed5 */(_UZ/* Data.Fixed.$fHasResolutionE12_$cresolution */, B(_Sd/* GHC.Integer.Type.timesInteger */(_XD/* slaY */, _Uy/* Data.Fixed.$fHasResolutionE5 */)), _Xz/* Data.Time.Clock.POSIX.posixDayLength1 */))));
  }));
},
_XH/* getCPUTime2 */ = new T1(0,0),
_XI/* $wa1 */ = function(_XJ/* s3vS */, _/* EXTERNAL */){
  var _XK/* s3vX */ = __get/* EXTERNAL */(_XJ/* s3vS */, 0),
  _XL/* s3w3 */ = __get/* EXTERNAL */(_XJ/* s3vS */, 1),
  _XM/* s3w7 */ = Number/* EXTERNAL */(_XK/* s3vX */),
  _XN/* s3wb */ = jsTrunc/* EXTERNAL */(_XM/* s3w7 */),
  _XO/* s3wf */ = Number/* EXTERNAL */(_XL/* s3w3 */),
  _XP/* s3wj */ = jsTrunc/* EXTERNAL */(_XO/* s3wf */);
  return new T2(0,_XN/* s3wb */,_XP/* s3wj */);
},
_XQ/* getCTimeval_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");
}),
_XR/* slbq */ = 660865024,
_XS/* slbr */ = 465661287,
_XT/* slbs */ = new T2(1,_XS/* slbr */,_6/* GHC.Types.[] */),
_XU/* slbt */ = new T2(1,_XR/* slbq */,_XT/* slbs */),
_XV/* getPOSIXTime2 */ = new T(function(){
  return B(_Kw/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _XU/* slbt */));
}),
_XW/* getPOSIXTime1 */ = function(_/* EXTERNAL */){
  var _XX/* slby */ = __app0/* EXTERNAL */(E(_XQ/* Data.Time.Clock.CTimeval.getCTimeval_f1 */)),
  _XY/* slbB */ = B(_XI/* Data.Time.Clock.CTimeval.$wa1 */(_XX/* slby */, _/* EXTERNAL */));
  return new T(function(){
    var _XZ/* slbE */ = E(_XY/* slbB */);
    if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_XV/* Data.Time.Clock.POSIX.getPOSIXTime2 */, _X8/* Data.Fixed.$fFractionalFixed1 */))){
      return B(_Ki/* GHC.Integer.Type.plusInteger */(B(_Sd/* GHC.Integer.Type.timesInteger */(B(_MI/* GHC.Integer.Type.smallInteger */(E(_XZ/* slbE */.a))), _Uy/* Data.Fixed.$fHasResolutionE5 */)), B(_VI/* GHC.Integer.Type.divInteger */(B(_Sd/* GHC.Integer.Type.timesInteger */(B(_Sd/* GHC.Integer.Type.timesInteger */(B(_MI/* GHC.Integer.Type.smallInteger */(E(_XZ/* slbE */.b))), _Uy/* Data.Fixed.$fHasResolutionE5 */)), _Uy/* Data.Fixed.$fHasResolutionE5 */)), _XV/* Data.Time.Clock.POSIX.getPOSIXTime2 */))));
    }else{
      return E(_Pv/* GHC.Real.divZeroError */);
    }
  });
},
_Y0/* getStdRandom3 */ = new T1(0,12345),
_Y1/* getStdRandom2 */ = function(_/* EXTERNAL */){
  var _Y2/* sfpA */ = B(_XW/* Data.Time.Clock.POSIX.getPOSIXTime1 */(0)),
  _Y3/* sfpG */ = B(_UT/* GHC.Real.$w$s$c/ */(B(_XB/* Data.Time.Clock.POSIX.$wposixSecondsToUTCTime */(_Y2/* sfpA */)).b, _KU/* GHC.Real.$fEnumRatio1 */, _Uy/* Data.Fixed.$fHasResolutionE5 */, _KU/* GHC.Real.$fEnumRatio1 */)),
  _Y4/* sfpI */ = _Y3/* sfpG */.b;
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_Y4/* sfpI */, _Tx/* System.Random.getStdRandom4 */))){
    var _Y5/* sfpK */ = B(_Wc/* GHC.Integer.Type.quotRemInteger */(_Y3/* sfpG */.a, _Y4/* sfpI */));
    return new F(function(){return nMV/* EXTERNAL */(new T(function(){
      var _Y6/* sfpV */ = B(_UA/* GHC.Int.$w$cdivMod1 */((B(_Vt/* GHC.Integer.Type.integerToInt */(B(_Ki/* GHC.Integer.Type.plusInteger */(B(_Ki/* GHC.Integer.Type.plusInteger */(B(_Ki/* GHC.Integer.Type.plusInteger */(B(_Sd/* GHC.Integer.Type.timesInteger */(_Y5/* sfpK */.a, _Y0/* System.Random.getStdRandom3 */)), _Y5/* sfpK */.b)), _XH/* System.CPUTime.getCPUTime2 */)), _Tx/* System.Random.getStdRandom4 */))))>>>0&2147483647)>>>0&4294967295, 2147483562));
      return new T2(0,E(_Y6/* sfpV */.b)+1|0,B(_Tz/* GHC.Classes.modInt# */(E(_Y6/* sfpV */.a), 2147483398))+1|0);
    }));});
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_Y7/* theStdGen */ = new T(function(){
  return B(_44/* GHC.IO.unsafeDupablePerformIO */(_Y1/* System.Random.getStdRandom2 */));
}),
_Y8/* $fRandomDouble8 */ = function(_Y9/* sfTt */, _/* EXTERNAL */){
  var _Ya/* sfTM */ = mMV/* EXTERNAL */(E(_Y7/* System.Random.theStdGen */), function(_Yb/* sfTx */){
    var _Yc/* sfTy */ = E(_Y9/* sfTt */),
    _Yd/* sfTF */ = B(_Ug/* System.Random.$w$srandomRFloating2 */(E(_Yc/* sfTy */.a), E(_Yc/* sfTy */.b), _Yb/* sfTx */));
    return new T2(0,E(_Yd/* sfTF */.b),_Yd/* sfTF */.a);
  }),
  _Ye/* sfTQ */ = E(_Ya/* sfTM */);
  return _Ya/* sfTM */;
},
_Yf/* speedMot19 */ = 1,
_Yg/* speedMot18 */ = new T2(0,_Js/* Motion.Speed.speedMot14 */,_Yf/* Motion.Speed.speedMot19 */),
_Yh/* speedMot17 */ = function(_/* EXTERNAL */){
  return new F(function(){return _Y8/* System.Random.$fRandomDouble8 */(_Yg/* Motion.Speed.speedMot18 */, _/* EXTERNAL */);});
},
_Yi/* speedMot16 */ = new T1(1,_Yh/* Motion.Speed.speedMot17 */),
_Yj/* speedMot15 */ = new T(function(){
  return B(_rx/* Control.Monad.Skeleton.bone */(_Yi/* Motion.Speed.speedMot16 */));
}),
_Yk/* speedMot3 */ = 60,
_Yl/* speedMot2 */ = new T1(0,_Yk/* Motion.Speed.speedMot3 */),
_Ym/* speedMot22 */ = 100,
_Yn/* speedMot21 */ = new T1(0,_Ym/* Motion.Speed.speedMot22 */),
_Yo/* speedMot20 */ = new T2(0,_Yn/* Motion.Speed.speedMot21 */,_Yn/* Motion.Speed.speedMot21 */),
_Yp/* speedMot5 */ = -30,
_Yq/* speedMot4 */ = new T1(0,_Yp/* Motion.Speed.speedMot5 */),
_Yr/* speedMot8 */ = new T(function(){
  return  -0;
}),
_Ys/* speedMot7 */ = new T1(0,_Yr/* Motion.Speed.speedMot8 */),
_Yt/* speedMot6 */ = new T2(0,_Ys/* Motion.Speed.speedMot7 */,_Ys/* Motion.Speed.speedMot7 */),
_Yu/* $fFloatingDouble_$cpi */ = 3.141592653589793,
_Yv/* $s$fFloatingValue_$cpi */ = new T1(0,_Yu/* GHC.Float.$fFloatingDouble_$cpi */),
_Yw/* speedMot11 */ = 6,
_Yx/* speedMot10 */ = new T1(0,_Yw/* Motion.Speed.speedMot11 */),
_Yy/* speedMot9 */ = new T(function(){
  return B(_sg/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, _Yv/* Motion.Speed.$s$fFloatingValue_$cpi */, _Yx/* Motion.Speed.speedMot10 */));
}),
_Yz/* speedMot */ = function(_YA/* sRx9 */){
  var _YB/* sRxa */ = new T(function(){
    var _YC/* sRy2 */ = new T(function(){
      var _YD/* sRxb */ = E(_Yj/* Motion.Speed.speedMot15 */),
      _YE/* sRxc */ = _YD/* sRxb */.a,
      _YF/* sRxd */ = _YD/* sRxb */.b,
      _YG/* sRxZ */ = function(_YH/* sRxe */){
        var _YI/* sRxf */ = new T(function(){
          var _YJ/* sRxi */ = Math.log/* EXTERNAL */(E(_YH/* sRxe */));
          return Math.sqrt/* EXTERNAL */( -(_YJ/* sRxi */+_YJ/* sRxi */));
        }),
        _YK/* sRxW */ = function(_YL/* sRxm */){
          var _YM/* sRxn */ = new T(function(){
            var _YN/* sRxo */ = E(_YI/* sRxf */),
            _YO/* sRxq */ = E(_YL/* sRxm */);
            return _YN/* sRxo */*Math.sin/* EXTERNAL */(6.283185307179586*_YO/* sRxq */)+_YN/* sRxo */*Math.sin/* EXTERNAL */(6.283185307179586*_YO/* sRxq */);
          }),
          _YP/* sRxT */ = function(_YQ/* sRxA */){
            var _YR/* sRxR */ = new T(function(){
              var _YS/* sRxP */ = new T(function(){
                var _YT/* sRxN */ = new T(function(){
                  var _YU/* sRxM */ = new T(function(){
                    var _YV/* sRxH */ = new T(function(){
                      return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _Yq/* Motion.Speed.speedMot4 */, new T1(0,new T(function(){
                        return 4/(1-E(_YQ/* sRxA */));
                      }))));
                    }),
                    _YW/* sRxI */ = B(_GO/* Core.Shape.Internal.$wcenterRect */(new T1(0,_YM/* sRxn */), _YV/* sRxH */, _Yl/* Motion.Speed.speedMot2 */, _Yl/* Motion.Speed.speedMot2 */));
                    return new T3(0,_YW/* sRxI */.a,_YW/* sRxI */.b,_YW/* sRxI */.c);
                  });
                  return B(_rB/* Core.Render.Internal.fill1 */(_YA/* sRx9 */, _YU/* sRxM */));
                });
                return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_Yt/* Motion.Speed.speedMot6 */,_YT/* sRxN */,_7/* GHC.Tuple.() */)));
              });
              return B(_rx/* Control.Monad.Skeleton.bone */(new T3(6,_Yy/* Motion.Speed.speedMot9 */,_YS/* sRxP */,_7/* GHC.Tuple.() */)));
            });
            return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T3(5,_Ju/* Motion.Speed.speedMot12 */,_YR/* sRxR */,_7/* GHC.Tuple.() */));});
          };
          return new T2(0,E(_YE/* sRxc */),E(new T2(2,_YF/* sRxd */,new T1(1,_YP/* sRxT */))));
        };
        return new T2(0,E(_YE/* sRxc */),E(new T2(2,_YF/* sRxd */,new T1(1,_YK/* sRxW */))));
      };
      return new T2(0,E(_YE/* sRxc */),E(new T2(2,_YF/* sRxd */,new T1(1,_YG/* sRxZ */))));
    });
    return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_Yo/* Motion.Speed.speedMot20 */,_YC/* sRy2 */,_7/* GHC.Tuple.() */)));
  });
  return function(_YX/* sRy5 */, _YY/* sRy6 */){
    return new F(function(){return A1(_YY/* sRy6 */,new T2(0,new T2(0,_YB/* sRxa */,_Jp/* Motion.Speed.speedMot1 */),_YX/* sRy5 */));});
  };
},
_YZ/* lvl49 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_Jm/* Motion.Main.lvl46 */, _Yz/* Motion.Speed.speedMot */, _Jn/* Motion.Main.lvl47 */, _Jo/* Motion.Main.lvl48 */));
}),
_Z0/* $sreplicateM2 */ = function(_Z1/* sSgA */, _Z2/* sSgB */){
  var _Z3/* sSgC */ = E(_Z1/* sSgA */);
  if(!_Z3/* sSgC */._){
    return function(_Z4/* sSgE */){
      return new F(function(){return A1(_Z4/* sSgE */,new T2(0,_6/* GHC.Types.[] */,_Z2/* sSgB */));});
    };
  }else{
    var _Z5/* sSgT */ = function(_Z6/* sSgI */){
      var _Z7/* sSgJ */ = new T(function(){
        return B(A1(_Z3/* sSgC */.a,_Z6/* sSgI */));
      }),
      _Z8/* sSgS */ = function(_Z9/* sSgK */){
        var _Za/* sSgR */ = function(_Zb/* sSgL */){
          var _Zc/* sSgQ */ = new T(function(){
            var _Zd/* sSgM */ = E(_Zb/* sSgL */);
            return new T2(0,function(_Ze/* B1 */){
              return new T2(1,_Zd/* sSgM */.a,_Ze/* B1 */);
            },_Zd/* sSgM */.b);
          });
          return new F(function(){return A1(_Z9/* sSgK */,_Zc/* sSgQ */);});
        };
        return new F(function(){return A1(_Z7/* sSgJ */,_Za/* sSgR */);});
      };
      return E(_Z8/* sSgS */);
    };
    return new F(function(){return _55/* Core.World.Internal.$fApplicativeWorld3 */(_Z5/* sSgT */, function(_Ze/* B1 */){
      return new F(function(){return _Z0/* Motion.Change.$sreplicateM2 */(_Z3/* sSgC */.b, _Ze/* B1 */);});
    }, _Z2/* sSgB */);});
  }
},
_Zf/* $swhen1 */ = new T(function(){
  return B(_qY/* Control.Monad.Skeleton.$w$cpure */(_/* EXTERNAL */, _7/* GHC.Tuple.() */));
}),
_Zg/* $fNumInt_$c* */ = function(_Zh/* s6GP */, _Zi/* s6GQ */){
  return imul/* EXTERNAL */(E(_Zh/* s6GP */), E(_Zi/* s6GQ */))|0;
},
_Zj/* $fNumInt_$c+ */ = function(_Zk/* s6H3 */, _Zl/* s6H4 */){
  return E(_Zk/* s6H3 */)+E(_Zl/* s6H4 */)|0;
},
_Zm/* $fNumInt_$c- */ = function(_Zn/* s6GW */, _Zo/* s6GX */){
  return E(_Zn/* s6GW */)-E(_Zo/* s6GX */)|0;
},
_Zp/* $fNumInt_$cabs */ = function(_Zq/* s6Hg */){
  var _Zr/* s6Hh */ = E(_Zq/* s6Hg */);
  return (_Zr/* s6Hh */<0) ?  -_Zr/* s6Hh */ : E(_Zr/* s6Hh */);
},
_Zs/* $fNumInt_$cfromInteger */ = function(_Zt/* s6GJ */){
  return new F(function(){return _Vt/* GHC.Integer.Type.integerToInt */(_Zt/* s6GJ */);});
},
_Zu/* $fNumInt_$cnegate */ = function(_Zv/* s6GL */){
  return  -E(_Zv/* s6GL */);
},
_Zw/* $fNumInt1 */ = -1,
_Zx/* $fNumInt2 */ = 0,
_Zy/* $fNumInt3 */ = 1,
_Zz/* $fNumInt_$csignum */ = function(_ZA/* s6Ha */){
  var _ZB/* s6Hb */ = E(_ZA/* s6Ha */);
  return (_ZB/* s6Hb */>=0) ? (E(_ZB/* s6Hb */)==0) ? E(_Zx/* GHC.Num.$fNumInt2 */) : E(_Zy/* GHC.Num.$fNumInt3 */) : E(_Zw/* GHC.Num.$fNumInt1 */);
},
_ZC/* $fNumInt */ = {_:0,a:_Zj/* GHC.Num.$fNumInt_$c+ */,b:_Zm/* GHC.Num.$fNumInt_$c- */,c:_Zg/* GHC.Num.$fNumInt_$c* */,d:_Zu/* GHC.Num.$fNumInt_$cnegate */,e:_Zp/* GHC.Num.$fNumInt_$cabs */,f:_Zz/* GHC.Num.$fNumInt_$csignum */,g:_Zs/* GHC.Num.$fNumInt_$cfromInteger */},
_ZD/* $fRandomBool2 */ = function(_ZE/* sftN */){
  var _ZF/* sftO */ = B(_TO/* System.Random.$w$srandomIvalInteger */(_ZC/* GHC.Num.$fNumInt */, _Tx/* System.Random.getStdRandom4 */, _Ti/* System.Random.$fRandomBool3 */, _ZE/* sftN */));
  return new T2(0,E(_ZF/* sftO */.b),new T(function(){
    if(!E(_ZF/* sftO */.a)){
      return false;
    }else{
      return true;
    }
  }));
},
_ZG/* a10 */ = function(_ZH/* sShH */, _ZI/* sShI */, _ZJ/* sShJ */){
  var _ZK/* sShK */ = E(_ZH/* sShH */);
  if(!_ZK/* sShK */._){
    return new F(function(){return A1(_ZJ/* sShJ */,new T2(0,_7/* GHC.Tuple.() */,_ZI/* sShI */));});
  }else{
    var _ZL/* sSit */ = function(_/* EXTERNAL */){
      var _ZM/* sShP */ = E(_Y7/* System.Random.theStdGen */),
      _ZN/* sShR */ = mMV/* EXTERNAL */(_ZM/* sShP */, _ZD/* System.Random.$fRandomBool2 */);
      return new T(function(){
        var _ZO/* sSir */ = function(_ZP/* sShZ */){
          var _ZQ/* sSi3 */ = function(_ZR/* sSi4 */, _ZS/* sSi5 */, _ZT/* sSi6 */){
            var _ZU/* sSi7 */ = E(_ZR/* sSi4 */);
            if(!_ZU/* sSi7 */._){
              return new F(function(){return A1(_ZT/* sSi6 */,new T2(0,_7/* GHC.Tuple.() */,_ZS/* sSi5 */));});
            }else{
              var _ZV/* sSiq */ = function(_/* EXTERNAL */){
                var _ZW/* sSic */ = mMV/* EXTERNAL */(_ZM/* sShP */, _ZD/* System.Random.$fRandomBool2 */);
                return new T(function(){
                  return B(A(_jN/* Core.Ease.$wforceTo */,[E(_ZU/* sSi7 */.a).c, E(_ZW/* sSic */), _ZS/* sSi5 */, function(_ZX/* sSik */){
                    return new F(function(){return _ZQ/* sSi3 */(_ZU/* sSi7 */.b, E(_ZX/* sSik */).b, _ZT/* sSi6 */);});
                  }]));
                });
              };
              return new T1(0,_ZV/* sSiq */);
            }
          };
          return new F(function(){return _ZQ/* sSi3 */(_ZK/* sShK */.b, E(_ZP/* sShZ */).b, _ZJ/* sShJ */);});
        };
        return B(A(_jN/* Core.Ease.$wforceTo */,[E(_ZK/* sShK */.a).c, E(_ZN/* sShR */), _ZI/* sShI */, _ZO/* sSir */]));
      });
    };
    return new T1(0,_ZL/* sSit */);
  }
},
_ZY/* a */ = new T1(0,_/* EXTERNAL */),
_ZZ/* a1 */ = new T1(0,_7/* GHC.Tuple.() */),
_100/* a2 */ = new T2(0,E(_ZZ/* Motion.Change.a1 */),E(_ZY/* Motion.Change.a */)),
_101/* lvl */ = new T4(0,_aw/* GHC.Types.True */,_aw/* GHC.Types.True */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_102/* lvl1 */ = new T2(0,_aw/* GHC.Types.True */,_101/* Motion.Change.lvl */),
_103/* lvl2 */ = new T2(0,_102/* Motion.Change.lvl1 */,_6/* GHC.Types.[] */),
_104/* lvl3 */ = function(_105/* sSgV */, _106/* sSgW */){
  var _107/* sSh5 */ = function(_/* EXTERNAL */){
    var _108/* sSgY */ = nMV/* EXTERNAL */(_103/* Motion.Change.lvl2 */);
    return new T(function(){
      return B(A1(_106/* sSgW */,new T2(0,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_108/* sSgY */),_105/* sSgV */)));
    });
  };
  return new T1(0,_107/* sSh5 */);
},
_109/* lvl4 */ = new T2(1,_104/* Motion.Change.lvl3 */,_6/* GHC.Types.[] */),
_10a/* $wxs */ = function(_10b/* sSh6 */){
  var _10c/* sSh7 */ = E(_10b/* sSh6 */);
  return (_10c/* sSh7 */==1) ? E(_109/* Motion.Change.lvl4 */) : new T2(1,_104/* Motion.Change.lvl3 */,new T(function(){
    return B(_10a/* Motion.Change.$wxs */(_10c/* sSh7 */-1|0));
  }));
},
_10d/* a7 */ = new T(function(){
  return B(_10a/* Motion.Change.$wxs */(10));
}),
_10e/* dur */ = 10,
_10f/* e */ = function(_10g/* sSha */, _10h/* sShb */){
  return 1-B(A1(_10g/* sSha */,new T(function(){
    return Math.pow/* EXTERNAL */(2,  -((1-(1-E(_10h/* sShb */)))*10));
  })));
},
_10i/* $fRealDouble1 */ = new T1(0,1),
_10j/* encodeDoubleInteger */ = function(_10k/* s1LC */, _10l/* s1LD */){
  var _10m/* s1LE */ = E(_10k/* s1LC */);
  return (_10m/* s1LE */._==0) ? _10m/* s1LE */.a*Math.pow/* EXTERNAL */(2, _10l/* s1LD */) : I_toNumber/* EXTERNAL */(_10m/* s1LE */.a)*Math.pow/* EXTERNAL */(2, _10l/* s1LD */);
},
_10n/* rationalToDouble5 */ = new T1(0,0),
_10o/* $w$j1 */ = function(_10p/* s18QG */, _10q/* s18QH */, _10r/* s18QI */){
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_10r/* s18QI */, _10n/* GHC.Float.rationalToDouble5 */))){
    var _10s/* s18QK */ = B(_Wc/* GHC.Integer.Type.quotRemInteger */(_10q/* s18QH */, _10r/* s18QI */)),
    _10t/* s18QL */ = _10s/* s18QK */.a;
    switch(B(_WR/* GHC.Integer.Type.compareInteger */(B(_K9/* GHC.Integer.Type.shiftLInteger */(_10s/* s18QK */.b, 1)), _10r/* s18QI */))){
      case 0:
        return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(_10t/* s18QL */, _10p/* s18QG */);});
        break;
      case 1:
        if(!(B(_Vt/* GHC.Integer.Type.integerToInt */(_10t/* s18QL */))&1)){
          return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(_10t/* s18QL */, _10p/* s18QG */);});
        }else{
          return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(B(_Ki/* GHC.Integer.Type.plusInteger */(_10t/* s18QL */, _10i/* GHC.Float.$fRealDouble1 */)), _10p/* s18QG */);});
        }
        break;
      default:
        return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(B(_Ki/* GHC.Integer.Type.plusInteger */(_10t/* s18QL */, _10i/* GHC.Float.$fRealDouble1 */)), _10p/* s18QG */);});
    }
  }else{
    return E(_Pv/* GHC.Real.divZeroError */);
  }
},
_10u/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_10v/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_10w/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_10x/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_10u/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_10v/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_10w/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_10y/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_10x/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_10z/* $fExceptionPatternMatchFail1 */ = function(_10A/* s4nDQ */){
  return E(_10y/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_10B/* $fExceptionPatternMatchFail_$cfromException */ = function(_10C/* s4nE1 */){
  var _10D/* s4nE2 */ = E(_10C/* s4nE1 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_10D/* s4nE2 */.a)), _10z/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _10D/* s4nE2 */.b);});
},
_10E/* $fExceptionPatternMatchFail_$cshow */ = function(_10F/* s4nDT */){
  return E(E(_10F/* s4nDT */).a);
},
_10G/* $fExceptionPatternMatchFail_$ctoException */ = function(_10H/* B1 */){
  return new T2(0,_10I/* Control.Exception.Base.$fExceptionPatternMatchFail */,_10H/* B1 */);
},
_10J/* $fShowPatternMatchFail1 */ = function(_10K/* s4nzz */, _10L/* s4nzA */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_10K/* s4nzz */).a, _10L/* s4nzA */);});
},
_10M/* $fShowPatternMatchFail_$cshowList */ = function(_10N/* s4nDR */, _10O/* s4nDS */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_10J/* Control.Exception.Base.$fShowPatternMatchFail1 */, _10N/* s4nDR */, _10O/* s4nDS */);});
},
_10P/* $fShowPatternMatchFail_$cshowsPrec */ = function(_10Q/* s4nDW */, _10R/* s4nDX */, _10S/* s4nDY */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_10R/* s4nDX */).a, _10S/* s4nDY */);});
},
_10T/* $fShowPatternMatchFail */ = new T3(0,_10P/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_10E/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_10M/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_10I/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_10z/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_10T/* Control.Exception.Base.$fShowPatternMatchFail */,_10G/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_10B/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_10E/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_10U/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_10V/* lvl */ = function(_10W/* s2S2g */, _10X/* s2S2h */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_10X/* s2S2h */, _10W/* s2S2g */));
  }));});
},
_10Y/* throw1 */ = function(_10Z/* B2 */, _Ps/* B1 */){
  return new F(function(){return _10V/* GHC.Exception.lvl */(_10Z/* B2 */, _Ps/* B1 */);});
},
_110/* $wspan */ = function(_111/* s9wA */, _112/* s9wB */){
  var _113/* s9wC */ = E(_112/* s9wB */);
  if(!_113/* s9wC */._){
    return new T2(0,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */);
  }else{
    var _114/* s9wD */ = _113/* s9wC */.a;
    if(!B(A1(_111/* s9wA */,_114/* s9wD */))){
      return new T2(0,_6/* GHC.Types.[] */,_113/* s9wC */);
    }else{
      var _115/* s9wG */ = new T(function(){
        var _116/* s9wH */ = B(_110/* GHC.List.$wspan */(_111/* s9wA */, _113/* s9wC */.b));
        return new T2(0,_116/* s9wH */.a,_116/* s9wH */.b);
      });
      return new T2(0,new T2(1,_114/* s9wD */,new T(function(){
        return E(E(_115/* s9wG */).a);
      })),new T(function(){
        return E(E(_115/* s9wG */).b);
      }));
    }
  }
},
_117/* untangle1 */ = 32,
_118/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_119/* untangle3 */ = function(_11a/* s3JKg */){
  return (E(_11a/* s3JKg */)==124) ? false : true;
},
_11b/* untangle */ = function(_11c/* s3JL9 */, _11d/* s3JLa */){
  var _11e/* s3JLc */ = B(_110/* GHC.List.$wspan */(_119/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_11c/* s3JL9 */)))),
  _11f/* s3JLd */ = _11e/* s3JLc */.a,
  _11g/* s3JLf */ = function(_11h/* s3JLg */, _11i/* s3JLh */){
    var _11j/* s3JLk */ = new T(function(){
      var _11k/* s3JLj */ = new T(function(){
        return B(_2/* GHC.Base.++ */(_11d/* s3JLa */, new T(function(){
          return B(_2/* GHC.Base.++ */(_11i/* s3JLh */, _118/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _11k/* s3JLj */));
    },1);
    return new F(function(){return _2/* GHC.Base.++ */(_11h/* s3JLg */, _11j/* s3JLk */);});
  },
  _11l/* s3JLl */ = E(_11e/* s3JLc */.b);
  if(!_11l/* s3JLl */._){
    return new F(function(){return _11g/* s3JLf */(_11f/* s3JLd */, _6/* GHC.Types.[] */);});
  }else{
    if(E(_11l/* s3JLl */.a)==124){
      return new F(function(){return _11g/* s3JLf */(_11f/* s3JLd */, new T2(1,_117/* GHC.IO.Exception.untangle1 */,_11l/* s3JLl */.b));});
    }else{
      return new F(function(){return _11g/* s3JLf */(_11f/* s3JLd */, _6/* GHC.Types.[] */);});
    }
  }
},
_11m/* patError */ = function(_11n/* s4nFx */){
  return new F(function(){return _10Y/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_11b/* GHC.IO.Exception.untangle */(_11n/* s4nFx */, _10U/* Control.Exception.Base.lvl3 */));
  })), _10I/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_11o/* log2I */ = function(_11p/* s1Ju */){
  var _11q/* s1Jv */ = function(_11r/* s1Jw */, _11s/* s1Jx */){
    while(1){
      if(!B(_Lx/* GHC.Integer.Type.ltInteger */(_11r/* s1Jw */, _11p/* s1Ju */))){
        if(!B(_L1/* GHC.Integer.Type.gtInteger */(_11r/* s1Jw */, _11p/* s1Ju */))){
          if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_11r/* s1Jw */, _11p/* s1Ju */))){
            return new F(function(){return _11m/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});
          }else{
            return E(_11s/* s1Jx */);
          }
        }else{
          return _11s/* s1Jx */-1|0;
        }
      }else{
        var _11t/*  s1Jw */ = B(_K9/* GHC.Integer.Type.shiftLInteger */(_11r/* s1Jw */, 1)),
        _11u/*  s1Jx */ = _11s/* s1Jx */+1|0;
        _11r/* s1Jw */ = _11t/*  s1Jw */;
        _11s/* s1Jx */ = _11u/*  s1Jx */;
        continue;
      }
    }
  };
  return new F(function(){return _11q/* s1Jv */(_Kg/* GHC.Integer.Type.log2I1 */, 0);});
},
_11v/* integerLog2# */ = function(_11w/* s1JD */){
  var _11x/* s1JE */ = E(_11w/* s1JD */);
  if(!_11x/* s1JE */._){
    var _11y/* s1JG */ = _11x/* s1JE */.a>>>0;
    if(!_11y/* s1JG */){
      return -1;
    }else{
      var _11z/* s1JH */ = function(_11A/* s1JI */, _11B/* s1JJ */){
        while(1){
          if(_11A/* s1JI */>=_11y/* s1JG */){
            if(_11A/* s1JI */<=_11y/* s1JG */){
              if(_11A/* s1JI */!=_11y/* s1JG */){
                return new F(function(){return _11m/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_11B/* s1JJ */);
              }
            }else{
              return _11B/* s1JJ */-1|0;
            }
          }else{
            var _11C/*  s1JI */ = imul/* EXTERNAL */(_11A/* s1JI */, 2)>>>0,
            _11D/*  s1JJ */ = _11B/* s1JJ */+1|0;
            _11A/* s1JI */ = _11C/*  s1JI */;
            _11B/* s1JJ */ = _11D/*  s1JJ */;
            continue;
          }
        }
      };
      return new F(function(){return _11z/* s1JH */(1, 0);});
    }
  }else{
    return new F(function(){return _11o/* GHC.Integer.Type.log2I */(_11x/* s1JE */);});
  }
},
_11E/* integerLog2IsPowerOf2# */ = function(_11F/* s1JT */){
  var _11G/* s1JU */ = E(_11F/* s1JT */);
  if(!_11G/* s1JU */._){
    var _11H/* s1JW */ = _11G/* s1JU */.a>>>0;
    if(!_11H/* s1JW */){
      return new T2(0,-1,0);
    }else{
      var _11I/* s1JX */ = function(_11J/* s1JY */, _11K/* s1JZ */){
        while(1){
          if(_11J/* s1JY */>=_11H/* s1JW */){
            if(_11J/* s1JY */<=_11H/* s1JW */){
              if(_11J/* s1JY */!=_11H/* s1JW */){
                return new F(function(){return _11m/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_11K/* s1JZ */);
              }
            }else{
              return _11K/* s1JZ */-1|0;
            }
          }else{
            var _11L/*  s1JY */ = imul/* EXTERNAL */(_11J/* s1JY */, 2)>>>0,
            _11M/*  s1JZ */ = _11K/* s1JZ */+1|0;
            _11J/* s1JY */ = _11L/*  s1JY */;
            _11K/* s1JZ */ = _11M/*  s1JZ */;
            continue;
          }
        }
      };
      return new T2(0,B(_11I/* s1JX */(1, 0)),(_11H/* s1JW */&_11H/* s1JW */-1>>>0)>>>0&4294967295);
    }
  }else{
    var _11N/* s1Kc */ = _11G/* s1JU */.a;
    return new T2(0,B(_11v/* GHC.Integer.Type.integerLog2# */(_11G/* s1JU */)),I_compareInt/* EXTERNAL */(I_and/* EXTERNAL */(_11N/* s1Kc */, I_sub/* EXTERNAL */(_11N/* s1Kc */, I_fromInt/* EXTERNAL */(1))), 0));
  }
},
_11O/* andInteger */ = function(_11P/* s1Lf */, _11Q/* s1Lg */){
  while(1){
    var _11R/* s1Lh */ = E(_11P/* s1Lf */);
    if(!_11R/* s1Lh */._){
      var _11S/* s1Li */ = _11R/* s1Lh */.a,
      _11T/* s1Lj */ = E(_11Q/* s1Lg */);
      if(!_11T/* s1Lj */._){
        return new T1(0,(_11S/* s1Li */>>>0&_11T/* s1Lj */.a>>>0)>>>0&4294967295);
      }else{
        _11P/* s1Lf */ = new T1(1,I_fromInt/* EXTERNAL */(_11S/* s1Li */));
        _11Q/* s1Lg */ = _11T/* s1Lj */;
        continue;
      }
    }else{
      var _11U/* s1Lu */ = E(_11Q/* s1Lg */);
      if(!_11U/* s1Lu */._){
        _11P/* s1Lf */ = _11R/* s1Lh */;
        _11Q/* s1Lg */ = new T1(1,I_fromInt/* EXTERNAL */(_11U/* s1Lu */.a));
        continue;
      }else{
        return new T1(1,I_and/* EXTERNAL */(_11R/* s1Lh */.a, _11U/* s1Lu */.a));
      }
    }
  }
},
_11V/* roundingMode#1 */ = new T1(0,2),
_11W/* roundingMode# */ = function(_11X/* s1Pt */, _11Y/* s1Pu */){
  var _11Z/* s1Pv */ = E(_11X/* s1Pt */);
  if(!_11Z/* s1Pv */._){
    var _120/* s1Px */ = (_11Z/* s1Pv */.a>>>0&(2<<_11Y/* s1Pu */>>>0)-1>>>0)>>>0,
    _121/* s1PB */ = 1<<_11Y/* s1Pu */>>>0;
    return (_121/* s1PB */<=_120/* s1Px */) ? (_121/* s1PB */>=_120/* s1Px */) ? 1 : 2 : 0;
  }else{
    var _122/* s1PH */ = B(_11O/* GHC.Integer.Type.andInteger */(_11Z/* s1Pv */, B(_LX/* GHC.Integer.Type.minusInteger */(B(_K9/* GHC.Integer.Type.shiftLInteger */(_11V/* GHC.Integer.Type.roundingMode#1 */, _11Y/* s1Pu */)), _Kg/* GHC.Integer.Type.log2I1 */)))),
    _123/* s1PK */ = B(_K9/* GHC.Integer.Type.shiftLInteger */(_Kg/* GHC.Integer.Type.log2I1 */, _11Y/* s1Pu */));
    return (!B(_L1/* GHC.Integer.Type.gtInteger */(_123/* s1PK */, _122/* s1PH */))) ? (!B(_Lx/* GHC.Integer.Type.ltInteger */(_123/* s1PK */, _122/* s1PH */))) ? 1 : 2 : 0;
  }
},
_124/* shiftRInteger */ = function(_125/* s1Ja */, _126/* s1Jb */){
  while(1){
    var _127/* s1Jc */ = E(_125/* s1Ja */);
    if(!_127/* s1Jc */._){
      _125/* s1Ja */ = new T1(1,I_fromInt/* EXTERNAL */(_127/* s1Jc */.a));
      continue;
    }else{
      return new T1(1,I_shiftRight/* EXTERNAL */(_127/* s1Jc */.a, _126/* s1Jb */));
    }
  }
},
_128/* $w$sfromRat'' */ = function(_129/* s18QU */, _12a/* s18QV */, _12b/* s18QW */, _12c/* s18QX */){
  var _12d/* s18QY */ = B(_11E/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_12c/* s18QX */)),
  _12e/* s18QZ */ = _12d/* s18QY */.a;
  if(!E(_12d/* s18QY */.b)){
    var _12f/* s18Rp */ = B(_11v/* GHC.Integer.Type.integerLog2# */(_12b/* s18QW */));
    if(_12f/* s18Rp */<((_12e/* s18QZ */+_129/* s18QU */|0)-1|0)){
      var _12g/* s18Ru */ = _12e/* s18QZ */+(_129/* s18QU */-_12a/* s18QV */|0)|0;
      if(_12g/* s18Ru */>0){
        if(_12g/* s18Ru */>_12f/* s18Rp */){
          if(_12g/* s18Ru */<=(_12f/* s18Rp */+1|0)){
            if(!E(B(_11E/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_12b/* s18QW */)).b)){
              return 0;
            }else{
              return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(_10i/* GHC.Float.$fRealDouble1 */, _129/* s18QU */-_12a/* s18QV */|0);});
            }
          }else{
            return 0;
          }
        }else{
          var _12h/* s18RI */ = B(_124/* GHC.Integer.Type.shiftRInteger */(_12b/* s18QW */, _12g/* s18Ru */));
          switch(B(_11W/* GHC.Integer.Type.roundingMode# */(_12b/* s18QW */, _12g/* s18Ru */-1|0))){
            case 0:
              return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(_12h/* s18RI */, _129/* s18QU */-_12a/* s18QV */|0);});
              break;
            case 1:
              if(!(B(_Vt/* GHC.Integer.Type.integerToInt */(_12h/* s18RI */))&1)){
                return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(_12h/* s18RI */, _129/* s18QU */-_12a/* s18QV */|0);});
              }else{
                return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(B(_Ki/* GHC.Integer.Type.plusInteger */(_12h/* s18RI */, _10i/* GHC.Float.$fRealDouble1 */)), _129/* s18QU */-_12a/* s18QV */|0);});
              }
              break;
            default:
              return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(B(_Ki/* GHC.Integer.Type.plusInteger */(_12h/* s18RI */, _10i/* GHC.Float.$fRealDouble1 */)), _129/* s18QU */-_12a/* s18QV */|0);});
          }
        }
      }else{
        return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(_12b/* s18QW */, (_129/* s18QU */-_12a/* s18QV */|0)-_12g/* s18Ru */|0);});
      }
    }else{
      if(_12f/* s18Rp */>=_12a/* s18QV */){
        var _12i/* s18RX */ = B(_124/* GHC.Integer.Type.shiftRInteger */(_12b/* s18QW */, (_12f/* s18Rp */+1|0)-_12a/* s18QV */|0));
        switch(B(_11W/* GHC.Integer.Type.roundingMode# */(_12b/* s18QW */, _12f/* s18Rp */-_12a/* s18QV */|0))){
          case 0:
            return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(_12i/* s18RX */, ((_12f/* s18Rp */-_12e/* s18QZ */|0)+1|0)-_12a/* s18QV */|0);});
            break;
          case 2:
            return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(B(_Ki/* GHC.Integer.Type.plusInteger */(_12i/* s18RX */, _10i/* GHC.Float.$fRealDouble1 */)), ((_12f/* s18Rp */-_12e/* s18QZ */|0)+1|0)-_12a/* s18QV */|0);});
            break;
          default:
            if(!(B(_Vt/* GHC.Integer.Type.integerToInt */(_12i/* s18RX */))&1)){
              return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(_12i/* s18RX */, ((_12f/* s18Rp */-_12e/* s18QZ */|0)+1|0)-_12a/* s18QV */|0);});
            }else{
              return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(B(_Ki/* GHC.Integer.Type.plusInteger */(_12i/* s18RX */, _10i/* GHC.Float.$fRealDouble1 */)), ((_12f/* s18Rp */-_12e/* s18QZ */|0)+1|0)-_12a/* s18QV */|0);});
            }
        }
      }else{
        return new F(function(){return _10j/* GHC.Integer.Type.encodeDoubleInteger */(_12b/* s18QW */,  -_12e/* s18QZ */);});
      }
    }
  }else{
    var _12j/* s18R3 */ = B(_11v/* GHC.Integer.Type.integerLog2# */(_12b/* s18QW */))-_12e/* s18QZ */|0,
    _12k/* s18R4 */ = function(_12l/* s18R5 */){
      var _12m/* s18R6 */ = function(_12n/* s18R7 */, _12o/* s18R8 */){
        if(!B(_WD/* GHC.Integer.Type.leInteger */(B(_K9/* GHC.Integer.Type.shiftLInteger */(_12o/* s18R8 */, _12a/* s18QV */)), _12n/* s18R7 */))){
          return new F(function(){return _10o/* GHC.Float.$w$j1 */(_12l/* s18R5 */-_12a/* s18QV */|0, _12n/* s18R7 */, _12o/* s18R8 */);});
        }else{
          return new F(function(){return _10o/* GHC.Float.$w$j1 */((_12l/* s18R5 */-_12a/* s18QV */|0)+1|0, _12n/* s18R7 */, B(_K9/* GHC.Integer.Type.shiftLInteger */(_12o/* s18R8 */, 1)));});
        }
      };
      if(_12l/* s18R5 */>=_12a/* s18QV */){
        if(_12l/* s18R5 */!=_12a/* s18QV */){
          return new F(function(){return _12m/* s18R6 */(_12b/* s18QW */, new T(function(){
            return B(_K9/* GHC.Integer.Type.shiftLInteger */(_12c/* s18QX */, _12l/* s18R5 */-_12a/* s18QV */|0));
          }));});
        }else{
          return new F(function(){return _12m/* s18R6 */(_12b/* s18QW */, _12c/* s18QX */);});
        }
      }else{
        return new F(function(){return _12m/* s18R6 */(new T(function(){
          return B(_K9/* GHC.Integer.Type.shiftLInteger */(_12b/* s18QW */, _12a/* s18QV */-_12l/* s18R5 */|0));
        }), _12c/* s18QX */);});
      }
    };
    if(_129/* s18QU */>_12j/* s18R3 */){
      return new F(function(){return _12k/* s18R4 */(_129/* s18QU */);});
    }else{
      return new F(function(){return _12k/* s18R4 */(_12j/* s18R3 */);});
    }
  }
},
_12p/* rationalToDouble1 */ = new T(function(){
  return 0/0;
}),
_12q/* rationalToDouble2 */ = new T(function(){
  return -1/0;
}),
_12r/* rationalToDouble3 */ = new T(function(){
  return 1/0;
}),
_12s/* rationalToDouble4 */ = 0,
_12t/* rationalToDouble */ = function(_12u/* s197E */, _12v/* s197F */){
  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_12v/* s197F */, _10n/* GHC.Float.rationalToDouble5 */))){
    if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_12u/* s197E */, _10n/* GHC.Float.rationalToDouble5 */))){
      if(!B(_Lx/* GHC.Integer.Type.ltInteger */(_12u/* s197E */, _10n/* GHC.Float.rationalToDouble5 */))){
        return new F(function(){return _128/* GHC.Float.$w$sfromRat'' */(-1021, 53, _12u/* s197E */, _12v/* s197F */);});
      }else{
        return  -B(_128/* GHC.Float.$w$sfromRat'' */(-1021, 53, B(_Ks/* GHC.Integer.Type.negateInteger */(_12u/* s197E */)), _12v/* s197F */));
      }
    }else{
      return E(_12s/* GHC.Float.rationalToDouble4 */);
    }
  }else{
    return (!B(_Ru/* GHC.Integer.Type.eqInteger */(_12u/* s197E */, _10n/* GHC.Float.rationalToDouble5 */))) ? (!B(_Lx/* GHC.Integer.Type.ltInteger */(_12u/* s197E */, _10n/* GHC.Float.rationalToDouble5 */))) ? E(_12r/* GHC.Float.rationalToDouble3 */) : E(_12q/* GHC.Float.rationalToDouble2 */) : E(_12p/* GHC.Float.rationalToDouble1 */);
  }
},
_12w/* $fFractionalDouble_$cfromRational */ = function(_12x/* s197P */){
  var _12y/* s197Q */ = E(_12x/* s197P */);
  return new F(function(){return _12t/* GHC.Float.rationalToDouble */(_12y/* s197Q */.a, _12y/* s197Q */.b);});
},
_12z/* $fFractionalDouble_$crecip */ = function(_12A/* s191m */){
  return 1/E(_12A/* s191m */);
},
_12B/* $fNumDouble_$cabs */ = function(_12C/* s190N */){
  var _12D/* s190O */ = E(_12C/* s190N */),
  _12E/* s190Q */ = E(_12D/* s190O */);
  return (_12E/* s190Q */==0) ? E(_12s/* GHC.Float.rationalToDouble4 */) : (_12E/* s190Q */<=0) ?  -_12E/* s190Q */ : E(_12D/* s190O */);
},
_12F/* $fNumDouble_$cfromInteger */ = function(_12G/* s190E */){
  return new F(function(){return _T6/* GHC.Integer.Type.doubleFromInteger */(_12G/* s190E */);});
},
_12H/* $fNumDouble1 */ = 1,
_12I/* $fNumDouble2 */ = -1,
_12J/* $fNumDouble_$csignum */ = function(_12K/* s190G */){
  var _12L/* s190H */ = E(_12K/* s190G */);
  return (_12L/* s190H */<=0) ? (_12L/* s190H */>=0) ? E(_12L/* s190H */) : E(_12I/* GHC.Float.$fNumDouble2 */) : E(_12H/* GHC.Float.$fNumDouble1 */);
},
_12M/* minusDouble */ = function(_12N/* s18yR */, _12O/* s18yS */){
  return E(_12N/* s18yR */)-E(_12O/* s18yS */);
},
_12P/* $fNumDouble */ = {_:0,a:_tr/* GHC.Float.plusDouble */,b:_12M/* GHC.Float.minusDouble */,c:_Aq/* GHC.Float.timesDouble */,d:_G3/* GHC.Float.negateDouble */,e:_12B/* GHC.Float.$fNumDouble_$cabs */,f:_12J/* GHC.Float.$fNumDouble_$csignum */,g:_12F/* GHC.Float.$fNumDouble_$cfromInteger */},
_12Q/* $fFractionalDouble */ = new T4(0,_12P/* GHC.Float.$fNumDouble */,_iE/* GHC.Float.divideDouble */,_12z/* GHC.Float.$fFractionalDouble_$crecip */,_12w/* GHC.Float.$fFractionalDouble_$cfromRational */),
_12R/* $fEqDouble_$c/= */ = function(_12S/* scFX */, _12T/* scFY */){
  return (E(_12S/* scFX */)!=E(_12T/* scFY */)) ? true : false;
},
_12U/* $fEqDouble_$c== */ = function(_12V/* scFQ */, _12W/* scFR */){
  return E(_12V/* scFQ */)==E(_12W/* scFR */);
},
_12X/* $fEqDouble */ = new T2(0,_12U/* GHC.Classes.$fEqDouble_$c== */,_12R/* GHC.Classes.$fEqDouble_$c/= */),
_12Y/* $fOrdDouble_$c< */ = function(_12Z/* scIa */, _130/* scIb */){
  return E(_12Z/* scIa */)<E(_130/* scIb */);
},
_131/* $fOrdDouble_$c<= */ = function(_132/* scI3 */, _133/* scI4 */){
  return E(_132/* scI3 */)<=E(_133/* scI4 */);
},
_134/* $fOrdDouble_$c> */ = function(_135/* scHW */, _136/* scHX */){
  return E(_135/* scHW */)>E(_136/* scHX */);
},
_137/* $fOrdDouble_$c>= */ = function(_138/* scHP */, _139/* scHQ */){
  return E(_138/* scHP */)>=E(_139/* scHQ */);
},
_13a/* $fOrdDouble_$ccompare */ = function(_13b/* scIh */, _13c/* scIi */){
  var _13d/* scIj */ = E(_13b/* scIh */),
  _13e/* scIl */ = E(_13c/* scIi */);
  return (_13d/* scIj */>=_13e/* scIl */) ? (_13d/* scIj */!=_13e/* scIl */) ? 2 : 1 : 0;
},
_13f/* $fOrdDouble_$cmax */ = function(_13g/* scIz */, _13h/* scIA */){
  var _13i/* scIB */ = E(_13g/* scIz */),
  _13j/* scID */ = E(_13h/* scIA */);
  return (_13i/* scIB */>_13j/* scID */) ? E(_13i/* scIB */) : E(_13j/* scID */);
},
_13k/* $fOrdDouble_$cmin */ = function(_13l/* scIr */, _13m/* scIs */){
  var _13n/* scIt */ = E(_13l/* scIr */),
  _13o/* scIv */ = E(_13m/* scIs */);
  return (_13n/* scIt */>_13o/* scIv */) ? E(_13o/* scIv */) : E(_13n/* scIt */);
},
_13p/* $fOrdDouble */ = {_:0,a:_12X/* GHC.Classes.$fEqDouble */,b:_13a/* GHC.Classes.$fOrdDouble_$ccompare */,c:_12Y/* GHC.Classes.$fOrdDouble_$c< */,d:_131/* GHC.Classes.$fOrdDouble_$c<= */,e:_134/* GHC.Classes.$fOrdDouble_$c> */,f:_137/* GHC.Classes.$fOrdDouble_$c>= */,g:_13f/* GHC.Classes.$fOrdDouble_$cmax */,h:_13k/* GHC.Classes.$fOrdDouble_$cmin */},
_13q/* lvl8 */ = -1,
_13r/* $p1Fractional */ = function(_13s/* svdN */){
  return E(E(_13s/* svdN */).a);
},
_13t/* + */ = function(_13u/* s6Fy */){
  return E(E(_13u/* s6Fy */).a);
},
_13v/* $wnumericEnumFrom */ = function(_13w/* svLB */, _13x/* svLC */){
  var _13y/* svLD */ = E(_13x/* svLC */),
  _13z/* svLK */ = new T(function(){
    var _13A/* svLE */ = B(_13r/* GHC.Real.$p1Fractional */(_13w/* svLB */)),
    _13B/* svLH */ = B(_13v/* GHC.Real.$wnumericEnumFrom */(_13w/* svLB */, B(A3(_13t/* GHC.Num.+ */,_13A/* svLE */, _13y/* svLD */, new T(function(){
      return B(A2(_KZ/* GHC.Num.fromInteger */,_13A/* svLE */, _KU/* GHC.Real.$fEnumRatio1 */));
    })))));
    return new T2(1,_13B/* svLH */.a,_13B/* svLH */.b);
  });
  return new T2(0,_13y/* svLD */,_13z/* svLK */);
},
_13C/* / */ = function(_13D/* svdT */){
  return E(E(_13D/* svdT */).b);
},
_13E/* <= */ = function(_13F/* scCl */){
  return E(E(_13F/* scCl */).d);
},
_13G/* takeWhile */ = function(_13H/* s9yw */, _13I/* s9yx */){
  var _13J/* s9yy */ = E(_13I/* s9yx */);
  if(!_13J/* s9yy */._){
    return __Z/* EXTERNAL */;
  }else{
    var _13K/* s9yz */ = _13J/* s9yy */.a;
    return (!B(A1(_13H/* s9yw */,_13K/* s9yz */))) ? __Z/* EXTERNAL */ : new T2(1,_13K/* s9yz */,new T(function(){
      return B(_13G/* GHC.List.takeWhile */(_13H/* s9yw */, _13J/* s9yy */.b));
    }));
  }
},
_13L/* numericEnumFromTo */ = function(_13M/* svMm */, _13N/* svMn */, _13O/* svMo */, _13P/* svMp */){
  var _13Q/* svMq */ = B(_13v/* GHC.Real.$wnumericEnumFrom */(_13N/* svMn */, _13O/* svMo */)),
  _13R/* svMt */ = new T(function(){
    var _13S/* svMu */ = B(_13r/* GHC.Real.$p1Fractional */(_13N/* svMn */)),
    _13T/* svMx */ = new T(function(){
      return B(A3(_13C/* GHC.Real./ */,_13N/* svMn */, new T(function(){
        return B(A2(_KZ/* GHC.Num.fromInteger */,_13S/* svMu */, _KU/* GHC.Real.$fEnumRatio1 */));
      }), new T(function(){
        return B(A2(_KZ/* GHC.Num.fromInteger */,_13S/* svMu */, _Sv/* GHC.Real.even2 */));
      })));
    });
    return B(A3(_13t/* GHC.Num.+ */,_13S/* svMu */, _13P/* svMp */, _13T/* svMx */));
  });
  return new F(function(){return _13G/* GHC.List.takeWhile */(function(_13U/* svMy */){
    return new F(function(){return A3(_13E/* GHC.Classes.<= */,_13M/* svMm */, _13U/* svMy */, _13R/* svMt */);});
  }, new T2(1,_13Q/* svMq */.a,_13Q/* svMq */.b));});
},
_13V/* x */ = 1,
_13W/* lvl9 */ = new T(function(){
  return B(_13L/* GHC.Real.numericEnumFromTo */(_13p/* GHC.Classes.$fOrdDouble */, _12Q/* GHC.Float.$fFractionalDouble */, _13q/* Motion.Change.lvl8 */, _13V/* Motion.Change.x */));
}),
_13X/* go */ = function(_13Y/* sShn */){
  var _13Z/* sSho */ = E(_13Y/* sShn */);
  if(!_13Z/* sSho */._){
    return __Z/* EXTERNAL */;
  }else{
    var _140/* sShr */ = new T(function(){
      return E(_13Z/* sSho */.a)*100;
    }),
    _141/* sShv */ = new T(function(){
      return B(_13X/* Motion.Change.go */(_13Z/* sSho */.b));
    }),
    _142/* sShw */ = function(_143/* sShx */){
      var _144/* sShy */ = E(_143/* sShx */);
      return (_144/* sShy */._==0) ? E(_141/* sShv */) : new T2(1,new T2(0,_140/* sShr */,new T(function(){
        return E(_144/* sShy */.a)*100;
      })),new T(function(){
        return B(_142/* sShw */(_144/* sShy */.b));
      }));
    };
    return new F(function(){return _142/* sShw */(_13W/* Motion.Change.lvl9 */);});
  }
},
_145/* lvl10 */ = new T(function(){
  return B(_13X/* Motion.Change.go */(_13W/* Motion.Change.lvl9 */));
}),
_146/* lvl11 */ = 1.5,
_147/* lvl12 */ = 15,
_148/* lvl13 */ = 50,
_149/* lvl14 */ = 100,
_14a/* lvl15 */ = new T4(0,_13V/* Motion.Change.x */,_13V/* Motion.Change.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_14b/* lvl16 */ = new T2(0,_13V/* Motion.Change.x */,_14a/* Motion.Change.lvl15 */),
_14c/* lvl17 */ = new T2(0,_14b/* Motion.Change.lvl16 */,_6/* GHC.Types.[] */),
_14d/* a8 */ = 100,
_14e/* lvl5 */ = new T1(0,_14d/* Motion.Change.a8 */),
_14f/* lvl6 */ = new T2(0,_14e/* Motion.Change.lvl5 */,_14e/* Motion.Change.lvl5 */),
_14g/* a9 */ = 3,
_14h/* lvl7 */ = new T1(0,_14g/* Motion.Change.a9 */),
_14i/* valueIO1 */ = function(_14j/* sb7e */, _/* EXTERNAL */){
  var _14k/* sb7g */ = E(_14j/* sb7e */);
  switch(_14k/* sb7g */._){
    case 0:
      return new T1(1,_14k/* sb7g */.a);
    case 1:
      var _14l/* sb7k */ = B(A1(_14k/* sb7g */.a,_/* EXTERNAL */));
      return new T1(1,_14l/* sb7k */);
    case 2:
      var _14m/* sb7w */ = rMV/* EXTERNAL */(E(E(_14k/* sb7g */.a).c)),
      _14n/* sb7z */ = E(_14m/* sb7w */);
      if(!_14n/* sb7z */._){
        var _14o/* sb7D */ = new T(function(){
          return B(A1(_14k/* sb7g */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_14n/* sb7z */.a));
          })));
        });
        return new T1(1,_14o/* sb7D */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
      break;
    default:
      var _14p/* sb7O */ = rMV/* EXTERNAL */(E(E(_14k/* sb7g */.a).c)),
      _14q/* sb7R */ = E(_14p/* sb7O */);
      if(!_14q/* sb7R */._){
        var _14r/* sb7X */ = B(A2(_14k/* sb7g */.b,E(_14q/* sb7R */.a).a, _/* EXTERNAL */));
        return new T1(1,_14r/* sb7X */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
  }
},
_14s/* changeMot1 */ = function(_14t/* sSiu */, _14u/* sSiv */){
  var _14v/* sSiw */ = new T(function(){
    return B(_Z0/* Motion.Change.$sreplicateM2 */(_10d/* Motion.Change.a7 */, _14u/* sSiv */));
  }),
  _14w/* sSix */ = function(_14x/* sSiy */, _14y/* sSiz */){
    var _14z/* sSiA */ = E(_14x/* sSiy */);
    if(!_14z/* sSiA */._){
      return E(_100/* Motion.Change.a2 */);
    }else{
      var _14A/* sSiD */ = E(_14y/* sSiz */);
      if(!_14A/* sSiD */._){
        return E(_100/* Motion.Change.a2 */);
      }else{
        var _14B/* sSiG */ = E(_14A/* sSiD */.a),
        _14C/* sSiJ */ = new T(function(){
          return B(_Iq/* Core.Ease.morph */(_14z/* sSiA */.a));
        }),
        _14D/* sSiM */ = B(_rx/* Control.Monad.Skeleton.bone */(new T1(1,function(_/* EXTERNAL */){
          return new F(function(){return _14i/* Core.Ease.valueIO1 */(_14C/* sSiJ */, _/* EXTERNAL */);});
        }))),
        _14E/* sSiP */ = new T(function(){
          return B(_14w/* sSix */(_14z/* sSiA */.b, _14A/* sSiD */.b));
        }),
        _14F/* sSiQ */ = new T(function(){
          return B(_rB/* Core.Render.Internal.fill1 */(_14t/* sSiu */, new T(function(){
            var _14G/* sSiT */ = B(_GO/* Core.Shape.Internal.$wcenterRect */(new T1(0,_14B/* sSiG */.a), new T1(0,_14B/* sSiG */.b), _14e/* Motion.Change.lvl5 */, _14e/* Motion.Change.lvl5 */));
            return new T3(0,_14G/* sSiT */.a,_14G/* sSiT */.b,_14G/* sSiT */.c);
          })));
        });
        return new T2(0,E(_14D/* sSiM */.a),E(new T2(2,new T2(2,_14D/* sSiM */.b,new T1(1,function(_14H/* sSiY */){
          var _14I/* sSiZ */ = E(_14H/* sSiY */);
          return (_14I/* sSiZ */._==0) ? E(_Zf/* Motion.Change.$swhen1 */) : (!E(_14I/* sSiZ */.a)) ? E(_Zf/* Motion.Change.$swhen1 */) : E(_14F/* sSiQ */);
        })),new T1(1,function(_14J/* sSj5 */){
          return E(_14E/* sSiP */);
        }))));
      }
    }
  },
  _14K/* sSkO */ = function(_14L/* sSj9 */){
    var _14M/* sSkN */ = function(_14N/* sSja */){
      var _14O/* sSjb */ = E(_14N/* sSja */),
      _14P/* sSjc */ = _14O/* sSjb */.a,
      _14Q/* sSkM */ = function(_/* EXTERNAL */){
        var _14R/* sSjf */ = nMV/* EXTERNAL */(_14c/* Motion.Change.lvl17 */);
        return new T(function(){
          var _14S/* sSjj */ = new T(function(){
            return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _10e/* Motion.Change.dur */, _10f/* Motion.Change.e */, _14R/* sSjf */, _13V/* Motion.Change.x */, _Ac/* Core.Ease.easeTo1 */));
          }),
          _14T/* sSjk */ = new T(function(){
            return B(_jN/* Core.Ease.$wforceTo */(_14R/* sSjf */, _146/* Motion.Change.lvl11 */));
          }),
          _14U/* sSjl */ = function(_14V/* sSjm */, _14W/* sSjn */){
            var _14X/* sSjo */ = function(_14Y/* sSjp */){
              return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_147/* Motion.Change.lvl12 */, E(_14Y/* sSjp */).b, _14W/* sSjn */);});
            },
            _14Z/* sSjt */ = function(_150/* sSju */){
              return new F(function(){return A2(_14S/* sSjj */,E(_150/* sSju */).b, _14X/* sSjo */);});
            };
            return new F(function(){return _ZG/* Motion.Change.a10 */(_14P/* sSjc */, _14V/* sSjm */, function(_151/* sSjy */){
              return new F(function(){return A2(_14T/* sSjk */,E(_151/* sSjy */).b, _14Z/* sSjt */);});
            });});
          },
          _152/* sSjD */ = new T(function(){
            var _153/* sSjF */ = function(_154/* sSjG */){
              var _155/* sSjH */ = E(_154/* sSjG */);
              return (_155/* sSjH */==1) ? E(new T2(1,_14U/* sSjl */,_6/* GHC.Types.[] */)) : new T2(1,_14U/* sSjl */,new T(function(){
                return B(_153/* sSjF */(_155/* sSjH */-1|0));
              }));
            };
            return B(_153/* sSjF */(4));
          }),
          _156/* sSjK */ = function(_157/* sSjL */){
            var _158/* sSjM */ = new T(function(){
              return B(_Z0/* Motion.Change.$sreplicateM2 */(_152/* sSjD */, _157/* sSjL */));
            }),
            _159/* sSkx */ = function(_15a/* sSjN */){
              var _15b/* sSjO */ = function(_15c/* sSjP */){
                return new F(function(){return A2(_156/* sSjK */,E(_15c/* sSjP */).b, _15a/* sSjN */);});
              },
              _15d/* sSjT */ = function(_15e/* sSjU */){
                return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_149/* Motion.Change.lvl14 */, E(_15e/* sSjU */).b, _15b/* sSjO */);});
              },
              _15f/* sSjY */ = function(_15g/* sSjZ */){
                return new F(function(){return A2(_14S/* sSjj */,E(_15g/* sSjZ */).b, _15d/* sSjT */);});
              },
              _15h/* sSk3 */ = function(_15i/* sSk4 */){
                return new F(function(){return A2(_14T/* sSjk */,E(_15i/* sSk4 */).b, _15f/* sSjY */);});
              },
              _15j/* sSk8 */ = function(_15k/* sSk9 */){
                return new F(function(){return _ZG/* Motion.Change.a10 */(_14P/* sSjc */, E(_15k/* sSk9 */).b, _15h/* sSk3 */);});
              },
              _15l/* sSkd */ = function(_15m/* sSke */){
                return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_148/* Motion.Change.lvl13 */, E(_15m/* sSke */).b, _15j/* sSk8 */);});
              },
              _15n/* sSki */ = function(_15o/* sSkj */){
                return new F(function(){return A2(_14S/* sSjj */,E(_15o/* sSkj */).b, _15l/* sSkd */);});
              },
              _15p/* sSkn */ = function(_15q/* sSko */){
                return new F(function(){return A2(_14T/* sSjk */,E(_15q/* sSko */).b, _15n/* sSki */);});
              };
              return new F(function(){return A1(_158/* sSjM */,function(_15r/* sSks */){
                return new F(function(){return _ZG/* Motion.Change.a10 */(_14P/* sSjc */, E(_15r/* sSks */).b, _15p/* sSkn */);});
              });});
            };
            return E(_159/* sSkx */);
          },
          _15s/* sSkI */ = new T(function(){
            var _15t/* sSkG */ = new T(function(){
              var _15u/* sSky */ = new T3(0,_10e/* Motion.Change.dur */,_10f/* Motion.Change.e */,_14R/* sSjf */);
              return B(_rx/* Control.Monad.Skeleton.bone */(new T3(7,new T2(0,new T(function(){
                return B(_sg/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, new T2(2,_15u/* sSky */,_2E/* GHC.Base.id */), _14h/* Motion.Change.lvl7 */));
              }),new T(function(){
                return B(_sg/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, new T2(2,_15u/* sSky */,_2E/* GHC.Base.id */), _14h/* Motion.Change.lvl7 */));
              })),new T(function(){
                return B(_14w/* sSix */(_14P/* sSjc */, _145/* Motion.Change.lvl10 */));
              }),_7/* GHC.Tuple.() */)));
            });
            return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_14f/* Motion.Change.lvl6 */,_15t/* sSkG */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_14L/* sSj9 */,new T2(0,new T2(0,_15s/* sSkI */,_156/* sSjK */),_14O/* sSjb */.b)));
        });
      };
      return new T1(0,_14Q/* sSkM */);
    };
    return new F(function(){return A1(_14v/* sSiw */,_14M/* sSkN */);});
  };
  return E(_14K/* sSkO */);
},
_15v/* lvl50 */ = 0.1,
_15w/* lvl51 */ = new T1(0,_15v/* Motion.Main.lvl50 */),
_15x/* lvl52 */ = new T4(0,_15w/* Motion.Main.lvl51 */,_Jh/* Motion.Main.lvl41 */,_Jh/* Motion.Main.lvl41 */,_Al/* Motion.Main.lvl11 */),
_15y/* lvl53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Change"));
}),
_15z/* lvl54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("easeOutExpo"));
}),
_15A/* lvl55 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_15x/* Motion.Main.lvl52 */, _14s/* Motion.Change.changeMot1 */, _15y/* Motion.Main.lvl53 */, _15z/* Motion.Main.lvl54 */));
}),
_15B/* lvl56 */ = new T4(0,_Al/* Motion.Main.lvl11 */,_AC/* Motion.Main.lvl23 */,_yT/* Motion.Main.lvl4 */,_Al/* Motion.Main.lvl11 */),
_15C/* lvl57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Trot"));
}),
_15D/* lvl58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("rotateAt corner easeInCubic & smoothStep scroll"));
}),
_15E/* cubic */ = function(_15F/* sbeu */, _15G/* sbev */){
  var _15H/* sbew */ = B(A1(_15F/* sbeu */,_15G/* sbev */));
  return _15H/* sbew */*_15H/* sbew */*_15H/* sbew */;
},
_15I/* dur */ = 40,
_15J/* $we */ = function(_15K/* sT5M */, _15L/* sT5N */){
  if(_15L/* sT5N */>=0.5){
    var _15M/* sT5Q */ = 2-(_15L/* sT5N */+_15L/* sT5N */);
    return 1-B(A1(_15K/* sT5M */,_15M/* sT5Q */*_15M/* sT5Q */*(3-_15M/* sT5Q */)/2))/2;
  }else{
    var _15N/* sT60 */ = _15L/* sT5N */+_15L/* sT5N */;
    return B(A1(_15K/* sT5M */,_15N/* sT60 */*_15N/* sT60 */*(3-_15N/* sT60 */)/2))/2;
  }
},
_15O/* e */ = function(_15P/* sT68 */, _15Q/* sT69 */){
  return new F(function(){return _15J/* Motion.Trot.$we */(_15P/* sT68 */, E(_15Q/* sT69 */));});
},
_15R/* x */ = 0,
_15S/* lvl */ = new T1(0,_15R/* Motion.Trot.x */),
_15T/* lvl10 */ = -100,
_15U/* lvl11 */ = new T1(0,_15T/* Motion.Trot.lvl10 */),
_15V/* lvl12 */ = -200,
_15W/* lvl13 */ = new T1(0,_15V/* Motion.Trot.lvl12 */),
_15X/* lvl14 */ = new T2(0,_15U/* Motion.Trot.lvl11 */,_15W/* Motion.Trot.lvl13 */),
_15Y/* lvl15 */ = new T4(0,_15R/* Motion.Trot.x */,_15R/* Motion.Trot.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_15Z/* lvl16 */ = new T2(0,_15R/* Motion.Trot.x */,_15Y/* Motion.Trot.lvl15 */),
_160/* lvl17 */ = new T2(0,_15Z/* Motion.Trot.lvl16 */,_6/* GHC.Types.[] */),
_161/* a3 */ = 25,
_162/* lvl3 */ = new T1(0,_161/* Motion.Trot.a3 */),
_163/* a4 */ = 125,
_164/* lvl4 */ = new T1(0,_163/* Motion.Trot.a4 */),
_165/* a5 */ = 75,
_166/* lvl5 */ = new T1(0,_165/* Motion.Trot.a5 */),
_167/* lvl6 */ = new T(function(){
  var _168/* sT6d */ = B(_kB/* Core.Shape.Internal.$wrect */(_162/* Motion.Trot.lvl3 */, _164/* Motion.Trot.lvl4 */, _166/* Motion.Trot.lvl5 */, _166/* Motion.Trot.lvl5 */));
  return new T3(0,_168/* sT6d */.a,_168/* sT6d */.b,_168/* sT6d */.c);
}),
_169/* lvl7 */ = 1.5707963267948966,
_16a/* lvl8 */ = -75,
_16b/* a1 */ = 100,
_16c/* lvl1 */ = new T1(0,_16b/* Motion.Trot.a1 */),
_16d/* a2 */ = 200,
_16e/* lvl2 */ = new T1(0,_16d/* Motion.Trot.a2 */),
_16f/* lvl9 */ = new T2(0,_16c/* Motion.Trot.lvl1 */,_16e/* Motion.Trot.lvl2 */),
_16g/* trotMot */ = function(_16h/* sT6h */){
  var _16i/* sT6i */ = new T(function(){
    return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_15X/* Motion.Trot.lvl14 */,new T(function(){
      return B(_rB/* Core.Render.Internal.fill1 */(_16h/* sT6h */, _167/* Motion.Trot.lvl6 */));
    }),_7/* GHC.Tuple.() */)));
  }),
  _16j/* sT7r */ = function(_16k/* sT6l */, _16l/* sT6m */){
    var _16m/* sT7q */ = function(_/* EXTERNAL */){
      var _16n/* sT6o */ = nMV/* EXTERNAL */(_160/* Motion.Trot.lvl17 */),
      _16o/* sT6q */ = _16n/* sT6o */,
      _16p/* sT6s */ = new T(function(){
        return B(_jN/* Core.Ease.$wforceTo */(_16o/* sT6q */, _15R/* Motion.Trot.x */));
      }),
      _16q/* sT6t */ = function(_16r/* sT6u */){
        return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _15I/* Motion.Trot.dur */, _15E/* Core.Ease.cubic */, _16o/* sT6q */, _169/* Motion.Trot.lvl7 */, function(_16s/* sT6v */){
          return E(_16r/* sT6u */);
        });});
      },
      _16t/* sT7o */ = function(_/* EXTERNAL */){
        var _16u/* sT6y */ = nMV/* EXTERNAL */(_160/* Motion.Trot.lvl17 */),
        _16v/* sT6A */ = _16u/* sT6y */;
        return new T(function(){
          var _16w/* sT6C */ = new T(function(){
            return B(_jN/* Core.Ease.$wforceTo */(_16v/* sT6A */, _15R/* Motion.Trot.x */));
          }),
          _16x/* sT6D */ = function(_16y/* sT6E */){
            return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _15I/* Motion.Trot.dur */, _15O/* Motion.Trot.e */, _16v/* sT6A */, _16a/* Motion.Trot.lvl8 */, function(_16z/* sT6F */){
              return E(_16y/* sT6E */);
            });});
          },
          _16A/* sT6H */ = function(_16B/* sT6I */){
            var _16C/* sT6J */ = new T(function(){
              return B(A1(_16p/* sT6s */,_16B/* sT6I */));
            }),
            _16D/* sT79 */ = function(_16E/* sT6K */){
              var _16F/* sT6L */ = function(_16G/* sT6M */){
                return new F(function(){return A2(_16A/* sT6H */,E(_16G/* sT6M */).b, _16E/* sT6K */);});
              },
              _16H/* sT6Q */ = function(_16I/* sT6R */){
                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_16x/* sT6D */, E(_16I/* sT6R */).b, _16F/* sT6L */)));
              },
              _16J/* sT6X */ = function(_16K/* sT6Y */){
                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_16q/* sT6t */, E(_16K/* sT6Y */).b, _16H/* sT6Q */)));
              };
              return new F(function(){return A1(_16C/* sT6J */,function(_16L/* sT74 */){
                return new F(function(){return A2(_16w/* sT6C */,E(_16L/* sT74 */).b, _16J/* sT6X */);});
              });});
            };
            return E(_16D/* sT79 */);
          },
          _16M/* sT7k */ = new T(function(){
            var _16N/* sT7i */ = new T(function(){
              return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_16f/* Motion.Trot.lvl9 */,new T(function(){
                return B(_rx/* Control.Monad.Skeleton.bone */(new T3(6,new T2(2,new T3(0,_15I/* Motion.Trot.dur */,_15E/* Core.Ease.cubic */,_16o/* sT6q */),_2E/* GHC.Base.id */),_16i/* sT6i */,_7/* GHC.Tuple.() */)));
              }),_7/* GHC.Tuple.() */)));
            });
            return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,new T2(2,new T3(0,_15I/* Motion.Trot.dur */,_15O/* Motion.Trot.e */,_16v/* sT6A */),_2E/* GHC.Base.id */),_15S/* Motion.Trot.lvl */),_16N/* sT7i */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_16l/* sT6m */,new T2(0,new T2(0,_16M/* sT7k */,_16A/* sT6H */),_16k/* sT6l */)));
        });
      };
      return new T1(0,_16t/* sT7o */);
    };
    return new T1(0,_16m/* sT7q */);
  };
  return E(_16j/* sT7r */);
},
_16O/* lvl59 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_15B/* Motion.Main.lvl56 */, _16g/* Motion.Trot.trotMot */, _15C/* Motion.Main.lvl57 */, _15D/* Motion.Main.lvl58 */));
}),
_16P/* lvl60 */ = new T4(0,_Al/* Motion.Main.lvl11 */,_yT/* Motion.Main.lvl4 */,_Az/* Motion.Main.lvl21 */,_Al/* Motion.Main.lvl11 */),
_16Q/* lvl61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resist"));
}),
_16R/* lvl62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("easeOutExpo & Randomness & Vel/Acc model"));
}),
_16S/* . */ = function(_16T/* s3ay */, _16U/* s3az */, _16V/* s3aA */){
  return new F(function(){return A1(_16T/* s3ay */,new T(function(){
    return B(A1(_16U/* s3az */,_16V/* s3aA */));
  }));});
},
_16W/* $fFloatingValue_$cfmap */ = function(_16X/* sb0h */, _16Y/* sb0i */){
  var _16Z/* sb0j */ = E(_16Y/* sb0i */);
  switch(_16Z/* sb0j */._){
    case 0:
      return new T1(0,new T(function(){
        return B(A1(_16X/* sb0h */,_16Z/* sb0j */.a));
      }));
    case 1:
      return new T1(1,function(_/* EXTERNAL */){
        return new F(function(){return _x/* GHC.Base.$fFunctorIO2 */(_16X/* sb0h */, _16Z/* sb0j */.a, _/* EXTERNAL */);});
      });
    case 2:
      return new T2(2,_16Z/* sb0j */.a,function(_Af/* B1 */){
        return new F(function(){return _16S/* GHC.Base.. */(_16X/* sb0h */, _16Z/* sb0j */.b, _Af/* B1 */);});
      });
    default:
      var _170/* sb0z */ = function(_171/* sb0t */, _/* EXTERNAL */){
        var _172/* sb0v */ = B(A2(_16Z/* sb0j */.b,_171/* sb0t */, _/* EXTERNAL */));
        return new T(function(){
          return B(A1(_16X/* sb0h */,_172/* sb0v */));
        });
      };
      return new T2(3,_16Z/* sb0j */.a,_170/* sb0z */);
  }
},
_173/* a11 */ = 0,
_174/* a */ = new T1(0,_/* EXTERNAL */),
_175/* a1 */ = new T1(0,_7/* GHC.Tuple.() */),
_176/* a2 */ = new T2(0,E(_175/* Motion.Resist.a1 */),E(_174/* Motion.Resist.a */)),
_177/* a5 */ = 1,
_178/* lvl7 */ = -2.0e-2,
_179/* lvl8 */ = 2.0e-2,
_17a/* lvl9 */ = new T2(0,_178/* Motion.Resist.lvl7 */,_179/* Motion.Resist.lvl8 */),
_17b/* lvl10 */ = function(_/* EXTERNAL */){
  return new F(function(){return _Y8/* System.Random.$fRandomDouble8 */(_17a/* Motion.Resist.lvl9 */, _/* EXTERNAL */);});
},
_17c/* lvl11 */ = new T1(1,_17b/* Motion.Resist.lvl10 */),
_17d/* a9 */ = new T(function(){
  return B(_rx/* Control.Monad.Skeleton.bone */(_17c/* Motion.Resist.lvl11 */));
}),
_17e/* dur */ = 100,
_17f/* dur1 */ = 80,
_17g/* e */ = function(_17h/* s8wC */, _17i/* s8wD */){
  return 1-B(A1(_17h/* s8wC */,new T(function(){
    return Math.pow/* EXTERNAL */(2,  -((1-(1-E(_17i/* s8wD */)))*10));
  })));
},
_17j/* hPutStrLn2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_17k/* jshWrite1 */ = function(_17l/* s4GFX */, _17m/* s4GFY */, _/* EXTERNAL */){
  var _17n/* s4GG8 */ = jsWriteHandle/* EXTERNAL */(E(_17l/* s4GFX */), toJSStr/* EXTERNAL */(E(_17m/* s4GFY */)));
  return _7/* GHC.Tuple.() */;
},
_17o/* hPutStrLn1 */ = function(_17p/* s5hMY */, _17q/* s5hMZ */, _/* EXTERNAL */){
  var _17r/* s5hN1 */ = E(_17p/* s5hMY */),
  _17s/* s5hN9 */ = jsWriteHandle/* EXTERNAL */(_17r/* s5hN1 */, toJSStr/* EXTERNAL */(E(_17q/* s5hMZ */)));
  return new F(function(){return _17k/* Haste.Handle.jshWrite1 */(_17r/* s5hN1 */, _17j/* GHC.IO.Handle.Text.hPutStrLn2 */, _/* EXTERNAL */);});
},
_17t/* lvl */ = new T1(0,_177/* Motion.Resist.a5 */),
_17u/* a6 */ = 2,
_17v/* lvl1 */ = new T1(0,_17u/* Motion.Resist.a6 */),
_17w/* x */ = 0,
_17x/* lvl12 */ = new T1(0,_17w/* Motion.Resist.x */),
_17y/* a10 */ = -40,
_17z/* lvl13 */ = new T1(0,_17y/* Motion.Resist.a10 */),
_17A/* lvl14 */ = new T2(0,_17x/* Motion.Resist.lvl12 */,_17z/* Motion.Resist.lvl13 */),
_17B/* lvl15 */ = new T1(0,0),
_17C/* lvl16 */ = 0.3,
_17D/* lvl17 */ = 20,
_17E/* lvl18 */ = -5.0e-2,
_17F/* a7 */ = 40,
_17G/* lvl2 */ = new T1(0,_17F/* Motion.Resist.a7 */),
_17H/* lvl19 */ = new T1(0,100),
_17I/* lvl4 */ = new T1(0,1),
_17J/* lvl20 */ = new T(function(){
  return B(_Ve/* GHC.Enum.enumDeltaToInteger */(_17B/* Motion.Resist.lvl15 */, _17I/* Motion.Resist.lvl4 */, _17H/* Motion.Resist.lvl19 */));
}),
_17K/* lvl21 */ = function(_17L/* s8wP */){
  var _17M/* s8wQ */ = E(_17L/* s8wP */);
  return (_17M/* s8wQ */<=0) ? (_17M/* s8wQ */>=0) ? E(_17M/* s8wQ */) : E(_12I/* GHC.Float.$fNumDouble2 */) : E(_12H/* GHC.Float.$fNumDouble1 */);
},
_17N/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po8"));
}),
_17O/* shows5 */ = 34,
_17P/* lvl23 */ = new T2(1,_17O/* GHC.Show.shows5 */,_6/* GHC.Types.[] */),
_17Q/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: negative index"));
}),
_17R/* lvl2 */ = new T(function(){
  return B(_2/* GHC.Base.++ */(_No/* GHC.List.prel_list_str */, _17Q/* GHC.List.lvl1 */));
}),
_17S/* negIndex */ = new T(function(){
  return B(err/* EXTERNAL */(_17R/* GHC.List.lvl2 */));
}),
_17T/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: index too large"));
}),
_17U/* lvl4 */ = new T(function(){
  return B(_2/* GHC.Base.++ */(_No/* GHC.List.prel_list_str */, _17T/* GHC.List.lvl3 */));
}),
_17V/* !!1 */ = new T(function(){
  return B(err/* EXTERNAL */(_17U/* GHC.List.lvl4 */));
}),
_17W/* poly_$wgo2 */ = function(_17X/* s9uX */, _17Y/* s9uY */){
  while(1){
    var _17Z/* s9uZ */ = E(_17X/* s9uX */);
    if(!_17Z/* s9uZ */._){
      return E(_17V/* GHC.List.!!1 */);
    }else{
      var _180/* s9v2 */ = E(_17Y/* s9uY */);
      if(!_180/* s9v2 */){
        return E(_17Z/* s9uZ */.a);
      }else{
        _17X/* s9uX */ = _17Z/* s9uZ */.b;
        _17Y/* s9uY */ = _180/* s9v2 */-1|0;
        continue;
      }
    }
  }
},
_181/* $w!! */ = function(_182/* s9v4 */, _183/* s9v5 */){
  if(_183/* s9v5 */>=0){
    return new F(function(){return _17W/* GHC.List.poly_$wgo2 */(_182/* s9v4 */, _183/* s9v5 */);});
  }else{
    return E(_17S/* GHC.List.negIndex */);
  }
},
_184/* asciiTab59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_185/* asciiTab58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_186/* asciiTab57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_187/* asciiTab33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_188/* asciiTab32 */ = new T2(1,_187/* GHC.Show.asciiTab33 */,_6/* GHC.Types.[] */),
_189/* asciiTab34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_18a/* asciiTab31 */ = new T2(1,_189/* GHC.Show.asciiTab34 */,_188/* GHC.Show.asciiTab32 */),
_18b/* asciiTab35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_18c/* asciiTab30 */ = new T2(1,_18b/* GHC.Show.asciiTab35 */,_18a/* GHC.Show.asciiTab31 */),
_18d/* asciiTab36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_18e/* asciiTab29 */ = new T2(1,_18d/* GHC.Show.asciiTab36 */,_18c/* GHC.Show.asciiTab30 */),
_18f/* asciiTab37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_18g/* asciiTab28 */ = new T2(1,_18f/* GHC.Show.asciiTab37 */,_18e/* GHC.Show.asciiTab29 */),
_18h/* asciiTab38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_18i/* asciiTab27 */ = new T2(1,_18h/* GHC.Show.asciiTab38 */,_18g/* GHC.Show.asciiTab28 */),
_18j/* asciiTab39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_18k/* asciiTab26 */ = new T2(1,_18j/* GHC.Show.asciiTab39 */,_18i/* GHC.Show.asciiTab27 */),
_18l/* asciiTab40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_18m/* asciiTab25 */ = new T2(1,_18l/* GHC.Show.asciiTab40 */,_18k/* GHC.Show.asciiTab26 */),
_18n/* asciiTab41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_18o/* asciiTab24 */ = new T2(1,_18n/* GHC.Show.asciiTab41 */,_18m/* GHC.Show.asciiTab25 */),
_18p/* asciiTab42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_18q/* asciiTab23 */ = new T2(1,_18p/* GHC.Show.asciiTab42 */,_18o/* GHC.Show.asciiTab24 */),
_18r/* asciiTab43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_18s/* asciiTab22 */ = new T2(1,_18r/* GHC.Show.asciiTab43 */,_18q/* GHC.Show.asciiTab23 */),
_18t/* asciiTab44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_18u/* asciiTab21 */ = new T2(1,_18t/* GHC.Show.asciiTab44 */,_18s/* GHC.Show.asciiTab22 */),
_18v/* asciiTab45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_18w/* asciiTab20 */ = new T2(1,_18v/* GHC.Show.asciiTab45 */,_18u/* GHC.Show.asciiTab21 */),
_18x/* asciiTab46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_18y/* asciiTab19 */ = new T2(1,_18x/* GHC.Show.asciiTab46 */,_18w/* GHC.Show.asciiTab20 */),
_18z/* asciiTab47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_18A/* asciiTab18 */ = new T2(1,_18z/* GHC.Show.asciiTab47 */,_18y/* GHC.Show.asciiTab19 */),
_18B/* asciiTab48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_18C/* asciiTab17 */ = new T2(1,_18B/* GHC.Show.asciiTab48 */,_18A/* GHC.Show.asciiTab18 */),
_18D/* asciiTab49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_18E/* asciiTab16 */ = new T2(1,_18D/* GHC.Show.asciiTab49 */,_18C/* GHC.Show.asciiTab17 */),
_18F/* asciiTab50 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_18G/* asciiTab15 */ = new T2(1,_18F/* GHC.Show.asciiTab50 */,_18E/* GHC.Show.asciiTab16 */),
_18H/* asciiTab51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_18I/* asciiTab14 */ = new T2(1,_18H/* GHC.Show.asciiTab51 */,_18G/* GHC.Show.asciiTab15 */),
_18J/* asciiTab52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_18K/* asciiTab13 */ = new T2(1,_18J/* GHC.Show.asciiTab52 */,_18I/* GHC.Show.asciiTab14 */),
_18L/* asciiTab53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_18M/* asciiTab12 */ = new T2(1,_18L/* GHC.Show.asciiTab53 */,_18K/* GHC.Show.asciiTab13 */),
_18N/* asciiTab54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_18O/* asciiTab11 */ = new T2(1,_18N/* GHC.Show.asciiTab54 */,_18M/* GHC.Show.asciiTab12 */),
_18P/* asciiTab55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_18Q/* asciiTab10 */ = new T2(1,_18P/* GHC.Show.asciiTab55 */,_18O/* GHC.Show.asciiTab11 */),
_18R/* asciiTab56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_18S/* asciiTab9 */ = new T2(1,_18R/* GHC.Show.asciiTab56 */,_18Q/* GHC.Show.asciiTab10 */),
_18T/* asciiTab8 */ = new T2(1,_186/* GHC.Show.asciiTab57 */,_18S/* GHC.Show.asciiTab9 */),
_18U/* asciiTab7 */ = new T2(1,_185/* GHC.Show.asciiTab58 */,_18T/* GHC.Show.asciiTab8 */),
_18V/* asciiTab6 */ = new T2(1,_184/* GHC.Show.asciiTab59 */,_18U/* GHC.Show.asciiTab7 */),
_18W/* asciiTab60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_18X/* asciiTab5 */ = new T2(1,_18W/* GHC.Show.asciiTab60 */,_18V/* GHC.Show.asciiTab6 */),
_18Y/* asciiTab61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_18Z/* asciiTab4 */ = new T2(1,_18Y/* GHC.Show.asciiTab61 */,_18X/* GHC.Show.asciiTab5 */),
_190/* asciiTab62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_191/* asciiTab3 */ = new T2(1,_190/* GHC.Show.asciiTab62 */,_18Z/* GHC.Show.asciiTab4 */),
_192/* asciiTab63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_193/* asciiTab2 */ = new T2(1,_192/* GHC.Show.asciiTab63 */,_191/* GHC.Show.asciiTab3 */),
_194/* asciiTab64 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_195/* asciiTab1 */ = new T2(1,_194/* GHC.Show.asciiTab64 */,_193/* GHC.Show.asciiTab2 */),
_196/* asciiTab65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_197/* asciiTab */ = new T2(1,_196/* GHC.Show.asciiTab65 */,_195/* GHC.Show.asciiTab1 */),
_198/* lvl */ = 92,
_199/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\DEL"));
}),
_19a/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\a"));
}),
_19b/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\\"));
}),
_19c/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\SO"));
}),
_19d/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\r"));
}),
_19e/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\f"));
}),
_19f/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\v"));
}),
_19g/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\n"));
}),
_19h/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\t"));
}),
_19i/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\b"));
}),
_19j/* $wshowLitChar */ = function(_19k/* sfem */, _19l/* sfen */){
  if(_19k/* sfem */<=127){
    var _19m/* sfeq */ = E(_19k/* sfem */);
    switch(_19m/* sfeq */){
      case 92:
        return new F(function(){return _2/* GHC.Base.++ */(_19b/* GHC.Show.lvl2 */, _19l/* sfen */);});
        break;
      case 127:
        return new F(function(){return _2/* GHC.Base.++ */(_199/* GHC.Show.lvl1 */, _19l/* sfen */);});
        break;
      default:
        if(_19m/* sfeq */<32){
          var _19n/* sfet */ = E(_19m/* sfeq */);
          switch(_19n/* sfet */){
            case 7:
              return new F(function(){return _2/* GHC.Base.++ */(_19a/* GHC.Show.lvl10 */, _19l/* sfen */);});
              break;
            case 8:
              return new F(function(){return _2/* GHC.Base.++ */(_19i/* GHC.Show.lvl9 */, _19l/* sfen */);});
              break;
            case 9:
              return new F(function(){return _2/* GHC.Base.++ */(_19h/* GHC.Show.lvl8 */, _19l/* sfen */);});
              break;
            case 10:
              return new F(function(){return _2/* GHC.Base.++ */(_19g/* GHC.Show.lvl7 */, _19l/* sfen */);});
              break;
            case 11:
              return new F(function(){return _2/* GHC.Base.++ */(_19f/* GHC.Show.lvl6 */, _19l/* sfen */);});
              break;
            case 12:
              return new F(function(){return _2/* GHC.Base.++ */(_19e/* GHC.Show.lvl5 */, _19l/* sfen */);});
              break;
            case 13:
              return new F(function(){return _2/* GHC.Base.++ */(_19d/* GHC.Show.lvl4 */, _19l/* sfen */);});
              break;
            case 14:
              return new F(function(){return _2/* GHC.Base.++ */(_19c/* GHC.Show.lvl3 */, new T(function(){
                var _19o/* sfex */ = E(_19l/* sfen */);
                if(!_19o/* sfex */._){
                  return __Z/* EXTERNAL */;
                }else{
                  if(E(_19o/* sfex */.a)==72){
                    return B(unAppCStr/* EXTERNAL */("\\&", _19o/* sfex */));
                  }else{
                    return E(_19o/* sfex */);
                  }
                }
              },1));});
              break;
            default:
              return new F(function(){return _2/* GHC.Base.++ */(new T2(1,_198/* GHC.Show.lvl */,new T(function(){
                return B(_181/* GHC.List.$w!! */(_197/* GHC.Show.asciiTab */, _19n/* sfet */));
              })), _19l/* sfen */);});
          }
        }else{
          return new T2(1,_19m/* sfeq */,_19l/* sfen */);
        }
    }
  }else{
    var _19p/* sfeW */ = new T(function(){
      var _19q/* sfeH */ = jsShowI/* EXTERNAL */(_19k/* sfem */);
      return B(_2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_19q/* sfeH */), new T(function(){
        var _19r/* sfeM */ = E(_19l/* sfen */);
        if(!_19r/* sfeM */._){
          return __Z/* EXTERNAL */;
        }else{
          var _19s/* sfeP */ = E(_19r/* sfeM */.a);
          if(_19s/* sfeP */<48){
            return E(_19r/* sfeM */);
          }else{
            if(_19s/* sfeP */>57){
              return E(_19r/* sfeM */);
            }else{
              return B(unAppCStr/* EXTERNAL */("\\&", _19r/* sfeM */));
            }
          }
        }
      },1)));
    });
    return new T2(1,_198/* GHC.Show.lvl */,_19p/* sfeW */);
  }
},
_19t/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\""));
}),
_19u/* showLitString */ = function(_19v/* sff1 */, _19w/* sff2 */){
  var _19x/* sff3 */ = E(_19v/* sff1 */);
  if(!_19x/* sff3 */._){
    return E(_19w/* sff2 */);
  }else{
    var _19y/* sff5 */ = _19x/* sff3 */.b,
    _19z/* sff8 */ = E(_19x/* sff3 */.a);
    if(_19z/* sff8 */==34){
      return new F(function(){return _2/* GHC.Base.++ */(_19t/* GHC.Show.lvl11 */, new T(function(){
        return B(_19u/* GHC.Show.showLitString */(_19y/* sff5 */, _19w/* sff2 */));
      },1));});
    }else{
      return new F(function(){return _19j/* GHC.Show.$wshowLitChar */(_19z/* sff8 */, new T(function(){
        return B(_19u/* GHC.Show.showLitString */(_19y/* sff5 */, _19w/* sff2 */));
      }));});
    }
  }
},
_19A/* lvl24 */ = new T(function(){
  return B(_19u/* GHC.Show.showLitString */(_17N/* Motion.Resist.lvl22 */, _17P/* Motion.Resist.lvl23 */));
}),
_19B/* lvl25 */ = new T2(1,_17O/* GHC.Show.shows5 */,_19A/* Motion.Resist.lvl24 */),
_19C/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po7"));
}),
_19D/* lvl27 */ = new T(function(){
  return B(_19u/* GHC.Show.showLitString */(_19C/* Motion.Resist.lvl26 */, _17P/* Motion.Resist.lvl23 */));
}),
_19E/* lvl28 */ = new T2(1,_17O/* GHC.Show.shows5 */,_19D/* Motion.Resist.lvl27 */),
_19F/* a8 */ = 200,
_19G/* lvl3 */ = new T1(0,_19F/* Motion.Resist.a8 */),
_19H/* lvl29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po6"));
}),
_19I/* lvl30 */ = new T(function(){
  return B(_19u/* GHC.Show.showLitString */(_19H/* Motion.Resist.lvl29 */, _17P/* Motion.Resist.lvl23 */));
}),
_19J/* lvl31 */ = new T2(1,_17O/* GHC.Show.shows5 */,_19I/* Motion.Resist.lvl30 */),
_19K/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po9"));
}),
_19L/* lvl33 */ = new T(function(){
  return B(_19u/* GHC.Show.showLitString */(_19K/* Motion.Resist.lvl32 */, _17P/* Motion.Resist.lvl23 */));
}),
_19M/* lvl34 */ = new T2(1,_17O/* GHC.Show.shows5 */,_19L/* Motion.Resist.lvl33 */),
_19N/* lvl35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po5"));
}),
_19O/* lvl36 */ = new T(function(){
  return B(_19u/* GHC.Show.showLitString */(_19N/* Motion.Resist.lvl35 */, _17P/* Motion.Resist.lvl23 */));
}),
_19P/* lvl37 */ = new T2(1,_17O/* GHC.Show.shows5 */,_19O/* Motion.Resist.lvl36 */),
_19Q/* lvl38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po4"));
}),
_19R/* lvl39 */ = new T(function(){
  return B(_19u/* GHC.Show.showLitString */(_19Q/* Motion.Resist.lvl38 */, _17P/* Motion.Resist.lvl23 */));
}),
_19S/* lvl40 */ = new T2(1,_17O/* GHC.Show.shows5 */,_19R/* Motion.Resist.lvl39 */),
_19T/* lvl41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po3"));
}),
_19U/* lvl42 */ = new T(function(){
  return B(_19u/* GHC.Show.showLitString */(_19T/* Motion.Resist.lvl41 */, _17P/* Motion.Resist.lvl23 */));
}),
_19V/* lvl43 */ = new T2(1,_17O/* GHC.Show.shows5 */,_19U/* Motion.Resist.lvl42 */),
_19W/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po2"));
}),
_19X/* lvl45 */ = new T(function(){
  return B(_19u/* GHC.Show.showLitString */(_19W/* Motion.Resist.lvl44 */, _17P/* Motion.Resist.lvl23 */));
}),
_19Y/* lvl46 */ = new T2(1,_17O/* GHC.Show.shows5 */,_19X/* Motion.Resist.lvl45 */),
_19Z/* lvl47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po1"));
}),
_1a0/* lvl48 */ = new T(function(){
  return B(_19u/* GHC.Show.showLitString */(_19Z/* Motion.Resist.lvl47 */, _17P/* Motion.Resist.lvl23 */));
}),
_1a1/* lvl49 */ = new T2(1,_17O/* GHC.Show.shows5 */,_1a0/* Motion.Resist.lvl48 */),
_1a2/* lvl50 */ = new T4(0,_17w/* Motion.Resist.x */,_17w/* Motion.Resist.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_1a3/* lvl51 */ = new T2(0,_17w/* Motion.Resist.x */,_1a2/* Motion.Resist.lvl50 */),
_1a4/* lvl52 */ = new T2(0,_1a3/* Motion.Resist.lvl51 */,_6/* GHC.Types.[] */),
_1a5/* lvl5 */ = new T1(0,5),
_1a6/* lvl6 */ = new T(function(){
  return B(_Ve/* GHC.Enum.enumDeltaToInteger */(_17I/* Motion.Resist.lvl4 */, _17I/* Motion.Resist.lvl4 */, _1a5/* Motion.Resist.lvl5 */));
}),
_1a7/* lvl1 */ = function(_/* EXTERNAL */){
  return new F(function(){return jsMkStdout/* EXTERNAL */();});
},
_1a8/* stdout */ = new T(function(){
  return B(_44/* GHC.IO.unsafeDupablePerformIO */(_1a7/* Haste.Handle.lvl1 */));
}),
_1a9/* $wa */ = function(_1aa/* s8wW */, _1ab/* s8wX */, _1ac/* s8wY */){
  return function(_/* EXTERNAL */){
    var _1ad/* s8x0 */ = nMV/* EXTERNAL */(_1a4/* Motion.Resist.lvl52 */),
    _1ae/* s8x2 */ = _1ad/* s8x0 */,
    _1af/* s8x4 */ = new T3(0,_17e/* Motion.Resist.dur */,_17g/* Motion.Resist.e */,_1ae/* s8x2 */),
    _1ag/* s8x5 */ = new T2(2,_1af/* s8x4 */,_2E/* GHC.Base.id */),
    _1ah/* s8x6 */ = new T(function(){
      return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, B(_sg/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _17t/* Motion.Resist.lvl */, new T2(2,_1af/* s8x4 */,_17K/* Motion.Resist.lvl21 */))), _17v/* Motion.Resist.lvl1 */)), _17G/* Motion.Resist.lvl2 */));
    }),
    _1ai/* s8xa */ = new T(function(){
      var _1aj/* s8xg */ = new T(function(){
        var _1ak/* s8xc */ = B(_kB/* Core.Shape.Internal.$wrect */(new T(function(){
          return B(_16W/* Core.Ease.$fFloatingValue_$cfmap */(_G3/* GHC.Float.negateDouble */, _1ah/* s8x6 */));
        }), _17x/* Motion.Resist.lvl12 */, _17G/* Motion.Resist.lvl2 */, _17G/* Motion.Resist.lvl2 */));
        return new T3(0,_1ak/* s8xc */.a,_1ak/* s8xc */.b,_1ak/* s8xc */.c);
      });
      return B(_rB/* Core.Render.Internal.fill1 */(_1aa/* s8wW */, _1aj/* s8xg */));
    }),
    _1al/* s8xh */ = new T(function(){
      return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _17e/* Motion.Resist.dur */, _17g/* Motion.Resist.e */, _1ae/* s8x2 */, _17C/* Motion.Resist.lvl16 */, _Ac/* Core.Ease.easeTo1 */));
    }),
    _1am/* s8B3 */ = function(_/* EXTERNAL */){
      var _1an/* s8xj */ = nMV/* EXTERNAL */(_1a4/* Motion.Resist.lvl52 */),
      _1ao/* s8xl */ = _1an/* s8xj */,
      _1ap/* s8xn */ = new T(function(){
        return B(_jN/* Core.Ease.$wforceTo */(_1ao/* s8xl */, _17E/* Motion.Resist.lvl18 */));
      }),
      _1aq/* s8xo */ = function(_1ar/* s8xp */, _1as/* s8xq */, _1at/* s8xr */){
        var _1au/* s8xs */ = E(_1ar/* s8xp */);
        if(!_1au/* s8xs */._){
          return new F(function(){return A1(_1at/* s8xr */,new T2(0,_7/* GHC.Tuple.() */,_1as/* s8xq */));});
        }else{
          var _1av/* s8xw */ = function(_1aw/* s8xx */){
            var _1ax/* s8xG */ = function(_/* EXTERNAL */){
              var _1ay/* s8xC */ = B(_17o/* GHC.IO.Handle.Text.hPutStrLn1 */(_1a8/* Haste.Handle.stdout */, _19B/* Motion.Resist.lvl25 */, _/* EXTERNAL */));
              return new T(function(){
                return B(_1aq/* s8xo */(_1au/* s8xs */.b, E(_1aw/* s8xx */).b, _1at/* s8xr */));
              });
            };
            return new T1(0,_1ax/* s8xG */);
          },
          _1az/* s8xH */ = function(_1aA/* s8xI */){
            var _1aB/* s8xR */ = function(_/* EXTERNAL */){
              var _1aC/* s8xN */ = B(_17o/* GHC.IO.Handle.Text.hPutStrLn1 */(_1a8/* Haste.Handle.stdout */, _19E/* Motion.Resist.lvl28 */, _/* EXTERNAL */));
              return new T(function(){
                return B(_tv/* Core.World.Internal.sleep1 */(_173/* Motion.Resist.a11 */, E(_1aA/* s8xI */).b, _1av/* s8xw */));
              });
            };
            return new T1(0,_1aB/* s8xR */);
          },
          _1aD/* s8yD */ = function(_1aE/* s8xS */){
            var _1aF/* s8xT */ = new T(function(){
              var _1aG/* s8xU */ = new T(function(){
                return E(E(_1aE/* s8xS */).a);
              }),
              _1aH/* s8xY */ = new T(function(){
                return E(_1aG/* s8xU */)*0.3;
              }),
              _1aI/* s8yw */ = function(_1aJ/* s8y2 */){
                var _1aK/* s8y3 */ = new T(function(){
                  var _1aL/* s8y4 */ = new T(function(){
                    return E(E(_1aJ/* s8y2 */).a);
                  }),
                  _1aM/* s8y8 */ = new T(function(){
                    return B(_jN/* Core.Ease.$wforceTo */(_1ao/* s8xl */, new T(function(){
                      return E(_1aL/* s8y4 */)*0.6-E(_1aH/* s8xY */);
                    })));
                  }),
                  _1aN/* s8yr */ = function(_1aO/* s8yh */){
                    var _1aP/* s8yq */ = function(_/* EXTERNAL */){
                      var _1aQ/* s8ym */ = B(_17o/* GHC.IO.Handle.Text.hPutStrLn1 */(_1a8/* Haste.Handle.stdout */, _19J/* Motion.Resist.lvl31 */, _/* EXTERNAL */));
                      return new T(function(){
                        return B(A2(_1aM/* s8y8 */,E(_1aO/* s8yh */).b, _1az/* s8xH */));
                      });
                    };
                    return new T1(0,_1aP/* s8yq */);
                  };
                  return B(A(_jN/* Core.Ease.$wforceTo */,[_1ae/* s8x2 */, new T(function(){
                    return B(_tr/* GHC.Float.plusDouble */(_1aG/* s8xU */, _1aL/* s8y4 */));
                  }), _1as/* s8xq */, _1aN/* s8yr */]));
                });
                return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_1ao/* s8xl */, _1aJ/* s8y2 */, function(_1aR/* s8ys */){
                  return E(_1aK/* s8y3 */);
                })));
              };
              return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_1ao/* s8xl */, _1aI/* s8yw */)));
            });
            return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_1ae/* s8x2 */, _1aE/* s8xS */, function(_1aS/* s8yz */){
              return E(_1aF/* s8xT */);
            })));
          };
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_1ae/* s8x2 */, _1aD/* s8yD */)));
        }
      },
      _1aT/* s8B1 */ = function(_/* EXTERNAL */){
        var _1aU/* s8yH */ = nMV/* EXTERNAL */(_1a4/* Motion.Resist.lvl52 */),
        _1aV/* s8yJ */ = _1aU/* s8yH */;
        return new T(function(){
          var _1aW/* s8yL */ = new T(function(){
            return B(_jN/* Core.Ease.$wforceTo */(_1aV/* s8yJ */, _17w/* Motion.Resist.x */));
          }),
          _1aX/* s8yM */ = function(_1aY/* s8yN */){
            return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _17f/* Motion.Resist.dur1 */, _17g/* Motion.Resist.e */, _1aV/* s8yJ */, _177/* Motion.Resist.a5 */, function(_1aZ/* s8yO */){
              return E(_1aY/* s8yN */);
            });});
          },
          _1b0/* s8yQ */ = function(_1b1/* s8yR */){
            var _1b2/* s8yS */ = new T(function(){
              return B(A1(_1al/* s8xh */,_1b1/* s8yR */));
            }),
            _1b3/* s8A0 */ = function(_1b4/* s8yT */){
              var _1b5/* s8yU */ = function(_1b6/* s8yV */){
                var _1b7/* s8z4 */ = function(_/* EXTERNAL */){
                  var _1b8/* s8z0 */ = B(_17o/* GHC.IO.Handle.Text.hPutStrLn1 */(_1a8/* Haste.Handle.stdout */, _19M/* Motion.Resist.lvl34 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(A2(_1b0/* s8yQ */,E(_1b6/* s8yV */).b, _1b4/* s8yT */));
                  });
                };
                return new T1(0,_1b7/* s8z4 */);
              },
              _1b9/* s8z5 */ = function(_1ba/* s8z6 */){
                var _1bb/* s8zf */ = function(_/* EXTERNAL */){
                  var _1bc/* s8zb */ = B(_17o/* GHC.IO.Handle.Text.hPutStrLn1 */(_1a8/* Haste.Handle.stdout */, _19P/* Motion.Resist.lvl37 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(_1aq/* s8xo */(_17J/* Motion.Resist.lvl20 */, E(_1ba/* s8z6 */).b, _1b5/* s8yU */));
                  });
                };
                return new T1(0,_1bb/* s8zf */);
              },
              _1bd/* s8zg */ = function(_1be/* s8zh */){
                var _1bf/* s8zq */ = function(_/* EXTERNAL */){
                  var _1bg/* s8zm */ = B(_17o/* GHC.IO.Handle.Text.hPutStrLn1 */(_1a8/* Haste.Handle.stdout */, _19S/* Motion.Resist.lvl40 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(A2(_1ap/* s8xn */,E(_1be/* s8zh */).b, _1b9/* s8z5 */));
                  });
                };
                return new T1(0,_1bf/* s8zq */);
              },
              _1bh/* s8zr */ = function(_1bi/* s8zs */){
                var _1bj/* s8zB */ = function(_/* EXTERNAL */){
                  var _1bk/* s8zx */ = B(_17o/* GHC.IO.Handle.Text.hPutStrLn1 */(_1a8/* Haste.Handle.stdout */, _19V/* Motion.Resist.lvl43 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(A2(_1aW/* s8yL */,E(_1bi/* s8zs */).b, _1bd/* s8zg */));
                  });
                };
                return new T1(0,_1bj/* s8zB */);
              },
              _1bl/* s8zC */ = function(_1bm/* s8zD */){
                var _1bn/* s8zO */ = function(_/* EXTERNAL */){
                  var _1bo/* s8zI */ = B(_17o/* GHC.IO.Handle.Text.hPutStrLn1 */(_1a8/* Haste.Handle.stdout */, _19Y/* Motion.Resist.lvl46 */, _/* EXTERNAL */));
                  return new T(function(){
                    return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_1aX/* s8yM */, E(_1bm/* s8zD */).b, _1bh/* s8zr */)));
                  });
                };
                return new T1(0,_1bn/* s8zO */);
              },
              _1bp/* s8zZ */ = function(_1bq/* s8zP */){
                var _1br/* s8zY */ = function(_/* EXTERNAL */){
                  var _1bs/* s8zU */ = B(_17o/* GHC.IO.Handle.Text.hPutStrLn1 */(_1a8/* Haste.Handle.stdout */, _1a1/* Motion.Resist.lvl49 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(_tv/* Core.World.Internal.sleep1 */(_17D/* Motion.Resist.lvl17 */, E(_1bq/* s8zP */).b, _1bl/* s8zC */));
                  });
                };
                return new T1(0,_1br/* s8zY */);
              };
              return new F(function(){return A1(_1b2/* s8yS */,_1bp/* s8zZ */);});
            };
            return E(_1b3/* s8A0 */);
          },
          _1bt/* s8AX */ = new T(function(){
            var _1bu/* s8AV */ = new T(function(){
              var _1bv/* s8A4 */ = new T2(2,new T3(0,_17f/* Motion.Resist.dur1 */,_17g/* Motion.Resist.e */,_1aV/* s8yJ */),_2E/* GHC.Base.id */),
              _1bw/* s8A5 */ = function(_1bx/* s8A6 */){
                var _1by/* s8A7 */ = E(_1bx/* s8A6 */);
                if(!_1by/* s8A7 */._){
                  return E(_176/* Motion.Resist.a2 */);
                }else{
                  var _1bz/* s8A8 */ = _1by/* s8A7 */.a,
                  _1bA/* s8A9 */ = _1by/* s8A7 */.b;
                  if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_1bz/* s8A8 */, _17B/* Motion.Resist.lvl15 */))){
                    var _1bB/* s8Ab */ = E(_17d/* Motion.Resist.a9 */),
                    _1bC/* s8Ac */ = _1bB/* s8Ab */.a,
                    _1bD/* s8Ad */ = _1bB/* s8Ab */.b,
                    _1bE/* s8Ae */ = new T(function(){
                      var _1bF/* s8Az */ = new T(function(){
                        var _1bG/* s8Ax */ = new T(function(){
                          var _1bH/* s8Af */ = function(_1bI/* s8Ag */, _1bJ/* s8Ah */){
                            if(!B(_Ru/* GHC.Integer.Type.eqInteger */(_1bI/* s8Ag */, _17B/* Motion.Resist.lvl15 */))){
                              var _1bK/* s8Aj */ = new T(function(){
                                var _1bL/* s8An */ = new T(function(){
                                  return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_17A/* Motion.Resist.lvl14 */,new T(function(){
                                    return B(_1bH/* s8Af */(B(_LX/* GHC.Integer.Type.minusInteger */(_1bI/* s8Ag */, _17I/* Motion.Resist.lvl4 */)), _1bJ/* s8Ah */));
                                  }),_7/* GHC.Tuple.() */)));
                                });
                                return B(_rx/* Control.Monad.Skeleton.bone */(new T3(6,_1ag/* s8x5 */,_1bL/* s8An */,_7/* GHC.Tuple.() */)));
                              }),
                              _1bM/* s8At */ = function(_1bN/* s8Ap */){
                                return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T3(6,new T(function(){
                                  return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_1bN/* s8Ap */), _1bv/* s8A4 */));
                                }),_1bK/* s8Aj */,_7/* GHC.Tuple.() */));});
                              };
                              return new T2(0,E(_1bC/* s8Ac */),E(new T2(2,_1bD/* s8Ad */,new T1(1,_1bM/* s8At */))));
                            }else{
                              return E(_1bJ/* s8Ah */);
                            }
                          };
                          return B(_1bH/* s8Af */(B(_LX/* GHC.Integer.Type.minusInteger */(_1bz/* s8A8 */, _17I/* Motion.Resist.lvl4 */)), _1ai/* s8xa */));
                        });
                        return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_17A/* Motion.Resist.lvl14 */,_1bG/* s8Ax */,_7/* GHC.Tuple.() */)));
                      });
                      return B(_rx/* Control.Monad.Skeleton.bone */(new T3(6,_1ag/* s8x5 */,_1bF/* s8Az */,_7/* GHC.Tuple.() */)));
                    }),
                    _1bO/* s8AB */ = new T(function(){
                      return B(_1bw/* s8A5 */(_1bA/* s8A9 */));
                    }),
                    _1bP/* s8AG */ = function(_1bQ/* s8AC */){
                      return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T3(6,new T(function(){
                        return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_1bQ/* s8AC */), _1bv/* s8A4 */));
                      }),_1bE/* s8Ae */,_7/* GHC.Tuple.() */));});
                    };
                    return new T2(0,E(_1bC/* s8Ac */),E(new T2(2,new T2(2,_1bD/* s8Ad */,new T1(1,_1bP/* s8AG */)),new T1(1,function(_1bR/* s8AJ */){
                      return E(_1bO/* s8AB */);
                    }))));
                  }else{
                    var _1bS/* s8AN */ = E(_1ai/* s8xa */),
                    _1bT/* s8AQ */ = new T(function(){
                      return B(_1bw/* s8A5 */(_1bA/* s8A9 */));
                    });
                    return new T2(0,E(_1bS/* s8AN */.a),E(new T2(2,_1bS/* s8AN */.b,new T1(1,function(_1bU/* s8AR */){
                      return E(_1bT/* s8AQ */);
                    }))));
                  }
                }
              };
              return B(_1bw/* s8A5 */(_1a6/* Motion.Resist.lvl6 */));
            });
            return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,new T(function(){
              return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _17G/* Motion.Resist.lvl2 */, _1ah/* s8x6 */));
            }),_19G/* Motion.Resist.lvl3 */),_1bu/* s8AV */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_1ac/* s8wY */,new T2(0,new T2(0,_1bt/* s8AX */,_1b0/* s8yQ */),_1ab/* s8wX */)));
        });
      };
      return new T1(0,_1aT/* s8B1 */);
    };
    return new T1(0,_1am/* s8B3 */);
  };
},
_1bV/* resistMot1 */ = function(_1bW/* s8B6 */, _1bX/* s8B7 */, _1bY/* s8B8 */){
  return new T1(0,B(_1a9/* Motion.Resist.$wa */(_1bW/* s8B6 */, _1bX/* s8B7 */, _1bY/* s8B8 */)));
},
_1bZ/* lvl63 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_16P/* Motion.Main.lvl60 */, _1bV/* Motion.Resist.resistMot1 */, _16Q/* Motion.Main.lvl61 */, _16R/* Motion.Main.lvl62 */));
}),
_1c0/* dur */ = 20,
_1c1/* lvl */ = 0,
_1c2/* x */ = 1,
_1c3/* lvl1 */ = new T4(0,_1c2/* Motion.Info.x */,_1c2/* Motion.Info.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_1c4/* lvl2 */ = new T2(0,_1c2/* Motion.Info.x */,_1c3/* Motion.Info.lvl1 */),
_1c5/* lvl3 */ = new T2(0,_1c4/* Motion.Info.lvl2 */,_6/* GHC.Types.[] */),
_1c6/* $wa */ = function(_1c7/* s6l3 */, _1c8/* s6l4 */, _1c9/* s6l5 */){
  return function(_/* EXTERNAL */){
    var _1ca/* s6l7 */ = nMV/* EXTERNAL */(_1c5/* Motion.Info.lvl3 */);
    return new T(function(){
      var _1cb/* s6la */ = function(_1cc/* s6lb */, _1cd/* s6lc */){
        var _1ce/* s6lq */ = B(A1(_1cc/* s6lb */,new T(function(){
          var _1cf/* s6lf */ = E(_1cd/* s6lc */)/0.6-_1c7/* s6l3 *//2*0.6666666666666667;
          if(1>_1cf/* s6lf */){
            if(0>_1cf/* s6lf */){
              return E(_1c2/* Motion.Info.x */);
            }else{
              return 1-_1cf/* s6lf */;
            }
          }else{
            return E(_1c1/* Motion.Info.lvl */);
          }
        })));
        return 1-_1ce/* s6lq */*_1ce/* s6lq */;
      },
      _1cg/* s6ly */ = new T3(0,_1c0/* Motion.Info.dur */,function(_1ch/* s6lu */, _1ci/* s6lv */){
        return new F(function(){return _1cb/* s6la */(_1ch/* s6lu */, _1ci/* s6lv */);});
      },_1ca/* s6l7 */),
      _1cj/* s6lz */ = E(_1c7/* s6l3 */);
      if(_1cj/* s6lz */==2){
        return B(A1(_1c9/* s6l5 */,new T2(0,new T2(1,_1cg/* s6ly */,_6/* GHC.Types.[] */),_1c8/* s6l4 */)));
      }else{
        return new T1(0,B(_1c6/* Motion.Info.$wa */(_1cj/* s6lz */+1|0, _1c8/* s6l4 */, function(_1ck/* s6lB */){
          var _1cl/* s6lC */ = E(_1ck/* s6lB */);
          return new F(function(){return A1(_1c9/* s6l5 */,new T2(0,new T2(1,_1cg/* s6ly */,_1cl/* s6lC */.a),_1cl/* s6lC */.b));});
        })));
      }
    });
  };
},
_1cm/* $wa1 */ = function(_1cn/* s6lO */, _1co/* s6lP */, _1cp/* s6lQ */){
  return function(_/* EXTERNAL */){
    var _1cq/* s6lS */ = nMV/* EXTERNAL */(_1c5/* Motion.Info.lvl3 */);
    return new T(function(){
      var _1cr/* s6lV */ = function(_1cs/* s6lW */, _1ct/* s6lX */){
        var _1cu/* s6mb */ = B(A1(_1cs/* s6lW */,new T(function(){
          var _1cv/* s6m0 */ = E(_1ct/* s6lX */)/0.6-_1cn/* s6lO *//2*0.6666666666666667;
          if(1>_1cv/* s6m0 */){
            if(0>_1cv/* s6m0 */){
              return E(_1c2/* Motion.Info.x */);
            }else{
              return 1-_1cv/* s6m0 */;
            }
          }else{
            return E(_1c1/* Motion.Info.lvl */);
          }
        })));
        return 1-_1cu/* s6mb */*_1cu/* s6mb */*_1cu/* s6mb */;
      },
      _1cw/* s6mk */ = new T3(0,_1c0/* Motion.Info.dur */,function(_1cx/* s6mg */, _1cy/* s6mh */){
        return new F(function(){return _1cr/* s6lV */(_1cx/* s6mg */, _1cy/* s6mh */);});
      },_1cq/* s6lS */),
      _1cz/* s6ml */ = E(_1cn/* s6lO */);
      if(_1cz/* s6ml */==2){
        return B(A1(_1cp/* s6lQ */,new T2(0,new T2(1,_1cw/* s6mk */,_6/* GHC.Types.[] */),_1co/* s6lP */)));
      }else{
        return new T1(0,B(_1cm/* Motion.Info.$wa1 */(_1cz/* s6ml */+1|0, _1co/* s6lP */, function(_1cA/* s6mn */){
          var _1cB/* s6mo */ = E(_1cA/* s6mn */);
          return new F(function(){return A1(_1cp/* s6lQ */,new T2(0,new T2(1,_1cw/* s6mk */,_1cB/* s6mo */.a),_1cB/* s6mo */.b));});
        })));
      }
    });
  };
},
_1cC/* a */ = new T1(0,_/* EXTERNAL */),
_1cD/* a1 */ = new T1(0,_7/* GHC.Tuple.() */),
_1cE/* a2 */ = new T2(0,E(_1cD/* Motion.Info.a1 */),E(_1cC/* Motion.Info.a */)),
_1cF/* e */ = function(_1cG/* s6kQ */, _1cH/* s6kR */){
  return 1-B(A1(_1cG/* s6kQ */,new T(function(){
    var _1cI/* s6kU */ = 1-E(_1cH/* s6kR */);
    return _1cI/* s6kU */*_1cI/* s6kU */*(2.70158*_1cI/* s6kU */-1.70158);
  })));
},
_1cJ/* a6 */ = function(_1cK/* s6mE */, _1cL/* s6mF */){
  return new F(function(){return A1(_1cL/* s6mF */,new T2(0,_6/* GHC.Types.[] */,_1cK/* s6mE */));});
},
_1cM/* go */ = function(_1cN/* s6mH */, _1cO/* s6mI */){
  var _1cP/* s6mJ */ = E(_1cN/* s6mH */);
  if(!_1cP/* s6mJ */._){
    return E(_1cJ/* Motion.Info.a6 */);
  }else{
    var _1cQ/* s6mM */ = E(_1cO/* s6mI */);
    if(!_1cQ/* s6mM */._){
      return E(_1cJ/* Motion.Info.a6 */);
    }else{
      var _1cR/* s6mP */ = new T(function(){
        return B(_1cM/* Motion.Info.go */(_1cP/* s6mJ */.b, _1cQ/* s6mM */.b));
      }),
      _1cS/* s6mQ */ = new T(function(){
        var _1cT/* s6mR */ = E(_1cQ/* s6mM */.a),
        _1cU/* s6mS */ = _1cT/* s6mR */.a,
        _1cV/* s6mT */ = _1cT/* s6mR */.b,
        _1cW/* s6mU */ = new T(function(){
          return B(_jN/* Core.Ease.$wforceTo */(E(_1cU/* s6mS */).c, _1c2/* Motion.Info.x */));
        }),
        _1cX/* s6mZ */ = new T(function(){
          return B(_jN/* Core.Ease.$wforceTo */(E(_1cV/* s6mT */).c, _1c2/* Motion.Info.x */));
        }),
        _1cY/* s6n4 */ = new T(function(){
          return 1.8-E(_1cP/* s6mJ */.a)/2*0.4;
        }),
        _1cZ/* s6nb */ = new T(function(){
          var _1d0/* s6nc */ = E(_1cU/* s6mS */);
          return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1d0/* s6nc */.a, _1d0/* s6nc */.b, _1d0/* s6nc */.c, _1cY/* s6n4 */, _Ac/* Core.Ease.easeTo1 */));
        }),
        _1d1/* s6ng */ = new T(function(){
          var _1d2/* s6nh */ = E(_1cV/* s6mT */);
          return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1d2/* s6nh */.a, _1d2/* s6nh */.b, _1d2/* s6nh */.c, _1cY/* s6n4 */, _Ac/* Core.Ease.easeTo1 */));
        }),
        _1d3/* s6nE */ = function(_1d4/* s6nl */){
          var _1d5/* s6nm */ = new T(function(){
            return B(A1(_1cW/* s6mU */,_1d4/* s6nl */));
          }),
          _1d6/* s6nD */ = function(_1d7/* s6nn */){
            var _1d8/* s6no */ = function(_1d9/* s6np */){
              return new F(function(){return A2(_1d1/* s6ng */,E(_1d9/* s6np */).b, _1d7/* s6nn */);});
            },
            _1da/* s6nt */ = function(_1db/* s6nu */){
              return new F(function(){return A2(_1cZ/* s6nb */,E(_1db/* s6nu */).b, _1d8/* s6no */);});
            };
            return new F(function(){return A1(_1d5/* s6nm */,function(_1dc/* s6ny */){
              return new F(function(){return A2(_1cX/* s6mZ */,E(_1dc/* s6ny */).b, _1da/* s6nt */);});
            });});
          };
          return E(_1d6/* s6nD */);
        };
        return E(_1d3/* s6nE */);
      }),
      _1dd/* s6nV */ = function(_1de/* s6nF */){
        var _1df/* s6nG */ = new T(function(){
          return B(A1(_1cS/* s6mQ */,_1de/* s6nF */));
        }),
        _1dg/* s6nU */ = function(_1dh/* s6nH */){
          var _1di/* s6nT */ = function(_1dj/* s6nI */){
            var _1dk/* s6nJ */ = E(_1dj/* s6nI */);
            return new F(function(){return A2(_1cR/* s6mP */,_1dk/* s6nJ */.b, function(_1dl/* s6nM */){
              var _1dm/* s6nN */ = E(_1dl/* s6nM */);
              return new F(function(){return A1(_1dh/* s6nH */,new T2(0,new T2(1,_1dk/* s6nJ */.a,_1dm/* s6nN */.a),_1dm/* s6nN */.b));});
            });});
          };
          return new F(function(){return A1(_1df/* s6nG */,_1di/* s6nT */);});
        };
        return E(_1dg/* s6nU */);
      };
      return E(_1dd/* s6nV */);
    }
  }
},
_1dn/* lvl10 */ = 1.2,
_1do/* a4 */ = 100,
_1dp/* lvl4 */ = new T1(0,_1do/* Motion.Info.a4 */),
_1dq/* lvl5 */ = new T2(0,_1dp/* Motion.Info.lvl4 */,_1dp/* Motion.Info.lvl4 */),
_1dr/* lvl6 */ = new T1(0,_1c1/* Motion.Info.lvl */),
_1ds/* a5 */ = 80,
_1dt/* lvl7 */ = new T1(0,_1ds/* Motion.Info.a5 */),
_1du/* lvl8 */ = new T(function(){
  var _1dv/* s6mA */ = B(_GO/* Core.Shape.Internal.$wcenterRect */(_1dr/* Motion.Info.lvl6 */, _1dr/* Motion.Info.lvl6 */, _1dt/* Motion.Info.lvl7 */, _1dt/* Motion.Info.lvl7 */));
  return new T3(0,_1dv/* s6mA */.a,_1dv/* s6mA */.b,_1dv/* s6mA */.c);
}),
_1dw/* lvl9 */ = 40,
_1dx/* zip */ = function(_1dy/* s9E4 */, _1dz/* s9E5 */){
  var _1dA/* s9E6 */ = E(_1dy/* s9E4 */);
  if(!_1dA/* s9E6 */._){
    return __Z/* EXTERNAL */;
  }else{
    var _1dB/* s9E9 */ = E(_1dz/* s9E5 */);
    return (_1dB/* s9E9 */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T2(0,_1dA/* s9E6 */.a,_1dB/* s9E9 */.a),new T(function(){
      return B(_1dx/* GHC.List.zip */(_1dA/* s9E6 */.b, _1dB/* s9E9 */.b));
    }));
  }
},
_1dC/* infoMot */ = function(_1dD/* s6nW */){
  var _1dE/* s6nX */ = new T(function(){
    return B(_rB/* Core.Render.Internal.fill1 */(_1dD/* s6nW */, _1du/* Motion.Info.lvl8 */));
  }),
  _1dF/* s6nY */ = function(_1dG/* s6nZ */){
    var _1dH/* s6o0 */ = E(_1dG/* s6nZ */);
    if(!_1dH/* s6o0 */._){
      return E(_1cE/* Motion.Info.a2 */);
    }else{
      var _1dI/* s6o3 */ = E(_1dH/* s6o0 */.a),
      _1dJ/* s6o6 */ = new T(function(){
        return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, _1dp/* Motion.Info.lvl4 */, B(_Iq/* Core.Ease.morph */(_1dI/* s6o3 */.a))));
      }),
      _1dK/* s6oa */ = B(_rx/* Control.Monad.Skeleton.bone */(new T1(1,function(_/* EXTERNAL */){
        return new F(function(){return _14i/* Core.Ease.valueIO1 */(_1dJ/* s6o6 */, _/* EXTERNAL */);});
      }))),
      _1dL/* s6od */ = new T(function(){
        return B(_1dF/* s6nY */(_1dH/* s6o0 */.b));
      }),
      _1dM/* s6oe */ = new T(function(){
        return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, _1dp/* Motion.Info.lvl4 */, B(_Iq/* Core.Ease.morph */(_1dI/* s6o3 */.b))));
      }),
      _1dN/* s6og */ = new T(function(){
        return B(_rx/* Control.Monad.Skeleton.bone */(new T1(1,function(_/* EXTERNAL */){
          return new F(function(){return _14i/* Core.Ease.valueIO1 */(_1dM/* s6oe */, _/* EXTERNAL */);});
        })));
      }),
      _1dO/* s6oj */ = new T(function(){
        var _1dP/* s6op */ = B(_rB/* Core.Render.Internal.fill1 */(_1dD/* s6nW */, new T(function(){
          var _1dQ/* s6ok */ = B(_GO/* Core.Shape.Internal.$wcenterRect */(_1dr/* Motion.Info.lvl6 */, _1dr/* Motion.Info.lvl6 */, _1dM/* s6oe */, _1dM/* s6oe */));
          return new T3(0,_1dQ/* s6ok */.a,_1dQ/* s6ok */.b,_1dQ/* s6ok */.c);
        }))),
        _1dR/* s6os */ = new T(function(){
          return B(_rB/* Core.Render.Internal.fill1 */(_yZ/* Core.Render.Internal.white */, new T(function(){
            var _1dS/* s6ot */ = B(_GO/* Core.Shape.Internal.$wcenterRect */(_1dr/* Motion.Info.lvl6 */, _1dr/* Motion.Info.lvl6 */, _1dJ/* s6o6 */, _1dJ/* s6o6 */));
            return new T3(0,_1dS/* s6ot */.a,_1dS/* s6ot */.b,_1dS/* s6ot */.c);
          })));
        });
        return new T2(0,E(_1dP/* s6op */.a),E(new T2(2,_1dP/* s6op */.b,new T1(1,function(_1dT/* s6oy */){
          return E(_1dR/* s6os */);
        }))));
      }),
      _1dU/* s6p0 */ = function(_1dV/* s6oC */){
        var _1dW/* s6oD */ = E(_1dN/* s6og */);
        return new T2(0,E(_1dW/* s6oD */.a),E(new T2(2,_1dW/* s6oD */.b,new T1(1,function(_1dX/* s6oG */){
          var _1dY/* s6oH */ = E(_1dV/* s6oC */);
          if(!_1dY/* s6oH */._){
            return E(_1cE/* Motion.Info.a2 */);
          }else{
            var _1dZ/* s6oJ */ = E(_1dX/* s6oG */);
            if(!_1dZ/* s6oJ */._){
              return E(_1cE/* Motion.Info.a2 */);
            }else{
              var _1e0/* s6oP */ = E(_1dY/* s6oH */.a)-E(_1dZ/* s6oJ */.a);
              return (_1e0/* s6oP */==0) ? E(_1cE/* Motion.Info.a2 */) : (_1e0/* s6oP */<=0) ? ( -_1e0/* s6oP */<=1) ? E(_1cE/* Motion.Info.a2 */) : E(_1dO/* s6oj */) : (_1e0/* s6oP */<=1) ? E(_1cE/* Motion.Info.a2 */) : E(_1dO/* s6oj */);
            }
          }
        }))));
      };
      return new T2(0,E(_1dK/* s6oa */.a),E(new T2(2,new T2(2,_1dK/* s6oa */.b,new T1(1,_1dU/* s6p0 */)),new T1(1,function(_1e1/* s6p3 */){
        return E(_1dL/* s6od */);
      }))));
    }
  },
  _1e2/* s6qk */ = function(_1e3/* s6p7 */, _1e4/* s6p8 */){
    var _1e5/* s6qj */ = function(_/* EXTERNAL */){
      var _1e6/* s6pa */ = nMV/* EXTERNAL */(_1c5/* Motion.Info.lvl3 */),
      _1e7/* s6pc */ = _1e6/* s6pa */;
      return new T(function(){
        var _1e8/* s6pe */ = new T(function(){
          var _1e9/* s6pf */ = new T3(0,_1c0/* Motion.Info.dur */,_1cF/* Motion.Info.e */,_1e7/* s6pc */);
          return B(_rx/* Control.Monad.Skeleton.bone */(new T3(7,new T2(0,new T2(2,_1e9/* s6pf */,_2E/* GHC.Base.id */),new T2(2,_1e9/* s6pf */,_2E/* GHC.Base.id */)),_1dE/* s6nX */,_7/* GHC.Tuple.() */)));
        }),
        _1ea/* s6pk */ = function(_1eb/* s6pl */){
          return E(_1e8/* s6pe */);
        },
        _1ec/* s6pn */ = new T(function(){
          return B(_jN/* Core.Ease.$wforceTo */(_1e7/* s6pc */, _1dn/* Motion.Info.lvl10 */));
        }),
        _1ed/* s6po */ = function(_1ee/* s6pp */){
          return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1c0/* Motion.Info.dur */, _1cF/* Motion.Info.e */, _1e7/* s6pc */, _1c2/* Motion.Info.x */, function(_1ef/* s6pq */){
            return E(_1ee/* s6pp */);
          });});
        },
        _1eg/* s6qf */ = function(_1eh/* s6ps */){
          var _1ei/* s6pt */ = E(_1eh/* s6ps */),
          _1ej/* s6qc */ = function(_1ek/* s6pw */){
            var _1el/* s6px */ = E(_1ek/* s6pw */),
            _1em/* s6pA */ = new T(function(){
              return B(_1dx/* GHC.List.zip */(_1ei/* s6pt */.a, _1el/* s6px */.a));
            }),
            _1en/* s6pB */ = new T(function(){
              return B(_1cM/* Motion.Info.go */(_Ik/* Core.Util.iforM1 */, _1em/* s6pA */));
            }),
            _1eo/* s6pD */ = function(_1ep/* s6pK */){
              return new F(function(){return _1eq/* s6pH */(E(_1ep/* s6pK */).b);});
            },
            _1er/* s6pE */ = function(_1es/* s6pO */){
              return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_1ed/* s6po */, E(_1es/* s6pO */).b, _1eo/* s6pD */)));
            },
            _1et/* s6pF */ = function(_1eu/* s6pU */){
              return new F(function(){return A2(_1en/* s6pB */,E(_1eu/* s6pU */).b, _1er/* s6pE */);});
            },
            _1ev/* s6pG */ = function(_1ew/* s6pY */){
              return new F(function(){return A2(_1ec/* s6pn */,E(_1ew/* s6pY */).b, _1et/* s6pF */);});
            },
            _1eq/* s6pH */ = function(_1ex/* s6q2 */){
              return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_1dw/* Motion.Info.lvl9 */, _1ex/* s6q2 */, _1ev/* s6pG */);});
            },
            _1ey/* s6q9 */ = new T(function(){
              return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_1dq/* Motion.Info.lvl5 */,new T(function(){
                var _1ez/* s6q3 */ = B(_1dF/* s6nY */(_1em/* s6pA */));
                return new T2(0,E(_1ez/* s6q3 */.a),E(new T2(2,_1ez/* s6q3 */.b,new T1(1,_1ea/* s6pk */))));
              }),_7/* GHC.Tuple.() */)));
            });
            return new F(function(){return A1(_1e4/* s6p8 */,new T2(0,new T2(0,_1ey/* s6q9 */,function(_1eA/* s6pI */, _1eB/* s6pJ */){
              return new F(function(){return _1eq/* s6pH */(_1eA/* s6pI */);});
            }),_1el/* s6px */.b));});
          };
          return new T1(0,B(_1cm/* Motion.Info.$wa1 */(0, _1ei/* s6pt */.b, _1ej/* s6qc */)));
        };
        return new T1(0,B(_1c6/* Motion.Info.$wa */(0, _1e3/* s6p7 */, _1eg/* s6qf */)));
      });
    };
    return new T1(0,_1e5/* s6qj */);
  };
  return E(_1e2/* s6qk */);
},
_1eC/* lvl64 */ = 0.9,
_1eD/* lvl65 */ = new T1(0,_1eC/* Motion.Main.lvl64 */),
_1eE/* lvl66 */ = new T4(0,_AC/* Motion.Main.lvl23 */,_Jh/* Motion.Main.lvl41 */,_1eD/* Motion.Main.lvl65 */,_Al/* Motion.Main.lvl11 */),
_1eF/* lvl67 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Info"));
}),
_1eG/* lvl68 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("easeOutBack & Cubic-Quad difference"));
}),
_1eH/* lvl69 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_1eE/* Motion.Main.lvl66 */, _1dC/* Motion.Info.infoMot */, _1eF/* Motion.Main.lvl67 */, _1eG/* Motion.Main.lvl68 */));
}),
_1eI/* lvl70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("height"));
}),
_1eJ/* lvl71 */ = 1,
_1eK/* lvl72 */ = new T1(1,_6/* GHC.Types.[] */),
_1eL/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.scale(x,y);})");
}),
_1eM/* f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,rad){ctx.rotate(rad);})");
}),
_1eN/* f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.translate(x,y);})");
}),
_1eO/* f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})");
}),
_1eP/* render2 */ = function(_1eQ/*  sFRL */, _1eR/*  sFRM */, _/* EXTERNAL */){
  while(1){
    var _1eS/*  render2 */ = B((function(_1eT/* sFRL */, _1eU/* sFRM */, _/* EXTERNAL */){
      var _1eV/* sFRO */ = B(_fo/* Control.Monad.Skeleton.debone */(_1eT/* sFRL */));
      if(!_1eV/* sFRO */._){
        return _1eV/* sFRO */.a;
      }else{
        var _1eW/* sFRR */ = _1eV/* sFRO */.b,
        _1eX/* sFRS */ = E(_1eV/* sFRO */.a);
        switch(_1eX/* sFRS */._){
          case 0:
            var _1eY/* sFRV */ = B(A2(_1eX/* sFRS */.a,_1eU/* sFRM */, _/* EXTERNAL */)),
            _1eZ/*   sFRM */ = _1eU/* sFRM */;
            _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1eX/* sFRS */.b));
            _1eR/*  sFRM */ = _1eZ/*   sFRM */;
            return __continue/* EXTERNAL */;
          case 1:
            var _1f0/* sFS0 */ = B(A1(_1eX/* sFRS */.a,_/* EXTERNAL */)),
            _1eZ/*   sFRM */ = _1eU/* sFRM */;
            _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1f0/* sFS0 */));
            _1eR/*  sFRM */ = _1eZ/*   sFRM */;
            return __continue/* EXTERNAL */;
          case 2:
            var _1eZ/*   sFRM */ = _1eU/* sFRM */;
            _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1eX/* sFRS */.b));
            _1eR/*  sFRM */ = _1eZ/*   sFRM */;
            return __continue/* EXTERNAL */;
          case 3:
            var _1f1/* sFSa */ = B(_1eP/* Core.Render.Internal.render2 */(_1eX/* sFRS */.b, _1eX/* sFRS */.a, _/* EXTERNAL */)),
            _1eZ/*   sFRM */ = _1eU/* sFRM */;
            _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1eX/* sFRS */.c));
            _1eR/*  sFRM */ = _1eZ/*   sFRM */;
            return __continue/* EXTERNAL */;
          case 4:
            var _1f2/* sFSl */ = _1eX/* sFRS */.h,
            _1f3/* sFSm */ = function(_1f4/* sFSn */, _/* EXTERNAL */){
              var _1f5/* sFTr */ = function(_1f6/* sFSp */, _/* EXTERNAL */){
                var _1f7/* sFTq */ = function(_1f8/* sFSr */, _/* EXTERNAL */){
                  var _1f9/* sFTp */ = function(_1fa/* sFSt */, _/* EXTERNAL */){
                    var _1fb/* sFTo */ = function(_1fc/* sFSv */, _/* EXTERNAL */){
                      return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1eX/* sFRS */.f, function(_1fd/* sFSx */, _/* EXTERNAL */){
                        var _1fe/* sFSz */ = E(_1eU/* sFRM */),
                        _1ff/* sFSE */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _1fe/* sFSz */),
                        _1fg/* sFTb */ = __apply/* EXTERNAL */(E(_1eO/* Core.Render.Internal.f4 */), new T2(1,E(_1fd/* sFSx */),new T2(1,E(_1fc/* sFSv */),new T2(1,E(_1fa/* sFSt */),new T2(1,E(_1f8/* sFSr */),new T2(1,E(_1f6/* sFSp */),new T2(1,E(_1f4/* sFSn */),new T2(1,_1fe/* sFSz */,_6/* GHC.Types.[] */)))))))),
                        _1fh/* sFTe */ = B(_1eP/* Core.Render.Internal.render2 */(_1eX/* sFRS */.g, _1fe/* sFSz */, _/* EXTERNAL */)),
                        _1fi/* sFTk */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), _1fe/* sFSz */);
                        return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
                      }, _/* EXTERNAL */);});
                    };
                    return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1eX/* sFRS */.e, _1fb/* sFTo */, _/* EXTERNAL */);});
                  };
                  return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1eX/* sFRS */.d, _1f9/* sFTp */, _/* EXTERNAL */);});
                };
                return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1eX/* sFRS */.c, _1f7/* sFTq */, _/* EXTERNAL */);});
              };
              return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1eX/* sFRS */.b, _1f5/* sFTr */, _/* EXTERNAL */);});
            },
            _1fj/* sFTs */ = E(_1eX/* sFRS */.a);
            switch(_1fj/* sFTs */._){
              case 0:
                var _1fk/* sFTu */ = B(_1f3/* sFSm */(_1fj/* sFTs */.a, _/* EXTERNAL */)),
                _1eZ/*   sFRM */ = _1eU/* sFRM */;
                _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1f2/* sFSl */));
                _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                return __continue/* EXTERNAL */;
              case 1:
                var _1fl/* sFTz */ = B(A1(_1fj/* sFTs */.a,_/* EXTERNAL */)),
                _1fm/* sFTC */ = B(_1f3/* sFSm */(_1fl/* sFTz */, _/* EXTERNAL */)),
                _1eZ/*   sFRM */ = _1eU/* sFRM */;
                _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1f2/* sFSl */));
                _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                return __continue/* EXTERNAL */;
              case 2:
                var _1fn/* sFTO */ = rMV/* EXTERNAL */(E(E(_1fj/* sFTs */.a).c)),
                _1fo/* sFTR */ = E(_1fn/* sFTO */);
                if(!_1fo/* sFTR */._){
                  var _1fp/* sFTV */ = new T(function(){
                    return B(A1(_1fj/* sFTs */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_1fo/* sFTR */.a));
                    })));
                  },1),
                  _1fq/* sFTW */ = B(_1f3/* sFSm */(_1fp/* sFTV */, _/* EXTERNAL */)),
                  _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1f2/* sFSl */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1f2/* sFSl */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _1fr/* sFUa */ = rMV/* EXTERNAL */(E(E(_1fj/* sFTs */.a).c)),
                _1fs/* sFUd */ = E(_1fr/* sFUa */);
                if(!_1fs/* sFUd */._){
                  var _1ft/* sFUj */ = B(A2(_1fj/* sFTs */.b,E(_1fs/* sFUd */.a).a, _/* EXTERNAL */)),
                  _1fu/* sFUm */ = B(_1f3/* sFSm */(_1ft/* sFUj */, _/* EXTERNAL */)),
                  _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1f2/* sFSl */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1f2/* sFSl */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 5:
            var _1fv/* sFUu */ = _1eX/* sFRS */.c,
            _1fw/* sFUv */ = E(_1eX/* sFRS */.a),
            _1fx/* sFUy */ = function(_1fy/* sFUz */, _/* EXTERNAL */){
              return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1fw/* sFUv */.b, function(_1fz/* sFUB */, _/* EXTERNAL */){
                var _1fA/* sFUD */ = E(_1eU/* sFRM */),
                _1fB/* sFUI */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _1fA/* sFUD */),
                _1fC/* sFUW */ = __app3/* EXTERNAL */(E(_1eN/* Core.Render.Internal.f3 */), _1fA/* sFUD */, E(_1fy/* sFUz */), E(_1fz/* sFUB */)),
                _1fD/* sFUZ */ = B(_1eP/* Core.Render.Internal.render2 */(_1eX/* sFRS */.b, _1fA/* sFUD */, _/* EXTERNAL */)),
                _1fE/* sFV5 */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), _1fA/* sFUD */);
                return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _1fF/* sFV9 */ = E(_1fw/* sFUv */.a);
            switch(_1fF/* sFV9 */._){
              case 0:
                var _1fG/* sFVb */ = B(_1fx/* sFUy */(_1fF/* sFV9 */.a, _/* EXTERNAL */)),
                _1eZ/*   sFRM */ = _1eU/* sFRM */;
                _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fv/* sFUu */));
                _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                return __continue/* EXTERNAL */;
              case 1:
                var _1fH/* sFVg */ = B(A1(_1fF/* sFV9 */.a,_/* EXTERNAL */)),
                _1fI/* sFVj */ = B(_1fx/* sFUy */(_1fH/* sFVg */, _/* EXTERNAL */)),
                _1eZ/*   sFRM */ = _1eU/* sFRM */;
                _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fv/* sFUu */));
                _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                return __continue/* EXTERNAL */;
              case 2:
                var _1fJ/* sFVv */ = rMV/* EXTERNAL */(E(E(_1fF/* sFV9 */.a).c)),
                _1fK/* sFVy */ = E(_1fJ/* sFVv */);
                if(!_1fK/* sFVy */._){
                  var _1fL/* sFVC */ = new T(function(){
                    return B(A1(_1fF/* sFV9 */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_1fK/* sFVy */.a));
                    })));
                  },1),
                  _1fM/* sFVD */ = B(_1fx/* sFUy */(_1fL/* sFVC */, _/* EXTERNAL */)),
                  _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fv/* sFUu */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fv/* sFUu */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _1fN/* sFVR */ = rMV/* EXTERNAL */(E(E(_1fF/* sFV9 */.a).c)),
                _1fO/* sFVU */ = E(_1fN/* sFVR */);
                if(!_1fO/* sFVU */._){
                  var _1fP/* sFW0 */ = B(A2(_1fF/* sFV9 */.b,E(_1fO/* sFVU */.a).a, _/* EXTERNAL */)),
                  _1fQ/* sFW3 */ = B(_1fx/* sFUy */(_1fP/* sFW0 */, _/* EXTERNAL */)),
                  _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fv/* sFUu */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fv/* sFUu */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 6:
            var _1fR/* sFWb */ = _1eX/* sFRS */.c,
            _1fS/* sFWc */ = function(_1fT/* sFWd */, _/* EXTERNAL */){
              var _1fU/* sFWf */ = E(_1eU/* sFRM */),
              _1fV/* sFWk */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _1fU/* sFWf */),
              _1fW/* sFWu */ = __app2/* EXTERNAL */(E(_1eM/* Core.Render.Internal.f2 */), _1fU/* sFWf */, E(_1fT/* sFWd */)),
              _1fX/* sFWx */ = B(_1eP/* Core.Render.Internal.render2 */(_1eX/* sFRS */.b, _1fU/* sFWf */, _/* EXTERNAL */)),
              _1fY/* sFWD */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), _1fU/* sFWf */);
              return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
            },
            _1fZ/* sFWG */ = E(_1eX/* sFRS */.a);
            switch(_1fZ/* sFWG */._){
              case 0:
                var _1g0/* sFWI */ = B(_1fS/* sFWc */(_1fZ/* sFWG */.a, _/* EXTERNAL */)),
                _1eZ/*   sFRM */ = _1eU/* sFRM */;
                _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fR/* sFWb */));
                _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                return __continue/* EXTERNAL */;
              case 1:
                var _1g1/* sFWN */ = B(A1(_1fZ/* sFWG */.a,_/* EXTERNAL */)),
                _1g2/* sFWQ */ = B(_1fS/* sFWc */(_1g1/* sFWN */, _/* EXTERNAL */)),
                _1eZ/*   sFRM */ = _1eU/* sFRM */;
                _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fR/* sFWb */));
                _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                return __continue/* EXTERNAL */;
              case 2:
                var _1g3/* sFX2 */ = rMV/* EXTERNAL */(E(E(_1fZ/* sFWG */.a).c)),
                _1g4/* sFX5 */ = E(_1g3/* sFX2 */);
                if(!_1g4/* sFX5 */._){
                  var _1g5/* sFX9 */ = new T(function(){
                    return B(A1(_1fZ/* sFWG */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_1g4/* sFX5 */.a));
                    })));
                  },1),
                  _1g6/* sFXa */ = B(_1fS/* sFWc */(_1g5/* sFX9 */, _/* EXTERNAL */)),
                  _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fR/* sFWb */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fR/* sFWb */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _1g7/* sFXo */ = rMV/* EXTERNAL */(E(E(_1fZ/* sFWG */.a).c)),
                _1g8/* sFXr */ = E(_1g7/* sFXo */);
                if(!_1g8/* sFXr */._){
                  var _1g9/* sFXx */ = B(A2(_1fZ/* sFWG */.b,E(_1g8/* sFXr */.a).a, _/* EXTERNAL */)),
                  _1ga/* sFXA */ = B(_1fS/* sFWc */(_1g9/* sFXx */, _/* EXTERNAL */)),
                  _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fR/* sFWb */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1fR/* sFWb */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 7:
            var _1gb/* sFXI */ = _1eX/* sFRS */.c,
            _1gc/* sFXJ */ = E(_1eX/* sFRS */.a),
            _1gd/* sFXM */ = function(_1ge/* sFXN */, _/* EXTERNAL */){
              return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1gc/* sFXJ */.b, function(_1gf/* sFXP */, _/* EXTERNAL */){
                var _1gg/* sFXR */ = E(_1eU/* sFRM */),
                _1gh/* sFXW */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _1gg/* sFXR */),
                _1gi/* sFYa */ = __app3/* EXTERNAL */(E(_1eL/* Core.Render.Internal.f1 */), _1gg/* sFXR */, E(_1ge/* sFXN */), E(_1gf/* sFXP */)),
                _1gj/* sFYd */ = B(_1eP/* Core.Render.Internal.render2 */(_1eX/* sFRS */.b, _1gg/* sFXR */, _/* EXTERNAL */)),
                _1gk/* sFYj */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), _1gg/* sFXR */);
                return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _1gl/* sFYn */ = E(_1gc/* sFXJ */.a);
            switch(_1gl/* sFYn */._){
              case 0:
                var _1gm/* sFYp */ = B(_1gd/* sFXM */(_1gl/* sFYn */.a, _/* EXTERNAL */)),
                _1eZ/*   sFRM */ = _1eU/* sFRM */;
                _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1gb/* sFXI */));
                _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                return __continue/* EXTERNAL */;
              case 1:
                var _1gn/* sFYu */ = B(A1(_1gl/* sFYn */.a,_/* EXTERNAL */)),
                _1go/* sFYx */ = B(_1gd/* sFXM */(_1gn/* sFYu */, _/* EXTERNAL */)),
                _1eZ/*   sFRM */ = _1eU/* sFRM */;
                _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1gb/* sFXI */));
                _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                return __continue/* EXTERNAL */;
              case 2:
                var _1gp/* sFYJ */ = rMV/* EXTERNAL */(E(E(_1gl/* sFYn */.a).c)),
                _1gq/* sFYM */ = E(_1gp/* sFYJ */);
                if(!_1gq/* sFYM */._){
                  var _1gr/* sFYQ */ = new T(function(){
                    return B(A1(_1gl/* sFYn */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_1gq/* sFYM */.a));
                    })));
                  },1),
                  _1gs/* sFYR */ = B(_1gd/* sFXM */(_1gr/* sFYQ */, _/* EXTERNAL */)),
                  _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1gb/* sFXI */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1gb/* sFXI */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _1gt/* sFZ5 */ = rMV/* EXTERNAL */(E(E(_1gl/* sFYn */.a).c)),
                _1gu/* sFZ8 */ = E(_1gt/* sFZ5 */);
                if(!_1gu/* sFZ8 */._){
                  var _1gv/* sFZe */ = B(A2(_1gl/* sFYn */.b,E(_1gu/* sFZ8 */.a).a, _/* EXTERNAL */)),
                  _1gw/* sFZh */ = B(_1gd/* sFXM */(_1gv/* sFZe */, _/* EXTERNAL */)),
                  _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1gb/* sFXI */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1eZ/*   sFRM */ = _1eU/* sFRM */;
                  _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1gb/* sFXI */));
                  _1eR/*  sFRM */ = _1eZ/*   sFRM */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          default:
            var _1gx/* sFZq */ = B(_1eP/* Core.Render.Internal.render2 */(_1eX/* sFRS */.a, _1eU/* sFRM */, _/* EXTERNAL */)),
            _1eZ/*   sFRM */ = _1eU/* sFRM */;
            _1eQ/*  sFRL */ = B(A1(_1eW/* sFRR */,_1eX/* sFRS */.c));
            _1eR/*  sFRM */ = _1eZ/*   sFRM */;
            return __continue/* EXTERNAL */;
        }
      }
    })(_1eQ/*  sFRL */, _1eR/*  sFRM */, _/* EXTERNAL */));
    if(_1eS/*  render2 */!=__continue/* EXTERNAL */){
      return _1eS/*  render2 */;
    }
  }
},
_1gy/* a12 */ = new T1(0,_/* EXTERNAL */),
_1gz/* a13 */ = new T1(0,_6/* GHC.Types.[] */),
_1gA/* a14 */ = new T2(0,E(_1gz/* Motion.Main.a13 */),E(_1gy/* Motion.Main.a12 */)),
_1gB/* pad */ = 40,
_1gC/* lvl1 */ = new T1(0,_1gB/* Motion.Main.pad */),
_1gD/* rendering1 */ = function(_1gE/* sXQu */){
  return E(E(_1gE/* sXQu */).b);
},
_1gF/* renderContents_go */ = function(_1gG/* s7J5 */, _1gH/* s7J6 */){
  var _1gI/* s7J7 */ = E(_1gG/* s7J5 */);
  if(!_1gI/* s7J7 */._){
    return E(_1gA/* Motion.Main.a14 */);
  }else{
    var _1gJ/* s7Ja */ = E(_1gH/* s7J6 */);
    if(!_1gJ/* s7Ja */._){
      return E(_1gA/* Motion.Main.a14 */);
    }else{
      var _1gK/* s7Jn */ = B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_1gC/* Motion.Main.lvl1 */,new T1(0,new T(function(){
        return 40+190*E(_1gI/* s7J7 */.a);
      }))),new T(function(){
        return B(_1gD/* Core.View.rendering1 */(_1gJ/* s7Ja */.a));
      }),_7/* GHC.Tuple.() */))),
      _1gL/* s7Jq */ = new T(function(){
        return B(_1gF/* Motion.Main.renderContents_go */(_1gI/* s7J7 */.b, _1gJ/* s7Ja */.b));
      }),
      _1gM/* s7JB */ = function(_1gN/* s7Jr */){
        var _1gO/* s7Js */ = E(_1gL/* s7Jq */);
        return new T2(0,E(_1gO/* s7Js */.a),E(new T2(2,_1gO/* s7Js */.b,new T1(1,function(_1gP/* s7Jv */){
          return new T2(0,E(new T1(0,new T2(1,_1gN/* s7Jr */,_1gP/* s7Jv */))),E(_1gy/* Motion.Main.a12 */));
        }))));
      };
      return new T2(0,E(_1gK/* s7Jn */.a),E(new T2(2,_1gK/* s7Jn */.b,new T1(1,_1gM/* s7JB */))));
    }
  }
},
_1gQ/* renderContents1 */ = function(_1gR/* s7JE */){
  return new F(function(){return _rp/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
    return B(_1gF/* Motion.Main.renderContents_go */(_Ik/* Core.Util.iforM1 */, _1gR/* s7JE */));
  }));});
},
_1gS/* launch1 */ = function(_1gT/* s7Ld */, _1gU/* s7Le */){
  var _1gV/* s7Lf */ = function(_1gW/* s7Lg */, _/* EXTERNAL */){
    var _1gX/* s7Li */ = E(_1gT/* s7Ld */),
    _1gY/* s7Lo */ = __app1/* EXTERNAL */(E(_ib/* Haste.Graphics.Canvas.buffer_f1 */), _1gX/* s7Li */.b);
    return new F(function(){return _1eP/* Core.Render.Internal.render2 */(B(_1gQ/* Motion.Main.renderContents1 */(_1gW/* s7Lg */)), _1gX/* s7Li */.a, _/* EXTERNAL */);});
  },
  _1gZ/* s7Lt */ = new T(function(){
    return B(A1(_G2/* Motion.Main.lvl39 */,_1gU/* s7Le */));
  }),
  _1h0/* s7Ns */ = function(_1h1/* s7Lu */){
    var _1h2/* s7Nr */ = function(_1h3/* s7Lv */){
      var _1h4/* s7Lw */ = E(_1h3/* s7Lv */),
      _1h5/* s7Nq */ = function(_1h6/* s7Lz */){
        var _1h7/* s7LA */ = E(_1h6/* s7Lz */),
        _1h8/* s7Np */ = function(_1h9/* s7LD */){
          var _1ha/* s7LE */ = E(_1h9/* s7LD */),
          _1hb/* s7No */ = function(_1hc/* s7LH */){
            var _1hd/* s7LI */ = E(_1hc/* s7LH */),
            _1he/* s7Nn */ = function(_1hf/* s7LL */){
              var _1hg/* s7LM */ = E(_1hf/* s7LL */),
              _1hh/* s7Nm */ = function(_1hi/* s7LP */){
                var _1hj/* s7LQ */ = E(_1hi/* s7LP */),
                _1hk/* s7Nl */ = function(_1hl/* s7LT */){
                  var _1hm/* s7LU */ = E(_1hl/* s7LT */),
                  _1hn/* s7M3 */ = new T2(1,_1h4/* s7Lw */.a,new T2(1,_1h7/* s7LA */.a,new T2(1,_1ha/* s7LE */.a,new T2(1,_1hd/* s7LI */.a,new T2(1,_1hg/* s7LM */.a,new T2(1,_1hj/* s7LQ */.a,new T2(1,_1hm/* s7LU */.a,_6/* GHC.Types.[] */))))))),
                  _1ho/* s7Nk */ = function(_/* EXTERNAL */){
                    var _1hp/* s7Mi */ = jsShow/* EXTERNAL */(40+B(_eT/* GHC.List.$wlenAcc */(_1hn/* s7M3 */, 0))*190),
                    _1hq/* s7Mu */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), E(_1gT/* s7Ld */).b, toJSStr/* EXTERNAL */(E(_1eI/* Motion.Main.lvl70 */)), toJSStr/* EXTERNAL */(fromJSStr/* EXTERNAL */(_1hp/* s7Mi */))),
                    _1hr/* s7Ni */ = function(_/* EXTERNAL */){
                      var _1hs/* s7Mz */ = nMV/* EXTERNAL */(new T2(0,_1hn/* s7M3 */,_6/* GHC.Types.[] */));
                      return new T(function(){
                        var _1ht/* s7MD */ = new T(function(){
                          return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _1hs/* s7Mz */, _eY/* Motion.Main.a24 */));
                        }),
                        _1hu/* s7MF */ = function(_1hv/* s7ML */){
                          return new F(function(){return _1hw/* s7MI */(E(_1hv/* s7ML */).b);});
                        },
                        _1hx/* s7MG */ = function(_1hy/* s7MP */){
                          return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_1eJ/* Motion.Main.lvl71 */, E(_1hy/* s7MP */).b, _1hu/* s7MF */);});
                        },
                        _1hz/* s7MH */ = function(_1hA/* s7MT */){
                          var _1hB/* s7MU */ = E(_1hA/* s7MT */);
                          return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[B(_1gQ/* Motion.Main.renderContents1 */(_1hB/* s7MU */.a)), _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _1hB/* s7MU */.b, _1hx/* s7MG */]);});
                        },
                        _1hw/* s7MI */ = function(_1hC/* s7MY */){
                          return new F(function(){return A2(_1ht/* s7MD */,_1hC/* s7MY */, _1hz/* s7MH */);});
                        },
                        _1hD/* s7Ne */ = function(_1hE/* s7MZ */){
                          var _1hF/* s7N2 */ = E(_1hE/* s7MZ */).b,
                          _1hG/* s7Nd */ = function(_/* EXTERNAL */){
                            var _1hH/* s7N4 */ = nMV/* EXTERNAL */(_1eK/* Motion.Main.lvl72 */);
                            return new T1(1,new T2(1,new T(function(){
                              return B(A1(_1h1/* s7Lu */,new T2(0,_7/* GHC.Tuple.() */,_1hF/* s7N2 */)));
                            }),new T2(1,new T(function(){
                              return B(_1hw/* s7MI */(_1hF/* s7N2 */));
                            }),_6/* GHC.Types.[] */)));
                          };
                          return new T1(0,_1hG/* s7Nd */);
                        };
                        return new T1(0,B(_e8/* Core.Front.Internal.$wa */(_1hs/* s7Mz */, _1gV/* s7Lf */, _1hm/* s7LU */.b, _1hD/* s7Ne */)));
                      });
                    };
                    return new T1(0,_1hr/* s7Ni */);
                  };
                  return new T1(0,_1ho/* s7Nk */);
                };
                return new F(function(){return A2(_1eH/* Motion.Main.lvl69 */,_1hj/* s7LQ */.b, _1hk/* s7Nl */);});
              };
              return new F(function(){return A2(_1bZ/* Motion.Main.lvl63 */,_1hg/* s7LM */.b, _1hh/* s7Nm */);});
            };
            return new F(function(){return A2(_16O/* Motion.Main.lvl59 */,_1hd/* s7LI */.b, _1he/* s7Nn */);});
          };
          return new F(function(){return A2(_15A/* Motion.Main.lvl55 */,_1ha/* s7LE */.b, _1hb/* s7No */);});
        };
        return new F(function(){return A2(_YZ/* Motion.Main.lvl49 */,_1h7/* s7LA */.b, _1h8/* s7Np */);});
      };
      return new F(function(){return A2(_Jl/* Motion.Main.lvl45 */,_1h4/* s7Lw */.b, _1h5/* s7Nq */);});
    };
    return new F(function(){return A1(_1gZ/* s7Lt */,_1h2/* s7Nr */);});
  };
  return E(_1h0/* s7Ns */);
},
_1hI/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Canvas not found!"));
}),
_1hJ/* main2 */ = new T(function(){
  return B(err/* EXTERNAL */(_1hI/* Main.lvl */));
}),
_1hK/* main3 */ = "canvas",
_1hL/* start_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(Util.onload)");
}),
_1hM/* main1 */ = function(_/* EXTERNAL */){
  var _1hN/* s1353 */ = __app1/* EXTERNAL */(E(_1hL/* Core.Front.Internal.start_f1 */), E(_48/* Haste.Prim.Any.jsNull */)),
  _1hO/* s1356 */ = B(A3(_e1/* Haste.DOM.JSString.elemById */,_2G/* Control.Monad.IO.Class.$fMonadIOIO */, _1hK/* Main.main3 */, _/* EXTERNAL */)),
  _1hP/* s1359 */ = E(_1hO/* s1356 */);
  if(!_1hP/* s1359 */._){
    return E(_1hJ/* Main.main2 */);
  }else{
    var _1hQ/* s135c */ = E(_1hP/* s1359 */.a),
    _1hR/* s135h */ = __app1/* EXTERNAL */(E(_1/* Haste.Graphics.Canvas.$fFromAnyCanvas_f2 */), _1hQ/* s135c */);
    if(!_1hR/* s135h */){
      return E(_1hJ/* Main.main2 */);
    }else{
      var _1hS/* s135p */ = __app1/* EXTERNAL */(E(_0/* Haste.Graphics.Canvas.$fFromAnyCanvas_f1 */), _1hQ/* s135c */),
      _1hT/* s135r */ = _1hS/* s135p */,
      _1hU/* s135w */ = new T(function(){
        return new T1(0,B(_d7/* Core.World.Internal.$wa5 */(function(_1hV/* B1 */){
          return new F(function(){return _1gS/* Motion.Main.launch1 */(new T2(0,_1hT/* s135r */,_1hQ/* s135c */), _1hV/* B1 */);});
        }, _2I/* Haste.Concurrent.Monad.forkIO1 */)));
      });
      return new F(function(){return _e/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(_1hU/* s135w */, _6/* GHC.Types.[] */, _/* EXTERNAL */);});
    }
  }
},
_1hW/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _1hM/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_1hW, [0]));};window.onload = hasteMain;