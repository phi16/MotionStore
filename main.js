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
_4D/* $fMonadEventWorld2 */ = function(_4E/* sbZ1 */){
  var _4F/* sbZ2 */ = E(_4E/* sbZ1 */);
  return new T0(2);
},
_4G/* $fMonadConcWorld1 */ = function(_4H/* sbZ5 */, _4I/* sbZ6 */, _4J/* sbZ7 */){
  return new T1(1,new T2(1,new T(function(){
    return B(A1(_4J/* sbZ7 */,new T2(0,_7/* GHC.Tuple.() */,_4I/* sbZ6 */)));
  }),new T2(1,new T(function(){
    return B(A2(_4H/* sbZ5 */,_4I/* sbZ6 */, _4D/* Core.World.Internal.$fMonadEventWorld2 */));
  }),_6/* GHC.Types.[] */)));
},
_4K/* $fApplicativeWorld1 */ = function(_4L/* sbSA */, _4M/* sbSB */, _4N/* sbSC */){
  var _4O/* sbSD */ = new T(function(){
    return B(A1(_4L/* sbSA */,_4N/* sbSC */));
  }),
  _4P/* sbSQ */ = function(_4Q/* sbSE */){
    var _4R/* sbSP */ = function(_4S/* sbSF */){
      var _4T/* sbSG */ = E(_4S/* sbSF */);
      return new F(function(){return A2(_4M/* sbSB */,_4T/* sbSG */.b, function(_4U/* sbSJ */){
        return new F(function(){return A1(_4Q/* sbSE */,new T2(0,_4T/* sbSG */.a,E(_4U/* sbSJ */).b));});
      });});
    };
    return new F(function(){return A1(_4O/* sbSD */,_4R/* sbSP */);});
  };
  return E(_4P/* sbSQ */);
},
_4V/* $fApplicativeWorld2 */ = function(_4W/* sbSR */, _4X/* sbSS */, _4Y/* sbST */){
  var _4Z/* sbSU */ = new T(function(){
    return B(A1(_4W/* sbSR */,_4Y/* sbST */));
  }),
  _50/* sbT6 */ = function(_51/* sbSV */){
    var _52/* sbSW */ = function(_53/* sbSX */){
      return new F(function(){return A1(_51/* sbSV */,E(_53/* sbSX */));});
    };
    return new F(function(){return A1(_4Z/* sbSU */,function(_54/* sbT1 */){
      return new F(function(){return A2(_4X/* sbSS */,E(_54/* sbT1 */).b, _52/* sbSW */);});
    });});
  };
  return E(_50/* sbT6 */);
},
_55/* $fApplicativeWorld3 */ = function(_56/* sbT7 */, _57/* sbT8 */, _58/* sbT9 */){
  var _59/* sbTa */ = new T(function(){
    return B(A1(_56/* sbT7 */,_58/* sbT9 */));
  }),
  _5a/* sbTo */ = function(_5b/* sbTb */){
    var _5c/* sbTn */ = function(_5d/* sbTc */){
      var _5e/* sbTd */ = E(_5d/* sbTc */),
      _5f/* sbTm */ = function(_5g/* sbTg */){
        var _5h/* sbTh */ = E(_5g/* sbTg */);
        return new F(function(){return A1(_5b/* sbTb */,new T2(0,new T(function(){
          return B(A1(_5e/* sbTd */.a,_5h/* sbTh */.a));
        }),_5h/* sbTh */.b));});
      };
      return new F(function(){return A2(_57/* sbT8 */,_5e/* sbTd */.b, _5f/* sbTm */);});
    };
    return new F(function(){return A1(_59/* sbTa */,_5c/* sbTn */);});
  };
  return E(_5a/* sbTo */);
},
_5i/* $fFunctorWorld1 */ = function(_5j/* sbVe */, _5k/* sbVf */, _5l/* sbVg */){
  var _5m/* sbVh */ = new T(function(){
    return B(A1(_5k/* sbVf */,_5l/* sbVg */));
  }),
  _5n/* sbVp */ = function(_5o/* sbVi */){
    var _5p/* sbVo */ = function(_5q/* sbVj */){
      return new F(function(){return A1(_5o/* sbVi */,new T(function(){
        return new T2(0,_5j/* sbVe */,E(_5q/* sbVj */).b);
      }));});
    };
    return new F(function(){return A1(_5m/* sbVh */,_5p/* sbVo */);});
  };
  return E(_5n/* sbVp */);
},
_5r/* $fFunctorWorld2 */ = function(_5s/* sbV1 */, _5t/* sbV2 */, _5u/* sbV3 */){
  var _5v/* sbV4 */ = new T(function(){
    return B(A1(_5t/* sbV2 */,_5u/* sbV3 */));
  }),
  _5w/* sbVd */ = function(_5x/* sbV5 */){
    var _5y/* sbVc */ = function(_5z/* sbV6 */){
      var _5A/* sbVb */ = new T(function(){
        var _5B/* sbV7 */ = E(_5z/* sbV6 */);
        return new T2(0,new T(function(){
          return B(A1(_5s/* sbV1 */,_5B/* sbV7 */.a));
        }),_5B/* sbV7 */.b);
      });
      return new F(function(){return A1(_5x/* sbV5 */,_5A/* sbVb */);});
    };
    return new F(function(){return A1(_5v/* sbV4 */,_5y/* sbVc */);});
  };
  return E(_5w/* sbVd */);
},
_5C/* $fFunctorWorld */ = new T2(0,_5r/* Core.World.Internal.$fFunctorWorld2 */,_5i/* Core.World.Internal.$fFunctorWorld1 */),
_5D/* $fMonadWorld2 */ = function(_5E/* sbRG */, _5F/* sbRH */, _5G/* sbRI */){
  return new F(function(){return A1(_5G/* sbRI */,new T2(0,_5E/* sbRG */,_5F/* sbRH */));});
},
_5H/* $fApplicativeWorld */ = new T5(0,_5C/* Core.World.Internal.$fFunctorWorld */,_5D/* Core.World.Internal.$fMonadWorld2 */,_55/* Core.World.Internal.$fApplicativeWorld3 */,_4V/* Core.World.Internal.$fApplicativeWorld2 */,_4K/* Core.World.Internal.$fApplicativeWorld1 */),
_5I/* $fMonadWorld1 */ = function(_5J/* sbSy */, _5K/* sbSz */){
  return new F(function(){return err/* EXTERNAL */(_5J/* sbSy */);});
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
_79/* a17 */ = function(_7a/* sbS9 */, _7b/* sbSa */, _7c/* sbSb */){
  var _7d/* sbSc */ = new T(function(){
    return B(A1(_7b/* sbSa */,_7c/* sbSb */));
  }),
  _7e/* sbSk */ = function(_7f/* sbSd */){
    var _7g/* sbSj */ = function(_7h/* sbSe */){
      return new F(function(){return A1(_7f/* sbSd */,new T(function(){
        return new T2(0,_7a/* sbS9 */,E(_7h/* sbSe */).b);
      }));});
    };
    return new F(function(){return A1(_7d/* sbSc */,_7g/* sbSj */);});
  };
  return E(_7e/* sbSk */);
},
_7i/* a18 */ = function(_7j/* sbSl */, _7k/* sbSm */, _7l/* sbSn */){
  var _7m/* sbSo */ = new T(function(){
    return B(A1(_7k/* sbSm */,_7l/* sbSn */));
  }),
  _7n/* sbSx */ = function(_7o/* sbSp */){
    var _7p/* sbSw */ = function(_7q/* sbSq */){
      var _7r/* sbSv */ = new T(function(){
        var _7s/* sbSr */ = E(_7q/* sbSq */);
        return new T2(0,new T(function(){
          return B(A1(_7j/* sbSl */,_7s/* sbSr */.a));
        }),_7s/* sbSr */.b);
      });
      return new F(function(){return A1(_7o/* sbSp */,_7r/* sbSv */);});
    };
    return new F(function(){return A1(_7m/* sbSo */,_7p/* sbSw */);});
  };
  return E(_7n/* sbSx */);
},
_7t/* $fMonadWorld_$s$fFunctorStateT */ = new T2(0,_7i/* Core.World.Internal.a18 */,_79/* Core.World.Internal.a17 */),
_7u/* a22 */ = function(_7v/* sbTp */, _7w/* sbTq */, _7x/* sbTr */){
  var _7y/* sbTs */ = new T(function(){
    return B(A1(_7v/* sbTp */,_7x/* sbTr */));
  }),
  _7z/* sbTG */ = function(_7A/* sbTt */){
    var _7B/* sbTF */ = function(_7C/* sbTu */){
      var _7D/* sbTv */ = E(_7C/* sbTu */),
      _7E/* sbTE */ = function(_7F/* sbTy */){
        var _7G/* sbTz */ = E(_7F/* sbTy */);
        return new F(function(){return A1(_7A/* sbTt */,new T2(0,new T(function(){
          return B(A1(_7D/* sbTv */.a,_7G/* sbTz */.a));
        }),_7G/* sbTz */.b));});
      };
      return new F(function(){return A2(_7w/* sbTq */,_7D/* sbTv */.b, _7E/* sbTE */);});
    };
    return new F(function(){return A1(_7y/* sbTs */,_7B/* sbTF */);});
  };
  return E(_7z/* sbTG */);
},
_7H/* a23 */ = function(_7I/* sbTH */, _7J/* sbTI */, _7K/* sbTJ */){
  var _7L/* sbTK */ = new T(function(){
    return B(A1(_7I/* sbTH */,_7K/* sbTJ */));
  }),
  _7M/* sbTW */ = function(_7N/* sbTL */){
    var _7O/* sbTM */ = function(_7P/* sbTN */){
      return new F(function(){return A1(_7N/* sbTL */,E(_7P/* sbTN */));});
    };
    return new F(function(){return A1(_7L/* sbTK */,function(_7Q/* sbTR */){
      return new F(function(){return A2(_7J/* sbTI */,E(_7Q/* sbTR */).b, _7O/* sbTM */);});
    });});
  };
  return E(_7M/* sbTW */);
},
_7R/* a24 */ = function(_7S/* sbTX */, _7T/* sbTY */, _7U/* sbTZ */){
  var _7V/* sbU0 */ = new T(function(){
    return B(A1(_7S/* sbTX */,_7U/* sbTZ */));
  }),
  _7W/* sbUd */ = function(_7X/* sbU1 */){
    var _7Y/* sbUc */ = function(_7Z/* sbU2 */){
      var _80/* sbU3 */ = E(_7Z/* sbU2 */);
      return new F(function(){return A2(_7T/* sbTY */,_80/* sbU3 */.b, function(_81/* sbU6 */){
        return new F(function(){return A1(_7X/* sbU1 */,new T2(0,_80/* sbU3 */.a,E(_81/* sbU6 */).b));});
      });});
    };
    return new F(function(){return A1(_7V/* sbU0 */,_7Y/* sbUc */);});
  };
  return E(_7W/* sbUd */);
},
_82/* $fMonadWorld_$s$fApplicativeStateT */ = new T5(0,_7t/* Core.World.Internal.$fMonadWorld_$s$fFunctorStateT */,_5D/* Core.World.Internal.$fMonadWorld2 */,_7u/* Core.World.Internal.a22 */,_7H/* Core.World.Internal.a23 */,_7R/* Core.World.Internal.a24 */),
_83/* $fMonadWorld3 */ = function(_84/* B2 */, _85/* B1 */){
  return new F(function(){return _71/* Control.Monad.Trans.State.Strict.$fMonadStateT_$c>> */(_82/* Core.World.Internal.$fMonadWorld_$s$fApplicativeStateT */, _6z/* Haste.Concurrent.Monad.$fMonadCIO */, _84/* B2 */, _85/* B1 */);});
},
_86/* $fMonadWorld5 */ = function(_87/* sbRK */, _88/* sbRL */, _89/* sbRM */){
  var _8a/* sbRN */ = new T(function(){
    return B(A1(_87/* sbRK */,_89/* sbRM */));
  }),
  _8b/* sbRU */ = function(_8c/* sbRO */){
    return new F(function(){return A1(_8a/* sbRN */,function(_8d/* sbRP */){
      var _8e/* sbRQ */ = E(_8d/* sbRP */);
      return new F(function(){return A3(_88/* sbRL */,_8e/* sbRQ */.a, _8e/* sbRQ */.b, _8c/* sbRO */);});
    });});
  };
  return E(_8b/* sbRU */);
},
_8f/* $fMonadWorld */ = new T5(0,_5H/* Core.World.Internal.$fApplicativeWorld */,_86/* Core.World.Internal.$fMonadWorld5 */,_83/* Core.World.Internal.$fMonadWorld3 */,_5D/* Core.World.Internal.$fMonadWorld2 */,_5I/* Core.World.Internal.$fMonadWorld1 */),
_8g/* liftW1 */ = function(_8h/* sbRV */, _8i/* sbRW */, _8j/* sbRX */){
  return new F(function(){return A1(_8h/* sbRV */,function(_8k/* sbRY */){
    return new F(function(){return A1(_8j/* sbRX */,new T2(0,_8k/* sbRY */,_8i/* sbRW */));});
  });});
},
_8l/* $fMonadConcWorld */ = new T3(0,_8f/* Core.World.Internal.$fMonadWorld */,_8g/* Core.World.Internal.liftW1 */,_4G/* Core.World.Internal.$fMonadConcWorld1 */),
_8m/* $fMonadEventWorld1 */ = function(_8n/* sbZx */, _8o/* sbZy */, _8p/* sbZz */){
  var _8q/* sbZD */ = function(_8r/* sbZA */, _/* EXTERNAL */){
    return new F(function(){return _e/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(new T(function(){
      return B(A3(_8n/* sbZx */,_8r/* sbZA */, _8o/* sbZy */, _4D/* Core.World.Internal.$fMonadEventWorld2 */));
    }), _6/* GHC.Types.[] */, _/* EXTERNAL */);});
  };
  return new F(function(){return A1(_8p/* sbZz */,new T2(0,_8q/* sbZD */,_8o/* sbZy */));});
},
_8s/* $fMonadIOWorld1 */ = function(_8t/* sbUe */, _8u/* sbUf */, _8v/* sbUg */){
  var _8w/* sbUn */ = function(_/* EXTERNAL */){
    var _8x/* sbUi */ = B(A1(_8t/* sbUe */,_/* EXTERNAL */));
    return new T(function(){
      return B(A1(_8v/* sbUg */,new T2(0,_8x/* sbUi */,_8u/* sbUf */)));
    });
  };
  return new T1(0,_8w/* sbUn */);
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
_9I/* $wwithMVar */ = function(_9J/* s6ev */, _9K/* s6ew */, _9L/* s6ex */){
  var _9M/* s6ey */ = new T(function(){
    return B(_2V/* Haste.Concurrent.Monad.liftConc */(_9J/* s6ev */));
  }),
  _9N/* s6ez */ = B(_9x/* Haste.Concurrent.Monad.$p1MonadConc */(_9J/* s6ev */)),
  _9O/* s6eA */ = function(_9P/* s6eB */, _9Q/* s6eC */){
    var _9R/* s6eE */ = new T(function(){
      return B(A1(_9M/* s6ey */,function(_9S/* B1 */){
        return new F(function(){return _9B/* Haste.Concurrent.Monad.putMVar1 */(_9K/* s6ew */, _9Q/* s6eC */, _9S/* B1 */);});
      }));
    });
    return new F(function(){return A3(_9z/* GHC.Base.>> */,_9N/* s6ez */, _9R/* s6eE */, new T(function(){
      return B(A2(_6T/* GHC.Base.return */,_9N/* s6ez */, _9P/* s6eB */));
    }));});
  },
  _9T/* s6eG */ = function(_9U/* s6eH */){
    var _9V/* s6eI */ = E(_9U/* s6eH */);
    return new F(function(){return _9O/* s6eA */(_9V/* s6eI */.a, _9V/* s6eI */.b);});
  },
  _9W/* s6eP */ = function(_9X/* s6eN */){
    return new F(function(){return A3(_6u/* GHC.Base.>>= */,_9N/* s6ez */, new T(function(){
      return B(A1(_9L/* s6ex */,_9X/* s6eN */));
    }), _9T/* s6eG */);});
  },
  _9Y/* s6eM */ = new T(function(){
    return B(A2(_2V/* Haste.Concurrent.Monad.liftConc */,_9J/* s6ev */, function(_9S/* B1 */){
      return new F(function(){return _9F/* Haste.Concurrent.Monad.takeMVar1 */(_9K/* s6ew */, _9S/* B1 */);});
    }));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_9N/* s6ez */, _9Y/* s6eM */, _9W/* s6eP */);});
},
_9Z/* a36 */ = function(_a0/* sc47 */, _a1/* sc48 */, _a2/* sc49 */){
  return new F(function(){return A1(_a2/* sc49 */,new T2(0,new T2(0,new T(function(){
    return E(E(_a0/* sc47 */).a);
  }),_a0/* sc47 */),_a1/* sc48 */));});
},
_a3/* a37 */ = 16,
_a4/* a38 */ = function(_a5/* sc4i */, _a6/* sc4j */, _a7/* sc4k */){
  var _a8/* sc4l */ = E(_a5/* sc4i */);
  if(!_a8/* sc4l */._){
    return new F(function(){return A1(_a7/* sc4k */,new T2(0,_6/* GHC.Types.[] */,_a6/* sc4j */));});
  }else{
    var _a9/* sc4D */ = function(_aa/* sc4s */){
      var _ab/* sc4t */ = E(_aa/* sc4s */);
      return new F(function(){return _a4/* Core.World.Internal.a38 */(_a8/* sc4l */.b, _ab/* sc4t */.b, function(_ac/* sc4w */){
        var _ad/* sc4x */ = E(_ac/* sc4w */);
        return new F(function(){return A1(_a7/* sc4k */,new T2(0,new T2(1,_ab/* sc4t */.a,_ad/* sc4x */.a),_ad/* sc4x */.b));});
      });});
    };
    return new F(function(){return A2(E(_a8/* sc4l */.a).a,_a6/* sc4j */, _a9/* sc4D */);});
  }
},
_ae/* a39 */ = function(_af/* sc4E */, _ag/* sc4F */, _ah/* sc4G */){
  var _ai/* sc4H */ = E(_af/* sc4E */);
  if(!_ai/* sc4H */._){
    return new F(function(){return A1(_ah/* sc4G */,new T2(0,_6/* GHC.Types.[] */,_ag/* sc4F */));});
  }else{
    var _aj/* sc4L */ = E(_ai/* sc4H */.a),
    _ak/* sc50 */ = function(_al/* sc4O */){
      var _am/* sc4P */ = E(_al/* sc4O */),
      _an/* sc4Z */ = function(_ao/* sc4S */){
        var _ap/* sc4T */ = E(_ao/* sc4S */),
        _aq/* sc4U */ = _ap/* sc4T */.a;
        return new F(function(){return A1(_ah/* sc4G */,new T2(0,new T(function(){
          if(!E(_am/* sc4P */.a)){
            return E(_aq/* sc4U */);
          }else{
            return new T2(1,_aj/* sc4L */,_aq/* sc4U */);
          }
        }),_ap/* sc4T */.b));});
      };
      return new F(function(){return _ae/* Core.World.Internal.a39 */(_ai/* sc4H */.b, _am/* sc4P */.b, _an/* sc4Z */);});
    };
    return new F(function(){return A2(_aj/* sc4L */.b,_ag/* sc4F */, _ak/* sc50 */);});
  }
},
_ar/* a3 */ = function(_as/* sbRc */, _at/* sbRd */, _au/* sbRe */){
  return new F(function(){return A1(_au/* sbRe */,new T2(0,new T2(0,new T(function(){
    return E(_as/* sbRc */).b;
  }),_as/* sbRc */),_at/* sbRd */));});
},
_av/* False */ = false,
_aw/* True */ = true,
_ax/* a2 */ = function(_ay/* sbQX */, _az/* sbQY */, _aA/* sbQZ */){
  return new F(function(){return A1(_aA/* sbQZ */,new T2(0,new T2(0,new T(function(){
    var _aB/* sbR5 */ = E(E(_ay/* sbQX */).c);
    if(!_aB/* sbR5 */._){
      return __Z/* EXTERNAL */;
    }else{
      return new T1(1,_aB/* sbR5 */.b);
    }
  }),_ay/* sbQX */),_az/* sbQY */));});
},
_aC/* Nil */ = __Z/* EXTERNAL */,
_aD/* $wincr */ = function(_aE/* shf5 */, _aF/* shf6 */, _aG/* shf7 */, _aH/* shf8 */){
  var _aI/* shf9 */ = E(_aH/* shf8 */);
  switch(_aI/* shf9 */._){
    case 0:
      return new T3(2,_aF/* shf6 */,_aG/* shf7 */,_aC/* Data.PQueue.Internals.Nil */);
    case 1:
      return new T3(2,_aF/* shf6 */,_aG/* shf7 */,_aI/* shf9 */.a);
    default:
      var _aJ/* shfb */ = _aI/* shf9 */.a,
      _aK/* shfc */ = _aI/* shf9 */.b,
      _aL/* shfd */ = _aI/* shf9 */.c;
      return new T1(1,new T(function(){
        if(!B(A2(_aE/* shf5 */,_aF/* shf6 */, _aJ/* shfb */))){
          return B(_aD/* Data.PQueue.Internals.$wincr */(_aE/* shf5 */, _aJ/* shfb */, new T3(0,_aF/* shf6 */,_aG/* shf7 */,_aK/* shfc */), _aL/* shfd */));
        }else{
          return B(_aD/* Data.PQueue.Internals.$wincr */(_aE/* shf5 */, _aF/* shf6 */, new T3(0,_aJ/* shfb */,_aK/* shfc */,_aG/* shf7 */), _aL/* shfd */));
        }
      }));
  }
},
_aM/* extractBin */ = function(_aN/* shgw */, _aO/* shgx */){
  var _aP/* shgy */ = E(_aO/* shgx */);
  switch(_aP/* shgy */._){
    case 0:
      return __Z/* EXTERNAL */;
    case 1:
      var _aQ/* shgA */ = B(_aM/* Data.PQueue.Internals.extractBin */(_aN/* shgw */, _aP/* shgy */.a));
      if(!_aQ/* shgA */._){
        return __Z/* EXTERNAL */;
      }else{
        var _aR/* shgE */ = E(_aQ/* shgA */.b);
        return new T3(1,_aQ/* shgA */.a,_aR/* shgE */.c,new T3(2,_aR/* shgE */.a,_aR/* shgE */.b,_aQ/* shgA */.c));
      }
      break;
    default:
      var _aS/* shgJ */ = _aP/* shgy */.a,
      _aT/* shgK */ = _aP/* shgy */.b,
      _aU/* shgL */ = _aP/* shgy */.c,
      _aV/* shgM */ = B(_aM/* Data.PQueue.Internals.extractBin */(_aN/* shgw */, _aU/* shgL */));
      if(!_aV/* shgM */._){
        return new T3(1,_aS/* shgJ */,_aT/* shgK */,new T1(1,_aU/* shgL */));
      }else{
        var _aW/* shgO */ = _aV/* shgM */.a,
        _aX/* shgQ */ = _aV/* shgM */.c;
        if(!B(A2(_aN/* shgw */,_aS/* shgJ */, _aW/* shgO */))){
          var _aY/* shgS */ = E(_aV/* shgM */.b),
          _aZ/* shgT */ = _aY/* shgS */.a,
          _b0/* shgU */ = _aY/* shgS */.b;
          return new T3(1,_aW/* shgO */,_aY/* shgS */.c,new T1(1,new T(function(){
            if(!B(A2(_aN/* shgw */,_aS/* shgJ */, _aZ/* shgT */))){
              return B(_aD/* Data.PQueue.Internals.$wincr */(_aN/* shgw */, _aZ/* shgT */, new T3(0,_aS/* shgJ */,_aT/* shgK */,_b0/* shgU */), _aX/* shgQ */));
            }else{
              return B(_aD/* Data.PQueue.Internals.$wincr */(_aN/* shgw */, _aS/* shgJ */, new T3(0,_aZ/* shgT */,_b0/* shgU */,_aT/* shgK */), _aX/* shgQ */));
            }
          })));
        }else{
          return new T3(1,_aS/* shgJ */,_aT/* shgK */,new T1(1,_aU/* shgL */));
        }
      }
  }
},
_b1/* a26 */ = function(_b2/* sbUo */){
  var _b3/* sbUp */ = new T(function(){
    var _b4/* sbUq */ = E(_b2/* sbUo */),
    _b5/* sbUv */ = E(_b4/* sbUq */.c);
    if(!_b5/* sbUv */._){
      var _b6/* sbUv#result */ = __Z/* EXTERNAL */;
    }else{
      var _b7/* sbUP */ = B(_aM/* Data.PQueue.Internals.extractBin */(function(_b8/* sbUz */, _b9/* sbUA */){
        var _ba/* sbUH */ = E(E(_b8/* sbUz */).a),
        _bb/* sbUJ */ = E(E(_b9/* sbUA */).a);
        return (_ba/* sbUH */>=_bb/* sbUJ */) ? _ba/* sbUH */==_bb/* sbUJ */ : true;
      }, _b5/* sbUv */.c));
      if(!_b7/* sbUP */._){
        var _bc/* sbUP#result */ = __Z/* EXTERNAL */;
      }else{
        var _bc/* sbUP#result */ = new T3(1,_b5/* sbUv */.a-1|0,_b7/* sbUP */.a,E(_b7/* sbUP */.c));
      }
      var _b6/* sbUv#result */ = _bc/* sbUP#result */;
    }
    return new T4(0,E(_b4/* sbUq */.a),_b4/* sbUq */.b,E(_b6/* sbUv#result */),E(_b4/* sbUq */.d));
  });
  return function(_bd/* sbUX */, _be/* sbUY */){
    return new F(function(){return A1(_be/* sbUY */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,_b3/* sbUp */),_bd/* sbUX */));});
  };
},
_bf/* a1 */ = function(_bg/* sbQL */, _bh/* sbQM */, _bi/* sbQN */){
  return new F(function(){return A1(_bi/* sbQN */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
    var _bj/* sbQO */ = E(_bg/* sbQL */);
    return new T4(0,E(_bj/* sbQO */.a),_bj/* sbQO */.b+1|0,E(_bj/* sbQO */.c),E(_bj/* sbQO */.d));
  })),_bh/* sbQM */));});
},
_bk/* a40 */ = function(_bl/* sc51 */, _bm/* sc52 */){
  return new T1(0,B(_bn/* Core.World.Internal.$wa7 */(_bl/* sc51 */)));
},
_bo/* absentError */ = function(_bp/* s4nFP */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Oops!  Entered absent arg ", new T(function(){
    return B(unCStr/* EXTERNAL */(_bp/* s4nFP */));
  }))));});
},
_bq/* eta */ = new T(function(){
  return B(_bo/* Control.Exception.Base.absentError */("w_saRG ((), MVar WorldState) -> Action"));
}),
_br/* eta1 */ = function(_bs/* sc55 */){
  return new F(function(){return _bk/* Core.World.Internal.a40 */(E(_bs/* sc55 */).b, _bq/* Core.World.Internal.eta */);});
},
_bt/* lvl6 */ = function(_bu/* sc59 */){
  var _bv/* sc5c */ = E(_bu/* sc59 */).b;
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bv/* sc5c */, _bf/* Core.World.Internal.a1 */, _bv/* sc5c */, _br/* Core.World.Internal.eta1 */]);});
},
_bw/* while */ = function(_bx/* s6eo */, _by/* s6ep */){
  var _bz/* s6eq */ = new T(function(){
    return B(A2(_6T/* GHC.Base.return */,_bx/* s6eo */, _7/* GHC.Tuple.() */));
  }),
  _bA/* s6er */ = new T(function(){
    return B(_bw/* Core.Util.while */(_bx/* s6eo */, _by/* s6ep */));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_bx/* s6eo */, _by/* s6ep */, function(_bB/* s6es */){
    return (!E(_bB/* s6es */)) ? E(_bz/* s6eq */) : E(_bA/* s6er */);
  });});
},
_bC/* lvl7 */ = function(_bD/* sc5d */){
  var _bE/* sc5e */ = E(_bD/* sc5d */),
  _bF/* sc5M */ = function(_bG/* sc5h */, _bH/* sc5i */){
    var _bI/* sc5j */ = function(_bJ/* sc5k */){
      return new F(function(){return A1(_bH/* sc5i */,new T2(0,_aw/* GHC.Types.True */,E(_bJ/* sc5k */).b));});
    },
    _bK/* sc5L */ = function(_bL/* sc5p */){
      var _bM/* sc5q */ = E(_bL/* sc5p */),
      _bN/* sc5s */ = _bM/* sc5q */.b,
      _bO/* sc5t */ = E(_bM/* sc5q */.a);
      if(!_bO/* sc5t */._){
        return new F(function(){return A1(_bH/* sc5i */,new T2(0,_av/* GHC.Types.False */,_bN/* sc5s */));});
      }else{
        var _bP/* sc5w */ = E(_bO/* sc5t */.a);
        if(E(_bP/* sc5w */.a)<=E(_bE/* sc5e */.a)){
          var _bQ/* sc5F */ = new T(function(){
            return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bN/* sc5s */, _b1/* Core.World.Internal.a26 */, _bN/* sc5s */, _bI/* sc5j */]));
          });
          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_bP/* sc5w */.b, _7/* GHC.Tuple.() */, function(_bR/* sc5G */){
            return E(_bQ/* sc5F */);
          })));
        }else{
          return new F(function(){return A1(_bH/* sc5i */,new T2(0,_av/* GHC.Types.False */,_bN/* sc5s */));});
        }
      }
    };
    return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bG/* sc5h */, _ax/* Core.World.Internal.a2 */, _bG/* sc5h */, _bK/* sc5L */]);});
  };
  return new F(function(){return A(_bw/* Core.Util.while */,[_8f/* Core.World.Internal.$fMonadWorld */, _bF/* sc5M */, _bE/* sc5e */.b, _bt/* Core.World.Internal.lvl6 */]);});
},
_bS/* lvl8 */ = function(_bT/* sc5N */){
  var _bU/* sc5Q */ = E(_bT/* sc5N */).b;
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bU/* sc5Q */, _ar/* Core.World.Internal.a3 */, _bU/* sc5Q */, _bC/* Core.World.Internal.lvl7 */]);});
},
_bV/* lvl9 */ = function(_bW/* sc5R */){
  var _bX/* sc5S */ = E(_bW/* sc5R */),
  _bY/* sc5U */ = _bX/* sc5S */.b,
  _bZ/* sc67 */ = function(_c0/* sc5V */, _c1/* sc5W */, _c2/* sc5X */){
    return new F(function(){return A1(_c2/* sc5X */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
      var _c3/* sc5Y */ = E(_c0/* sc5V */);
      return new T4(0,E(_bX/* sc5S */.a),_c3/* sc5Y */.b,E(_c3/* sc5Y */.c),E(_c3/* sc5Y */.d));
    })),_c1/* sc5W */));});
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bY/* sc5U */, _bZ/* sc67 */, _bY/* sc5U */, _bS/* Core.World.Internal.lvl8 */]);});
},
_c4/* lvl10 */ = function(_c5/* sc68 */){
  var _c6/* sc69 */ = E(_c5/* sc68 */),
  _c7/* sc6a */ = _c6/* sc69 */.a;
  return new F(function(){return _a4/* Core.World.Internal.a38 */(_c7/* sc6a */, _c6/* sc69 */.b, function(_c8/* sc6c */){
    return new F(function(){return _ae/* Core.World.Internal.a39 */(_c7/* sc6a */, E(_c8/* sc6c */).b, _bV/* Core.World.Internal.lvl9 */);});
  });});
},
_bn/* $wa7 */ = function(_c9/* sc6h */){
  var _ca/* sc6i */ = new T(function(){
    return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _c9/* sc6h */, _9Z/* Core.World.Internal.a36 */, _c9/* sc6h */, _c4/* Core.World.Internal.lvl10 */]));
  });
  return new F(function(){return _9p/* Haste.Concurrent.$wa */(_a3/* Core.World.Internal.a37 */, function(_cb/* sc6j */){
    return E(_ca/* sc6i */);
  });});
},
_cc/* MouseDown */ = 2,
_cd/* MouseMove */ = 4,
_ce/* MouseUp */ = 3,
_cf/* a */ = function(_cg/* sbQx */, _ch/* sbQy */, _ci/* sbQz */){
  return new F(function(){return A1(_ci/* sbQz */,new T2(0,new T2(0,new T(function(){
    return E(E(E(_cg/* sbQx */).d).b);
  }),_cg/* sbQx */),_ch/* sbQy */));});
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
_d4/* oneway2 */ = function(_d5/* sbQt */, _d6/* sbQu */){
  return new F(function(){return A1(_d6/* sbQu */,new T2(0,_7/* GHC.Tuple.() */,_d5/* sbQt */));});
},
_d7/* $wa5 */ = function(_d8/* sc6l */, _d9/* sc6m */){
  return function(_/* EXTERNAL */){
    var _da/* sc6o */ = nMV/* EXTERNAL */(_cs/* Core.World.Internal.lvl14 */),
    _db/* sc6q */ = _da/* sc6o */,
    _dc/* sc6s */ = function(_dd/* sc6t */){
      return new F(function(){return A1(_d9/* sc6m */,E(_dd/* sc6t */).a);});
    },
    _de/* sc6x */ = function(_df/* sc6y */){
      return new F(function(){return A2(_d8/* sc6l */,E(_df/* sc6y */).b, _dc/* sc6s */);});
    },
    _dg/* sc8o */ = function(_/* EXTERNAL */){
      var _dh/* sc6D */ = nMV/* EXTERNAL */(_cm/* Core.World.Internal.lvl11 */),
      _di/* sc6F */ = _dh/* sc6D */,
      _dj/* sc8k */ = new T(function(){
        var _dk/* sc74 */ = function(_dl/* sc78 */){
          return new F(function(){return _dm/* sc75 */(E(_dl/* sc78 */).b);});
        },
        _dm/* sc75 */ = function(_dn/* sc7c */){
          var _do/* sc8h */ = function(_dp/* sc7d */){
            var _dq/* sc8g */ = function(_dr/* sc7e */){
              var _ds/* sc7f */ = E(_dr/* sc7e */),
              _dt/* sc7h */ = _ds/* sc7f */.b,
              _du/* sc7i */ = E(_dp/* sc7d */),
              _dv/* sc7l */ = function(_dw/* sc7m */, _dx/* sc7n */, _dy/* sc7o */){
                var _dz/* sc7p */ = function(_dA/*  sc7q */, _dB/*  sc7r */){
                  while(1){
                    var _dC/*  sc7p */ = B((function(_dD/* sc7q */, _dE/* sc7r */){
                      var _dF/* sc7s */ = E(_dE/* sc7r */);
                      switch(_dF/* sc7s */._){
                        case 0:
                          _dA/*  sc7q */ = new T(function(){
                            return B(_dz/* sc7p */(_dD/* sc7q */, _dF/* sc7s */.d));
                          });
                          _dB/*  sc7r */ = _dF/* sc7s */.c;
                          return __continue/* EXTERNAL */;
                        case 1:
                          var _dG/* sc7A */ = new T(function(){
                            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _dF/* sc7s */.b, _dw/* sc7m */));
                          }),
                          _dH/* sc7K */ = function(_dI/* sc7B */){
                            var _dJ/* sc7C */ = new T(function(){
                              return B(A1(_dG/* sc7A */,_dI/* sc7B */));
                            }),
                            _dK/* sc7J */ = function(_dL/* sc7D */){
                              return new F(function(){return A1(_dJ/* sc7C */,function(_dM/* sc7E */){
                                return new F(function(){return A2(_dD/* sc7q */,E(_dM/* sc7E */).b, _dL/* sc7D */);});
                              });});
                            };
                            return E(_dK/* sc7J */);
                          };
                          return E(_dH/* sc7K */);
                        default:
                          return E(_dD/* sc7q */);
                      }
                    })(_dA/*  sc7q */, _dB/*  sc7r */));
                    if(_dC/*  sc7p */!=__continue/* EXTERNAL */){
                      return _dC/*  sc7p */;
                    }
                  }
                },
                _dN/* sc7L */ = E(_ds/* sc7f */.a);
                if(!_dN/* sc7L */._){
                  var _dO/* sc7O */ = _dN/* sc7L */.c,
                  _dP/* sc7P */ = _dN/* sc7L */.d;
                  if(_dN/* sc7L */.b>=0){
                    return new F(function(){return A(_dz/* sc7p */,[new T(function(){
                      return B(_dz/* sc7p */(_d4/* Core.World.Internal.oneway2 */, _dP/* sc7P */));
                    }), _dO/* sc7O */, _dx/* sc7n */, _dy/* sc7o */]);});
                  }else{
                    return new F(function(){return A(_dz/* sc7p */,[new T(function(){
                      return B(_dz/* sc7p */(_d4/* Core.World.Internal.oneway2 */, _dO/* sc7O */));
                    }), _dP/* sc7P */, _dx/* sc7n */, _dy/* sc7o */]);});
                  }
                }else{
                  return new F(function(){return A(_dz/* sc7p */,[_d4/* Core.World.Internal.oneway2 */, _dN/* sc7L */, _dx/* sc7n */, _dy/* sc7o */]);});
                }
              };
              switch(E(_du/* sc7i */.a)){
                case 2:
                  return new F(function(){return _dv/* sc7l */(_cl/* Core.World.Internal.lvl1 */, _dt/* sc7h */, _dk/* sc74 */);});
                  break;
                case 3:
                  return new F(function(){return _dv/* sc7l */(_ck/* Core.World.Internal.lvl */, _dt/* sc7h */, _dk/* sc74 */);});
                  break;
                case 4:
                  var _dQ/* sc7V */ = new T(function(){
                    return E(E(_du/* sc7i */.b).a);
                  });
                  return new F(function(){return _dv/* sc7l */(new T1(1,new T2(0,new T(function(){
                    return E(E(_dQ/* sc7V */).a);
                  }),new T(function(){
                    return E(E(_dQ/* sc7V */).b);
                  }))), _dt/* sc7h */, _dk/* sc74 */);});
                  break;
                default:
                  return new F(function(){return _dm/* sc75 */(_dt/* sc7h */);});
              }
            };
            return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _dn/* sc7c */, _cf/* Core.World.Internal.a */, _dn/* sc7c */, _dq/* sc8g */]);});
          };
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_di/* sc6F */, _do/* sc8h */)));
        };
        return B(_dm/* sc75 */(_db/* sc6q */));
      }),
      _dR/* sc72 */ = new T(function(){
        var _dS/* sc6H */ = new T(function(){
          return B(_cC/* Haste.Events.Core.onEvent */(_8z/* Core.World.Internal.$fMonadEventWorld */, _4C/* Haste.DOM.Core.$fIsElemElem */, _4z/* Haste.Events.MouseEvents.$fEventMouseEvent */, _cj/* Haste.DOM.Core.document1 */, _cd/* Haste.Events.MouseEvents.MouseMove */, function(_dT/* sc6I */){
            return new F(function(){return _2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _di/* sc6F */, new T2(0,_cd/* Haste.Events.MouseEvents.MouseMove */,_dT/* sc6I */));});
          }));
        }),
        _dU/* sc6L */ = new T(function(){
          return B(_cC/* Haste.Events.Core.onEvent */(_8z/* Core.World.Internal.$fMonadEventWorld */, _4C/* Haste.DOM.Core.$fIsElemElem */, _4z/* Haste.Events.MouseEvents.$fEventMouseEvent */, _cj/* Haste.DOM.Core.document1 */, _ce/* Haste.Events.MouseEvents.MouseUp */, function(_dV/* sc6M */){
            return new F(function(){return _2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _di/* sc6F */, new T2(0,_ce/* Haste.Events.MouseEvents.MouseUp */,_dV/* sc6M */));});
          }));
        }),
        _dW/* sc6P */ = function(_dX/* sc6Q */){
          return new F(function(){return A2(_dU/* sc6L */,E(_dX/* sc6Q */).b, _de/* sc6x */);});
        };
        return B(A(_cC/* Haste.Events.Core.onEvent */,[_8z/* Core.World.Internal.$fMonadEventWorld */, _4C/* Haste.DOM.Core.$fIsElemElem */, _4z/* Haste.Events.MouseEvents.$fEventMouseEvent */, _cj/* Haste.DOM.Core.document1 */, _cc/* Haste.Events.MouseEvents.MouseDown */, function(_dY/* sc6U */){
          return new F(function(){return _2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _di/* sc6F */, new T2(0,_cc/* Haste.Events.MouseEvents.MouseDown */,_dY/* sc6U */));});
        }, _db/* sc6q */, function(_dZ/* sc6X */){
          return new F(function(){return A2(_dS/* sc6H */,E(_dZ/* sc6X */).b, _dW/* sc6P */);});
        }]));
      });
      return new T1(1,new T2(1,_dR/* sc72 */,new T2(1,_dj/* sc8k */,_6/* GHC.Types.[] */)));
    };
    return new T1(1,new T2(1,new T1(0,_dg/* sc8o */),new T2(1,new T(function(){
      return new T1(0,B(_bn/* Core.World.Internal.$wa7 */(_db/* sc6q */)));
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
_e8/* $wa */ = function(_e9/* smYx */, _ea/* smYy */, _eb/* smYz */, _ec/* smYA */){
  return function(_/* EXTERNAL */){
    var _ed/* smYC */ = E(_e9/* smYx */),
    _ee/* smYE */ = rMV/* EXTERNAL */(_ed/* smYC */),
    _ef/* smYH */ = E(_ee/* smYE */);
    if(!_ef/* smYH */._){
      var _eg/* smYK */ = B(A2(_ea/* smYy */,_ef/* smYH */.a, _/* EXTERNAL */)),
      _eh/* smZw */ = function(_ei/* smYN */, _/* EXTERNAL */){
        var _ej/* smYP */ = function(_/* EXTERNAL */){
          var _ek/* smYS */ = rMV/* EXTERNAL */(_ed/* smYC */),
          _el/* smYV */ = function(_/* EXTERNAL */, _em/* smYX */){
            var _en/* smYY */ = function(_/* EXTERNAL */){
              var _eo/* smZ9 */ = __createJSFunc/* EXTERNAL */(2, function(_ep/* smZ0 */, _/* EXTERNAL */){
                var _eq/* smZ2 */ = B(_er/* smYQ */(_/* EXTERNAL */, _/* EXTERNAL */));
                return _48/* Haste.Prim.Any.jsNull */;
              }),
              _es/* smZf */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _eo/* smZ9 */);
              return _7/* GHC.Tuple.() */;
            },
            _et/* smZi */ = E(_em/* smYX */);
            if(!_et/* smZi */._){
              return new F(function(){return _en/* smYY */(_/* EXTERNAL */);});
            }else{
              var _eu/* smZk */ = B(A2(_ea/* smYy */,_et/* smZi */.a, _/* EXTERNAL */));
              return new F(function(){return _en/* smYY */(_/* EXTERNAL */);});
            }
          },
          _ev/* smZn */ = E(_ek/* smYS */);
          if(!_ev/* smZn */._){
            return new F(function(){return _el/* smYV */(_/* EXTERNAL */, new T1(1,_ev/* smZn */.a));});
          }else{
            return new F(function(){return _el/* smYV */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
        },
        _er/* smYQ */ = function(_ew/* smZs */, _/* EXTERNAL */){
          return new F(function(){return _ej/* smYP */(_/* EXTERNAL */);});
        },
        _ex/* smZt */ = B(_er/* smYQ */(_/* EXTERNAL */, _/* EXTERNAL */));
        return _48/* Haste.Prim.Any.jsNull */;
      },
      _ey/* smZA */ = __createJSFunc/* EXTERNAL */(2, E(_eh/* smZw */)),
      _ez/* smZG */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _ey/* smZA */);
      return new T(function(){
        return B(A1(_ec/* smYA */,new T2(0,_7/* GHC.Tuple.() */,_eb/* smYz */)));
      });
    }else{
      var _eA/* sn0v */ = function(_eB/* smZM */, _/* EXTERNAL */){
        var _eC/* smZO */ = function(_/* EXTERNAL */){
          var _eD/* smZR */ = rMV/* EXTERNAL */(_ed/* smYC */),
          _eE/* smZU */ = function(_/* EXTERNAL */, _eF/* smZW */){
            var _eG/* smZX */ = function(_/* EXTERNAL */){
              var _eH/* sn08 */ = __createJSFunc/* EXTERNAL */(2, function(_eI/* smZZ */, _/* EXTERNAL */){
                var _eJ/* sn01 */ = B(_eK/* smZP */(_/* EXTERNAL */, _/* EXTERNAL */));
                return _48/* Haste.Prim.Any.jsNull */;
              }),
              _eL/* sn0e */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _eH/* sn08 */);
              return _7/* GHC.Tuple.() */;
            },
            _eM/* sn0h */ = E(_eF/* smZW */);
            if(!_eM/* sn0h */._){
              return new F(function(){return _eG/* smZX */(_/* EXTERNAL */);});
            }else{
              var _eN/* sn0j */ = B(A2(_ea/* smYy */,_eM/* sn0h */.a, _/* EXTERNAL */));
              return new F(function(){return _eG/* smZX */(_/* EXTERNAL */);});
            }
          },
          _eO/* sn0m */ = E(_eD/* smZR */);
          if(!_eO/* sn0m */._){
            return new F(function(){return _eE/* smZU */(_/* EXTERNAL */, new T1(1,_eO/* sn0m */.a));});
          }else{
            return new F(function(){return _eE/* smZU */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
        },
        _eK/* smZP */ = function(_eP/* sn0r */, _/* EXTERNAL */){
          return new F(function(){return _eC/* smZO */(_/* EXTERNAL */);});
        },
        _eQ/* sn0s */ = B(_eK/* smZP */(_/* EXTERNAL */, _/* EXTERNAL */));
        return _48/* Haste.Prim.Any.jsNull */;
      },
      _eR/* sn0z */ = __createJSFunc/* EXTERNAL */(2, E(_eA/* sn0v */)),
      _eS/* sn0F */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _eR/* sn0z */);
      return new T(function(){
        return B(A1(_ec/* smYA */,new T2(0,_7/* GHC.Tuple.() */,_eb/* smYz */)));
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
_eY/* a22 */ = function(_eZ/* saK6 */, _f0/* saK7 */, _f1/* saK8 */){
  return new F(function(){return A1(_f1/* saK8 */,new T2(0,new T2(0,_eZ/* saK6 */,_eZ/* saK6 */),_f0/* saK7 */));});
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
_fD/* valueOf1 */ = function(_fE/* sb0p */, _fF/* sb0q */, _fG/* sb0r */){
  var _fH/* sb0s */ = E(_fE/* sb0p */);
  switch(_fH/* sb0s */._){
    case 0:
      return new F(function(){return _5D/* Core.World.Internal.$fMonadWorld2 */(_fH/* sb0s */.a, _fF/* sb0q */, _fG/* sb0r */);});
      break;
    case 1:
      return new F(function(){return _8s/* Core.World.Internal.$fMonadIOWorld1 */(_fH/* sb0s */.a, _fF/* sb0q */, _fG/* sb0r */);});
      break;
    case 2:
      var _fI/* sb0A */ = E(_fH/* sb0s */.a).c,
      _fJ/* sb0K */ = function(_fK/* sb0B */){
        var _fL/* sb0C */ = new T(function(){
          var _fM/* sb0E */ = new T(function(){
            return B(A1(_fH/* sb0s */.b,new T(function(){
              return B(_fB/* Data.Tuple.fst */(_fK/* sb0B */));
            })));
          });
          return B(A1(_fG/* sb0r */,new T2(0,_fM/* sb0E */,_fF/* sb0q */)));
        });
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_fI/* sb0A */, _fK/* sb0B */, function(_fN/* sb0G */){
          return E(_fL/* sb0C */);
        })));
      };
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_fI/* sb0A */, _fJ/* sb0K */)));
    default:
      var _fO/* sb0S */ = E(_fH/* sb0s */.a).c,
      _fP/* sb17 */ = function(_fQ/* sb0T */){
        var _fR/* sb0U */ = function(_/* EXTERNAL */){
          var _fS/* sb0X */ = B(A2(_fH/* sb0s */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_fQ/* sb0T */));
          }), _/* EXTERNAL */));
          return new T(function(){
            return B(A1(_fG/* sb0r */,new T2(0,_fS/* sb0X */,_fF/* sb0q */)));
          });
        };
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_fO/* sb0S */, _fQ/* sb0T */, function(_fT/* sb13 */){
          return E(new T1(0,_fR/* sb0U */));
        })));
      };
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_fO/* sb0S */, _fP/* sb17 */)));
  }
},
_fU/* applyTransform_world */ = function(_fV/*  sbZ9 */, _fW/*  sbZa */, _fX/*  sbZb */, _fY/*  sbZc */, _fZ/*  sbZd */, _g0/*  sbZe */, _g1/*  sbZf */){
  while(1){
    var _g2/*  applyTransform_world */ = B((function(_g3/* sbZ9 */, _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */){
      var _ga/* sbZg */ = new T(function(){
        return 0*E(_g4/* sbZa */)+0*E(_g5/* sbZb */)+E(_g6/* sbZc */);
      }),
      _gb/* sbZr */ = new T(function(){
        return 0*E(_g7/* sbZd */)+0*E(_g8/* sbZe */)+E(_g9/* sbZf */);
      }),
      _gc/* sbZC */ = B(_fo/* Control.Monad.Skeleton.debone */(_g3/* sbZ9 */));
      if(!_gc/* sbZC */._){
        return function(_gd/* _fa_1 */, _ge/* _fa_2 */){
          return new F(function(){return _5D/* Core.World.Internal.$fMonadWorld2 */(_gc/* sbZC */.a, _gd/* _fa_1 */, _ge/* _fa_2 */);});
        };
      }else{
        var _gf/* sbZF */ = _gc/* sbZC */.b,
        _gg/* sbZG */ = E(_gc/* sbZC */.a);
        switch(_gg/* sbZG */._){
          case 0:
            var _gh/*   sbZa */ = _g4/* sbZa */,
            _gi/*   sbZb */ = _g5/* sbZb */,
            _gj/*   sbZc */ = _g6/* sbZc */,
            _gk/*   sbZd */ = _g7/* sbZd */,
            _gl/*   sbZe */ = _g8/* sbZe */,
            _gm/*   sbZf */ = _g9/* sbZf */;
            _fV/*  sbZ9 */ = B(A1(_gf/* sbZF */,_gg/* sbZG */.b));
            _fW/*  sbZa */ = _gh/*   sbZa */;
            _fX/*  sbZb */ = _gi/*   sbZb */;
            _fY/*  sbZc */ = _gj/*   sbZc */;
            _fZ/*  sbZd */ = _gk/*   sbZd */;
            _g0/*  sbZe */ = _gl/*   sbZe */;
            _g1/*  sbZf */ = _gm/*   sbZf */;
            return __continue/* EXTERNAL */;
          case 1:
            var _gn/* sbZU */ = function(_go/* sbZL */, _gp/* sbZM */){
              var _gq/* sbZT */ = function(_/* EXTERNAL */){
                var _gr/* sbZO */ = B(A1(_gg/* sbZG */.a,_/* EXTERNAL */));
                return new T(function(){
                  return B(A(_fU/* Core.Render.Internal.applyTransform_world */,[B(A1(_gf/* sbZF */,_gr/* sbZO */)), _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */, _go/* sbZL */, _gp/* sbZM */]));
                });
              };
              return new T1(0,_gq/* sbZT */);
            };
            return E(_gn/* sbZU */);
          case 2:
            var _gs/* sbZX */ = new T(function(){
              return B(A(_gg/* sbZG */.a,[_g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */]));
            }),
            _gt/* sbZY */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sbZF */,_gg/* sbZG */.b)), _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */));
            }),
            _gu/* sc09 */ = function(_gv/* sc00 */){
              var _gw/* sc01 */ = new T(function(){
                return B(A1(_gs/* sbZX */,_gv/* sc00 */));
              }),
              _gx/* sc08 */ = function(_gy/* sc02 */){
                return new F(function(){return A1(_gw/* sc01 */,function(_gz/* sc03 */){
                  return new F(function(){return A2(_gt/* sbZY */,E(_gz/* sc03 */).b, _gy/* sc02 */);});
                });});
              };
              return E(_gx/* sc08 */);
            };
            return E(_gu/* sc09 */);
          case 3:
            var _gA/* sc0d */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(_gg/* sbZG */.b, _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */));
            }),
            _gB/* sc0e */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sbZF */,_gg/* sbZG */.c)), _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */));
            }),
            _gC/* sc0p */ = function(_gD/* sc0g */){
              var _gE/* sc0h */ = new T(function(){
                return B(A1(_gA/* sc0d */,_gD/* sc0g */));
              }),
              _gF/* sc0o */ = function(_gG/* sc0i */){
                return new F(function(){return A1(_gE/* sc0h */,function(_gH/* sc0j */){
                  return new F(function(){return A2(_gB/* sc0e */,E(_gH/* sc0j */).b, _gG/* sc0i */);});
                });});
              };
              return E(_gF/* sc0o */);
            };
            return E(_gC/* sc0p */);
          case 4:
            var _gI/* sc0y */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sbZF */,_gg/* sbZG */.h)), _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */));
            }),
            _gJ/* sc2r */ = function(_gK/* sc0A */, _gL/* sc0B */){
              var _gM/* sc0C */ = function(_gN/* sc0D */){
                return new F(function(){return A2(_gI/* sc0y */,E(_gN/* sc0D */).b, _gL/* sc0B */);});
              },
              _gO/* sc2q */ = function(_gP/* sc0H */){
                var _gQ/* sc0I */ = E(_gP/* sc0H */),
                _gR/* sc0J */ = _gQ/* sc0I */.a,
                _gS/* sc2p */ = function(_gT/* sc0L */){
                  var _gU/* sc0M */ = E(_gT/* sc0L */),
                  _gV/* sc0N */ = _gU/* sc0M */.a,
                  _gW/* sc2o */ = function(_gX/* sc0P */){
                    var _gY/* sc0Q */ = E(_gX/* sc0P */),
                    _gZ/* sc0R */ = _gY/* sc0Q */.a,
                    _h0/* sc2n */ = function(_h1/* sc0T */){
                      var _h2/* sc0U */ = E(_h1/* sc0T */),
                      _h3/* sc0V */ = _h2/* sc0U */.a,
                      _h4/* sc0X */ = new T(function(){
                        return E(_gR/* sc0J */)*E(_g7/* sbZd */)+E(_h3/* sc0V */)*E(_g8/* sbZe */);
                      }),
                      _h5/* sc19 */ = new T(function(){
                        return E(_gR/* sc0J */)*E(_g4/* sbZa */)+E(_h3/* sc0V */)*E(_g5/* sbZb */);
                      }),
                      _h6/* sc2m */ = function(_h7/* sc1l */){
                        var _h8/* sc1m */ = E(_h7/* sc1l */),
                        _h9/* sc1n */ = _h8/* sc1m */.a,
                        _ha/* sc1p */ = new T(function(){
                          return E(_gV/* sc0N */)*E(_g7/* sbZd */)+E(_h9/* sc1n */)*E(_g8/* sbZe */);
                        }),
                        _hb/* sc1B */ = new T(function(){
                          return E(_gV/* sc0N */)*E(_g4/* sbZa */)+E(_h9/* sc1n */)*E(_g5/* sbZb */);
                        }),
                        _hc/* sc2l */ = function(_hd/* sc1N */){
                          var _he/* sc1O */ = E(_hd/* sc1N */),
                          _hf/* sc1P */ = _he/* sc1O */.a;
                          return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sbZG */.g, _h5/* sc19 */, _hb/* sc1B */, new T(function(){
                            return E(_gZ/* sc0R */)*E(_g4/* sbZa */)+E(_hf/* sc1P */)*E(_g5/* sbZb */)+E(_g6/* sbZc */);
                          }), _h4/* sc0X */, _ha/* sc1p */, new T(function(){
                            return E(_gZ/* sc0R */)*E(_g7/* sbZd */)+E(_hf/* sc1P */)*E(_g8/* sbZe */)+E(_g9/* sbZf */);
                          }), _he/* sc1O */.b, _gM/* sc0C */]);});
                        };
                        return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sbZG */.f, _h8/* sc1m */.b, _hc/* sc2l */);});
                      };
                      return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sbZG */.e, _h2/* sc0U */.b, _h6/* sc2m */);});
                    };
                    return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sbZG */.d, _gY/* sc0Q */.b, _h0/* sc2n */);});
                  };
                  return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sbZG */.c, _gU/* sc0M */.b, _gW/* sc2o */);});
                };
                return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sbZG */.b, _gQ/* sc0I */.b, _gS/* sc2p */);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sbZG */.a, _gK/* sc0A */, _gO/* sc2q */);});
            };
            return E(_gJ/* sc2r */);
          case 5:
            var _hg/* sc2v */ = E(_gg/* sbZG */.a),
            _hh/* sc2y */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sbZF */,_gg/* sbZG */.c)), _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */));
            }),
            _hi/* sc2A */ = new T(function(){
              return 0*E(_g7/* sbZd */)+E(_g8/* sbZe */);
            }),
            _hj/* sc2H */ = new T(function(){
              return E(_g7/* sbZd */)+0*E(_g8/* sbZe */);
            }),
            _hk/* sc2O */ = new T(function(){
              return 0*E(_g4/* sbZa */)+E(_g5/* sbZb */);
            }),
            _hl/* sc2V */ = new T(function(){
              return E(_g4/* sbZa */)+0*E(_g5/* sbZb */);
            }),
            _hm/* sc3N */ = function(_hn/* sc32 */, _ho/* sc33 */){
              var _hp/* sc34 */ = function(_hq/* sc35 */){
                return new F(function(){return A2(_hh/* sc2y */,E(_hq/* sc35 */).b, _ho/* sc33 */);});
              },
              _hr/* sc3M */ = function(_hs/* sc39 */){
                var _ht/* sc3a */ = E(_hs/* sc39 */),
                _hu/* sc3b */ = _ht/* sc3a */.a,
                _hv/* sc3L */ = function(_hw/* sc3d */){
                  var _hx/* sc3e */ = E(_hw/* sc3d */),
                  _hy/* sc3f */ = _hx/* sc3e */.a;
                  return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sbZG */.b, _hl/* sc2V */, _hk/* sc2O */, new T(function(){
                    return E(_hu/* sc3b */)*E(_g4/* sbZa */)+E(_hy/* sc3f */)*E(_g5/* sbZb */)+E(_g6/* sbZc */);
                  }), _hj/* sc2H */, _hi/* sc2A */, new T(function(){
                    return E(_hu/* sc3b */)*E(_g7/* sbZd */)+E(_hy/* sc3f */)*E(_g8/* sbZe */)+E(_g9/* sbZf */);
                  }), _hx/* sc3e */.b, _hp/* sc34 */]);});
                };
                return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hg/* sc2v */.b, _ht/* sc3a */.b, _hv/* sc3L */);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hg/* sc2v */.a, _hn/* sc32 */, _hr/* sc3M */);});
            };
            return E(_hm/* sc3N */);
          case 6:
            var _hz/* sc3R */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sbZF */,_gg/* sbZG */.c)), _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */));
            }),
            _hA/* sc53 */ = function(_hB/* sc3T */, _hC/* sc3U */){
              var _hD/* sc3V */ = function(_hE/* sc3W */){
                return new F(function(){return A2(_hz/* sc3R */,E(_hE/* sc3W */).b, _hC/* sc3U */);});
              },
              _hF/* sc52 */ = function(_hG/* sc40 */){
                var _hH/* sc41 */ = E(_hG/* sc40 */),
                _hI/* sc42 */ = _hH/* sc41 */.a,
                _hJ/* sc44 */ = new T(function(){
                  return Math.cos/* EXTERNAL */(E(_hI/* sc42 */));
                }),
                _hK/* sc48 */ = new T(function(){
                  return Math.sin/* EXTERNAL */(E(_hI/* sc42 */));
                }),
                _hL/* sc4c */ = new T(function(){
                  return  -E(_hK/* sc48 */);
                });
                return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sbZG */.b, new T(function(){
                  return E(_hJ/* sc44 */)*E(_g4/* sbZa */)+E(_hK/* sc48 */)*E(_g5/* sbZb */);
                }), new T(function(){
                  return E(_hL/* sc4c */)*E(_g4/* sbZa */)+E(_hJ/* sc44 */)*E(_g5/* sbZb */);
                }), _ga/* sbZg */, new T(function(){
                  return E(_hJ/* sc44 */)*E(_g7/* sbZd */)+E(_hK/* sc48 */)*E(_g8/* sbZe */);
                }), new T(function(){
                  return E(_hL/* sc4c */)*E(_g7/* sbZd */)+E(_hJ/* sc44 */)*E(_g8/* sbZe */);
                }), _gb/* sbZr */, _hH/* sc41 */.b, _hD/* sc3V */]);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sbZG */.a, _hB/* sc3T */, _hF/* sc52 */);});
            };
            return E(_hA/* sc53 */);
          case 7:
            var _hM/* sc57 */ = E(_gg/* sbZG */.a),
            _hN/* sc5a */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sbZF */,_gg/* sbZG */.c)), _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */));
            }),
            _hO/* sc67 */ = function(_hP/* sc5c */, _hQ/* sc5d */){
              var _hR/* sc5e */ = function(_hS/* sc5f */){
                return new F(function(){return A2(_hN/* sc5a */,E(_hS/* sc5f */).b, _hQ/* sc5d */);});
              },
              _hT/* sc66 */ = function(_hU/* sc5j */){
                var _hV/* sc5k */ = E(_hU/* sc5j */),
                _hW/* sc5l */ = _hV/* sc5k */.a,
                _hX/* sc5n */ = new T(function(){
                  return E(_hW/* sc5l */)*E(_g7/* sbZd */)+0*E(_g8/* sbZe */);
                }),
                _hY/* sc5x */ = new T(function(){
                  return E(_hW/* sc5l */)*E(_g4/* sbZa */)+0*E(_g5/* sbZb */);
                }),
                _hZ/* sc65 */ = function(_i0/* sc5H */){
                  var _i1/* sc5I */ = E(_i0/* sc5H */),
                  _i2/* sc5J */ = _i1/* sc5I */.a;
                  return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sbZG */.b, _hY/* sc5x */, new T(function(){
                    return 0*E(_g4/* sbZa */)+E(_i2/* sc5J */)*E(_g5/* sbZb */);
                  }), _ga/* sbZg */, _hX/* sc5n */, new T(function(){
                    return 0*E(_g7/* sbZd */)+E(_i2/* sc5J */)*E(_g8/* sbZe */);
                  }), _gb/* sbZr */, _i1/* sc5I */.b, _hR/* sc5e */]);});
                };
                return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hM/* sc57 */.b, _hV/* sc5k */.b, _hZ/* sc65 */);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hM/* sc57 */.a, _hP/* sc5c */, _hT/* sc66 */);});
            };
            return E(_hO/* sc67 */);
          default:
            var _i3/* sc6b */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(_gg/* sbZG */.b, _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */));
            }),
            _i4/* sc6c */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sbZF */,_gg/* sbZG */.c)), _g4/* sbZa */, _g5/* sbZb */, _g6/* sbZc */, _g7/* sbZd */, _g8/* sbZe */, _g9/* sbZf */));
            }),
            _i5/* sc6n */ = function(_i6/* sc6e */){
              var _i7/* sc6f */ = new T(function(){
                return B(A1(_i3/* sc6b */,_i6/* sc6e */));
              }),
              _i8/* sc6m */ = function(_i9/* sc6g */){
                return new F(function(){return A1(_i7/* sc6f */,function(_ia/* sc6h */){
                  return new F(function(){return A2(_i4/* sc6c */,E(_ia/* sc6h */).b, _i9/* sc6g */);});
                });});
              };
              return E(_i8/* sc6m */);
            };
            return E(_i5/* sc6n */);
        }
      }
    })(_fV/*  sbZ9 */, _fW/*  sbZa */, _fX/*  sbZb */, _fY/*  sbZc */, _fZ/*  sbZd */, _g0/*  sbZe */, _g1/*  sbZf */));
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
_id/* $fMorphDouble_$clerp */ = function(_ie/* sbbd */, _if/* sbbe */, _ig/* sbbf */){
  var _ih/* sbbi */ = E(_ie/* sbbd */);
  return E(_if/* sbbe */)*(1-_ih/* sbbi */)+E(_ig/* sbbf */)*_ih/* sbbi */;
},
_ii/* a7 */ = function(_ij/* sbc8 */, _ik/* sbc9 */, _il/* sbca */){
  var _im/* sbcb */ = new T(function(){
    return E(E(_ij/* sbc8 */).b);
  });
  return new F(function(){return A1(_il/* sbca */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,new T(function(){
    return E(E(_ij/* sbc8 */).a);
  }),new T4(0,new T(function(){
    return E(E(_im/* sbcb */).a);
  }),new T(function(){
    return E(E(_im/* sbcb */).b);
  }),new T(function(){
    return E(E(_im/* sbcb */).c);
  }),_av/* GHC.Types.False */))),_ik/* sbc9 */));});
},
_in/* divideDouble */ = function(_io/* s18yD */, _ip/* s18yE */){
  return E(_io/* s18yD */)/E(_ip/* s18yE */);
},
_iq/* ease2 */ = 0,
_ir/* easeRegister1 */ = function(_is/* sc3w */, _it/* sc3x */, _iu/* sc3y */, _iv/* sc3z */){
  var _iw/* sc3N */ = function(_ix/* sc3B */, _iy/* sc3C */, _iz/* sc3D */){
    return new F(function(){return A1(_iz/* sc3D */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
      var _iA/* sc3E */ = E(_ix/* sc3B */);
      return new T4(0,E(new T2(1,new T2(0,_is/* sc3w */,_it/* sc3x */),_iA/* sc3E */.a)),_iA/* sc3E */.b,E(_iA/* sc3E */.c),E(_iA/* sc3E */.d));
    })),_iy/* sc3C */));});
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _iu/* sc3y */, _iw/* sc3N */, _iu/* sc3y */, _iv/* sc3z */]);});
},
_iB/* $weaseHandle */ = function(_iC/* sbcF */, _iD/* sbcG */, _iE/* sbcH */, _iF/* sbcI */, _iG/* sbcJ */, _iH/* sbcK */){
  var _iI/* sbcL */ = new T(function(){
    var _iJ/* sbcM */ = new T(function(){
      return B(A1(_iE/* sbcH */,_2E/* GHC.Base.id */));
    }),
    _iK/* sbd5 */ = function(_iL/* sbcN */, _iM/* sbcO */, _iN/* sbcP */){
      var _iO/* sbcQ */ = E(_iL/* sbcN */),
      _iP/* sbcT */ = E(_iO/* sbcQ */.b),
      _iQ/* sbd0 */ = new T(function(){
        var _iR/* sbcZ */ = new T(function(){
          return B(A1(_iJ/* sbcM */,new T(function(){
            return B(_in/* GHC.Float.divideDouble */(_iP/* sbcT */.c, _iD/* sbcG */));
          })));
        });
        return B(A3(_iC/* sbcF */,_iR/* sbcZ */, _iP/* sbcT */.a, _iP/* sbcT */.b));
      });
      return new F(function(){return A1(_iN/* sbcP */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_iO/* sbcQ */.a,new T4(0,_iQ/* sbd0 */,_iG/* sbcJ */,_iq/* Core.Ease.ease2 */,_iP/* sbcT */.d))),_iM/* sbcO */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iF/* sbcI */, _iK/* sbd5 */));
  }),
  _iS/* sbd6 */ = new T(function(){
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iF/* sbcI */, _ii/* Core.Ease.a7 */));
  }),
  _iT/* sbd7 */ = new T(function(){
    var _iU/* sbd8 */ = new T(function(){
      return B(A1(_iH/* sbcK */,_av/* GHC.Types.False */));
    }),
    _iV/* sbd9 */ = new T(function(){
      return B(A1(_iH/* sbcK */,_aw/* GHC.Types.True */));
    }),
    _iW/* sbda */ = new T(function(){
      return B(A1(_iE/* sbcH */,_2E/* GHC.Base.id */));
    }),
    _iX/* sbdX */ = function(_iY/* sbdb */, _iZ/* sbdc */, _j0/* sbdd */){
      var _j1/* sbde */ = E(_iY/* sbdb */),
      _j2/* sbdh */ = E(_j1/* sbde */.b),
      _j3/* sbdi */ = _j2/* sbdh */.a,
      _j4/* sbdj */ = _j2/* sbdh */.b;
      if(!E(_j2/* sbdh */.d)){
        var _j5/* sbdn */ = E(_iD/* sbcG */),
        _j6/* sbdr */ = E(_j2/* sbdh */.c)+1,
        _j7/* sbds */ = function(_j8/* sbdt */, _j9/* sbdu */){
          var _ja/* sbdv */ = new T(function(){
            var _jb/* sbdy */ = new T(function(){
              return B(A1(_iW/* sbda */,new T(function(){
                return _j8/* sbdt *//_j5/* sbdn */;
              })));
            });
            return B(A3(_iC/* sbcF */,_jb/* sbdy */, _j3/* sbdi */, _j4/* sbdj */));
          }),
          _jc/* sbdz */ = new T4(0,_j3/* sbdi */,_j4/* sbdj */,_j9/* sbdu */,_aw/* GHC.Types.True */);
          if(_j8/* sbdt */>=_j5/* sbdn */){
            return new F(function(){return A2(_iV/* sbd9 */,_iZ/* sbdc */, function(_jd/* sbdE */){
              return new F(function(){return A1(_j0/* sbdd */,new T2(0,new T2(0,_av/* GHC.Types.False */,new T2(0,_ja/* sbdv */,_jc/* sbdz */)),E(_jd/* sbdE */).b));});
            });});
          }else{
            return new F(function(){return A1(_j0/* sbdd */,new T2(0,new T2(0,_aw/* GHC.Types.True */,new T2(0,_ja/* sbdv */,_jc/* sbdz */)),_iZ/* sbdc */));});
          }
        };
        if(_j5/* sbdn */>_j6/* sbdr */){
          return new F(function(){return _j7/* sbds */(_j6/* sbdr */, _j6/* sbdr */);});
        }else{
          return new F(function(){return _j7/* sbds */(_j5/* sbdn */, _j5/* sbdn */);});
        }
      }else{
        return new F(function(){return A2(_iU/* sbd8 */,_iZ/* sbdc */, function(_je/* sbdR */){
          return new F(function(){return A1(_j0/* sbdd */,new T2(0,new T2(0,_av/* GHC.Types.False */,_j1/* sbde */),E(_je/* sbdR */).b));});
        });});
      }
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iF/* sbcI */, _iX/* sbdX */));
  }),
  _jf/* sbe7 */ = function(_jg/* sbdY */){
    var _jh/* sbdZ */ = new T(function(){
      return B(A1(_iI/* sbcL */,_jg/* sbdY */));
    }),
    _ji/* sbe6 */ = function(_jj/* sbe0 */){
      return new F(function(){return A1(_jh/* sbdZ */,function(_jk/* sbe1 */){
        return new F(function(){return _ir/* Core.World.Internal.easeRegister1 */(_iS/* sbd6 */, _iT/* sbd7 */, E(_jk/* sbe1 */).b, _jj/* sbe0 */);});
      });});
    };
    return E(_ji/* sbe6 */);
  };
  return E(_jf/* sbe7 */);
},
_jl/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _7/* GHC.Tuple.() */;
},
_jm/* $wa */ = function(_jn/* scjK */, _jo/* scjL */, _jp/* scjM */, _jq/* scjN */, _/* EXTERNAL */){
  var _jr/* scjP */ = function(_/* EXTERNAL */, _js/* scjR */){
    var _jt/* scjS */ = function(_/* EXTERNAL */, _ju/* scjU */){
      var _jv/* scjV */ = function(_/* EXTERNAL */, _jw/* scjX */){
        var _jx/* scjY */ = E(_jq/* scjN */);
        switch(_jx/* scjY */._){
          case 0:
            return new T(function(){
              var _jy/* sck0 */ = function(_jz/* sck1 */){
                var _jA/* sck2 */ = _jz/* sck1 */*256,
                _jB/* sck3 */ = _jA/* sck2 */&4294967295,
                _jC/* sck4 */ = function(_jD/* sck5 */){
                  var _jE/* sck8 */ = E(_ju/* scjU */)*256,
                  _jF/* sck9 */ = _jE/* sck8 */&4294967295,
                  _jG/* scka */ = function(_jH/* sckb */){
                    var _jI/* sckc */ = function(_jJ/* sckd */){
                      var _jK/* scke */ = _jJ/* sckd */*256,
                      _jL/* sckf */ = _jK/* scke */&4294967295,
                      _jM/* sckg */ = function(_jN/* sckh */){
                        var _jO/* scki */ = E(_jx/* scjY */.a);
                        return (1>_jO/* scki */) ? (0>_jO/* scki */) ? new T4(1,_jD/* sck5 */,_jH/* sckb */,_jN/* sckh */,0) : new T4(1,_jD/* sck5 */,_jH/* sckb */,_jN/* sckh */,_jO/* scki */) : new T4(1,_jD/* sck5 */,_jH/* sckb */,_jN/* sckh */,1);
                      };
                      if(_jK/* scke */>=_jL/* sckf */){
                        if(255>_jL/* sckf */){
                          if(0>_jL/* sckf */){
                            return new F(function(){return _jM/* sckg */(0);});
                          }else{
                            return new F(function(){return _jM/* sckg */(_jL/* sckf */);});
                          }
                        }else{
                          return new F(function(){return _jM/* sckg */(255);});
                        }
                      }else{
                        var _jP/* sckv */ = _jL/* sckf */-1|0;
                        if(255>_jP/* sckv */){
                          if(0>_jP/* sckv */){
                            return new F(function(){return _jM/* sckg */(0);});
                          }else{
                            return new F(function(){return _jM/* sckg */(_jP/* sckv */);});
                          }
                        }else{
                          return new F(function(){return _jM/* sckg */(255);});
                        }
                      }
                    },
                    _jQ/* sckA */ = E(_jw/* scjX */);
                    if(!_jQ/* sckA */._){
                      return new F(function(){return _jI/* sckc */(0);});
                    }else{
                      return new F(function(){return _jI/* sckc */(E(_jQ/* sckA */.a));});
                    }
                  };
                  if(_jE/* sck8 */>=_jF/* sck9 */){
                    if(255>_jF/* sck9 */){
                      if(0>_jF/* sck9 */){
                        return new F(function(){return _jG/* scka */(0);});
                      }else{
                        return new F(function(){return _jG/* scka */(_jF/* sck9 */);});
                      }
                    }else{
                      return new F(function(){return _jG/* scka */(255);});
                    }
                  }else{
                    var _jR/* sckL */ = _jF/* sck9 */-1|0;
                    if(255>_jR/* sckL */){
                      if(0>_jR/* sckL */){
                        return new F(function(){return _jG/* scka */(0);});
                      }else{
                        return new F(function(){return _jG/* scka */(_jR/* sckL */);});
                      }
                    }else{
                      return new F(function(){return _jG/* scka */(255);});
                    }
                  }
                };
                if(_jA/* sck2 */>=_jB/* sck3 */){
                  if(255>_jB/* sck3 */){
                    if(0>_jB/* sck3 */){
                      return new F(function(){return _jC/* sck4 */(0);});
                    }else{
                      return new F(function(){return _jC/* sck4 */(_jB/* sck3 */);});
                    }
                  }else{
                    return new F(function(){return _jC/* sck4 */(255);});
                  }
                }else{
                  var _jS/* sckX */ = _jB/* sck3 */-1|0;
                  if(255>_jS/* sckX */){
                    if(0>_jS/* sckX */){
                      return new F(function(){return _jC/* sck4 */(0);});
                    }else{
                      return new F(function(){return _jC/* sck4 */(_jS/* sckX */);});
                    }
                  }else{
                    return new F(function(){return _jC/* sck4 */(255);});
                  }
                }
              },
              _jT/* scl2 */ = E(_js/* scjR */);
              if(!_jT/* scl2 */._){
                return B(_jy/* sck0 */(0));
              }else{
                return B(_jy/* sck0 */(E(_jT/* scl2 */.a)));
              }
            });
          case 1:
            var _jU/* scl8 */ = B(A1(_jx/* scjY */.a,_/* EXTERNAL */)),
            _jV/* scla */ = _jU/* scl8 */;
            return new T(function(){
              var _jW/* sclb */ = function(_jX/* sclc */){
                var _jY/* scld */ = _jX/* sclc */*256,
                _jZ/* scle */ = _jY/* scld */&4294967295,
                _k0/* sclf */ = function(_k1/* sclg */){
                  var _k2/* sclj */ = E(_ju/* scjU */)*256,
                  _k3/* sclk */ = _k2/* sclj */&4294967295,
                  _k4/* scll */ = function(_k5/* sclm */){
                    var _k6/* scln */ = function(_k7/* sclo */){
                      var _k8/* sclp */ = _k7/* sclo */*256,
                      _k9/* sclq */ = _k8/* sclp */&4294967295,
                      _ka/* sclr */ = function(_kb/* scls */){
                        var _kc/* sclt */ = E(_jV/* scla */);
                        return (1>_kc/* sclt */) ? (0>_kc/* sclt */) ? new T4(1,_k1/* sclg */,_k5/* sclm */,_kb/* scls */,0) : new T4(1,_k1/* sclg */,_k5/* sclm */,_kb/* scls */,_kc/* sclt */) : new T4(1,_k1/* sclg */,_k5/* sclm */,_kb/* scls */,1);
                      };
                      if(_k8/* sclp */>=_k9/* sclq */){
                        if(255>_k9/* sclq */){
                          if(0>_k9/* sclq */){
                            return new F(function(){return _ka/* sclr */(0);});
                          }else{
                            return new F(function(){return _ka/* sclr */(_k9/* sclq */);});
                          }
                        }else{
                          return new F(function(){return _ka/* sclr */(255);});
                        }
                      }else{
                        var _kd/* sclG */ = _k9/* sclq */-1|0;
                        if(255>_kd/* sclG */){
                          if(0>_kd/* sclG */){
                            return new F(function(){return _ka/* sclr */(0);});
                          }else{
                            return new F(function(){return _ka/* sclr */(_kd/* sclG */);});
                          }
                        }else{
                          return new F(function(){return _ka/* sclr */(255);});
                        }
                      }
                    },
                    _ke/* sclL */ = E(_jw/* scjX */);
                    if(!_ke/* sclL */._){
                      return new F(function(){return _k6/* scln */(0);});
                    }else{
                      return new F(function(){return _k6/* scln */(E(_ke/* sclL */.a));});
                    }
                  };
                  if(_k2/* sclj */>=_k3/* sclk */){
                    if(255>_k3/* sclk */){
                      if(0>_k3/* sclk */){
                        return new F(function(){return _k4/* scll */(0);});
                      }else{
                        return new F(function(){return _k4/* scll */(_k3/* sclk */);});
                      }
                    }else{
                      return new F(function(){return _k4/* scll */(255);});
                    }
                  }else{
                    var _kf/* sclW */ = _k3/* sclk */-1|0;
                    if(255>_kf/* sclW */){
                      if(0>_kf/* sclW */){
                        return new F(function(){return _k4/* scll */(0);});
                      }else{
                        return new F(function(){return _k4/* scll */(_kf/* sclW */);});
                      }
                    }else{
                      return new F(function(){return _k4/* scll */(255);});
                    }
                  }
                };
                if(_jY/* scld */>=_jZ/* scle */){
                  if(255>_jZ/* scle */){
                    if(0>_jZ/* scle */){
                      return new F(function(){return _k0/* sclf */(0);});
                    }else{
                      return new F(function(){return _k0/* sclf */(_jZ/* scle */);});
                    }
                  }else{
                    return new F(function(){return _k0/* sclf */(255);});
                  }
                }else{
                  var _kg/* scm8 */ = _jZ/* scle */-1|0;
                  if(255>_kg/* scm8 */){
                    if(0>_kg/* scm8 */){
                      return new F(function(){return _k0/* sclf */(0);});
                    }else{
                      return new F(function(){return _k0/* sclf */(_kg/* scm8 */);});
                    }
                  }else{
                    return new F(function(){return _k0/* sclf */(255);});
                  }
                }
              },
              _kh/* scmd */ = E(_js/* scjR */);
              if(!_kh/* scmd */._){
                return B(_jW/* sclb */(0));
              }else{
                return B(_jW/* sclb */(E(_kh/* scmd */.a)));
              }
            });
          case 2:
            var _ki/* scmq */ = rMV/* EXTERNAL */(E(E(_jx/* scjY */.a).c)),
            _kj/* scmt */ = E(_ki/* scmq */);
            return (_kj/* scmt */._==0) ? new T(function(){
              var _kk/* scmw */ = function(_kl/* scmx */){
                var _km/* scmy */ = _kl/* scmx */*256,
                _kn/* scmz */ = _km/* scmy */&4294967295,
                _ko/* scmA */ = function(_kp/* scmB */){
                  var _kq/* scmE */ = E(_ju/* scjU */)*256,
                  _kr/* scmF */ = _kq/* scmE */&4294967295,
                  _ks/* scmG */ = function(_kt/* scmH */){
                    var _ku/* scmI */ = function(_kv/* scmJ */){
                      var _kw/* scmK */ = _kv/* scmJ */*256,
                      _kx/* scmL */ = _kw/* scmK */&4294967295,
                      _ky/* scmM */ = function(_kz/* scmN */){
                        var _kA/* scmP */ = B(A1(_jx/* scjY */.b,new T(function(){
                          return B(_fB/* Data.Tuple.fst */(_kj/* scmt */.a));
                        })));
                        return (1>_kA/* scmP */) ? (0>_kA/* scmP */) ? new T4(1,_kp/* scmB */,_kt/* scmH */,_kz/* scmN */,0) : new T4(1,_kp/* scmB */,_kt/* scmH */,_kz/* scmN */,_kA/* scmP */) : new T4(1,_kp/* scmB */,_kt/* scmH */,_kz/* scmN */,1);
                      };
                      if(_kw/* scmK */>=_kx/* scmL */){
                        if(255>_kx/* scmL */){
                          if(0>_kx/* scmL */){
                            return new F(function(){return _ky/* scmM */(0);});
                          }else{
                            return new F(function(){return _ky/* scmM */(_kx/* scmL */);});
                          }
                        }else{
                          return new F(function(){return _ky/* scmM */(255);});
                        }
                      }else{
                        var _kB/* scn2 */ = _kx/* scmL */-1|0;
                        if(255>_kB/* scn2 */){
                          if(0>_kB/* scn2 */){
                            return new F(function(){return _ky/* scmM */(0);});
                          }else{
                            return new F(function(){return _ky/* scmM */(_kB/* scn2 */);});
                          }
                        }else{
                          return new F(function(){return _ky/* scmM */(255);});
                        }
                      }
                    },
                    _kC/* scn7 */ = E(_jw/* scjX */);
                    if(!_kC/* scn7 */._){
                      return new F(function(){return _ku/* scmI */(0);});
                    }else{
                      return new F(function(){return _ku/* scmI */(E(_kC/* scn7 */.a));});
                    }
                  };
                  if(_kq/* scmE */>=_kr/* scmF */){
                    if(255>_kr/* scmF */){
                      if(0>_kr/* scmF */){
                        return new F(function(){return _ks/* scmG */(0);});
                      }else{
                        return new F(function(){return _ks/* scmG */(_kr/* scmF */);});
                      }
                    }else{
                      return new F(function(){return _ks/* scmG */(255);});
                    }
                  }else{
                    var _kD/* scni */ = _kr/* scmF */-1|0;
                    if(255>_kD/* scni */){
                      if(0>_kD/* scni */){
                        return new F(function(){return _ks/* scmG */(0);});
                      }else{
                        return new F(function(){return _ks/* scmG */(_kD/* scni */);});
                      }
                    }else{
                      return new F(function(){return _ks/* scmG */(255);});
                    }
                  }
                };
                if(_km/* scmy */>=_kn/* scmz */){
                  if(255>_kn/* scmz */){
                    if(0>_kn/* scmz */){
                      return new F(function(){return _ko/* scmA */(0);});
                    }else{
                      return new F(function(){return _ko/* scmA */(_kn/* scmz */);});
                    }
                  }else{
                    return new F(function(){return _ko/* scmA */(255);});
                  }
                }else{
                  var _kE/* scnu */ = _kn/* scmz */-1|0;
                  if(255>_kE/* scnu */){
                    if(0>_kE/* scnu */){
                      return new F(function(){return _ko/* scmA */(0);});
                    }else{
                      return new F(function(){return _ko/* scmA */(_kE/* scnu */);});
                    }
                  }else{
                    return new F(function(){return _ko/* scmA */(255);});
                  }
                }
              },
              _kF/* scnz */ = E(_js/* scjR */);
              if(!_kF/* scnz */._){
                return B(_kk/* scmw */(0));
              }else{
                return B(_kk/* scmw */(E(_kF/* scnz */.a)));
              }
            }) : new T(function(){
              var _kG/* scnF */ = function(_kH/* scnG */){
                var _kI/* scnH */ = _kH/* scnG */*256,
                _kJ/* scnI */ = _kI/* scnH */&4294967295,
                _kK/* scnJ */ = function(_kL/* scnK */){
                  var _kM/* scnN */ = E(_ju/* scjU */)*256,
                  _kN/* scnO */ = _kM/* scnN */&4294967295,
                  _kO/* scnP */ = function(_kP/* scnQ */){
                    var _kQ/* scnR */ = function(_kR/* scnS */){
                      var _kS/* scnT */ = _kR/* scnS */*256,
                      _kT/* scnU */ = _kS/* scnT */&4294967295;
                      if(_kS/* scnT */>=_kT/* scnU */){
                        return (255>_kT/* scnU */) ? (0>_kT/* scnU */) ? new T4(1,_kL/* scnK */,_kP/* scnQ */,0,1) : new T4(1,_kL/* scnK */,_kP/* scnQ */,_kT/* scnU */,1) : new T4(1,_kL/* scnK */,_kP/* scnQ */,255,1);
                      }else{
                        var _kU/* sco2 */ = _kT/* scnU */-1|0;
                        return (255>_kU/* sco2 */) ? (0>_kU/* sco2 */) ? new T4(1,_kL/* scnK */,_kP/* scnQ */,0,1) : new T4(1,_kL/* scnK */,_kP/* scnQ */,_kU/* sco2 */,1) : new T4(1,_kL/* scnK */,_kP/* scnQ */,255,1);
                      }
                    },
                    _kV/* sco7 */ = E(_jw/* scjX */);
                    if(!_kV/* sco7 */._){
                      return new F(function(){return _kQ/* scnR */(0);});
                    }else{
                      return new F(function(){return _kQ/* scnR */(E(_kV/* sco7 */.a));});
                    }
                  };
                  if(_kM/* scnN */>=_kN/* scnO */){
                    if(255>_kN/* scnO */){
                      if(0>_kN/* scnO */){
                        return new F(function(){return _kO/* scnP */(0);});
                      }else{
                        return new F(function(){return _kO/* scnP */(_kN/* scnO */);});
                      }
                    }else{
                      return new F(function(){return _kO/* scnP */(255);});
                    }
                  }else{
                    var _kW/* scoi */ = _kN/* scnO */-1|0;
                    if(255>_kW/* scoi */){
                      if(0>_kW/* scoi */){
                        return new F(function(){return _kO/* scnP */(0);});
                      }else{
                        return new F(function(){return _kO/* scnP */(_kW/* scoi */);});
                      }
                    }else{
                      return new F(function(){return _kO/* scnP */(255);});
                    }
                  }
                };
                if(_kI/* scnH */>=_kJ/* scnI */){
                  if(255>_kJ/* scnI */){
                    if(0>_kJ/* scnI */){
                      return new F(function(){return _kK/* scnJ */(0);});
                    }else{
                      return new F(function(){return _kK/* scnJ */(_kJ/* scnI */);});
                    }
                  }else{
                    return new F(function(){return _kK/* scnJ */(255);});
                  }
                }else{
                  var _kX/* scou */ = _kJ/* scnI */-1|0;
                  if(255>_kX/* scou */){
                    if(0>_kX/* scou */){
                      return new F(function(){return _kK/* scnJ */(0);});
                    }else{
                      return new F(function(){return _kK/* scnJ */(_kX/* scou */);});
                    }
                  }else{
                    return new F(function(){return _kK/* scnJ */(255);});
                  }
                }
              },
              _kY/* scoz */ = E(_js/* scjR */);
              if(!_kY/* scoz */._){
                return B(_kG/* scnF */(0));
              }else{
                return B(_kG/* scnF */(E(_kY/* scoz */.a)));
              }
            });
          default:
            var _kZ/* scoM */ = rMV/* EXTERNAL */(E(E(_jx/* scjY */.a).c)),
            _l0/* scoP */ = E(_kZ/* scoM */);
            if(!_l0/* scoP */._){
              var _l1/* scoV */ = B(A2(_jx/* scjY */.b,E(_l0/* scoP */.a).a, _/* EXTERNAL */)),
              _l2/* scoX */ = _l1/* scoV */;
              return new T(function(){
                var _l3/* scoY */ = function(_l4/* scoZ */){
                  var _l5/* scp0 */ = _l4/* scoZ */*256,
                  _l6/* scp1 */ = _l5/* scp0 */&4294967295,
                  _l7/* scp2 */ = function(_l8/* scp3 */){
                    var _l9/* scp6 */ = E(_ju/* scjU */)*256,
                    _la/* scp7 */ = _l9/* scp6 */&4294967295,
                    _lb/* scp8 */ = function(_lc/* scp9 */){
                      var _ld/* scpa */ = function(_le/* scpb */){
                        var _lf/* scpc */ = _le/* scpb */*256,
                        _lg/* scpd */ = _lf/* scpc */&4294967295,
                        _lh/* scpe */ = function(_li/* scpf */){
                          var _lj/* scpg */ = E(_l2/* scoX */);
                          return (1>_lj/* scpg */) ? (0>_lj/* scpg */) ? new T4(1,_l8/* scp3 */,_lc/* scp9 */,_li/* scpf */,0) : new T4(1,_l8/* scp3 */,_lc/* scp9 */,_li/* scpf */,_lj/* scpg */) : new T4(1,_l8/* scp3 */,_lc/* scp9 */,_li/* scpf */,1);
                        };
                        if(_lf/* scpc */>=_lg/* scpd */){
                          if(255>_lg/* scpd */){
                            if(0>_lg/* scpd */){
                              return new F(function(){return _lh/* scpe */(0);});
                            }else{
                              return new F(function(){return _lh/* scpe */(_lg/* scpd */);});
                            }
                          }else{
                            return new F(function(){return _lh/* scpe */(255);});
                          }
                        }else{
                          var _lk/* scpt */ = _lg/* scpd */-1|0;
                          if(255>_lk/* scpt */){
                            if(0>_lk/* scpt */){
                              return new F(function(){return _lh/* scpe */(0);});
                            }else{
                              return new F(function(){return _lh/* scpe */(_lk/* scpt */);});
                            }
                          }else{
                            return new F(function(){return _lh/* scpe */(255);});
                          }
                        }
                      },
                      _ll/* scpy */ = E(_jw/* scjX */);
                      if(!_ll/* scpy */._){
                        return new F(function(){return _ld/* scpa */(0);});
                      }else{
                        return new F(function(){return _ld/* scpa */(E(_ll/* scpy */.a));});
                      }
                    };
                    if(_l9/* scp6 */>=_la/* scp7 */){
                      if(255>_la/* scp7 */){
                        if(0>_la/* scp7 */){
                          return new F(function(){return _lb/* scp8 */(0);});
                        }else{
                          return new F(function(){return _lb/* scp8 */(_la/* scp7 */);});
                        }
                      }else{
                        return new F(function(){return _lb/* scp8 */(255);});
                      }
                    }else{
                      var _lm/* scpJ */ = _la/* scp7 */-1|0;
                      if(255>_lm/* scpJ */){
                        if(0>_lm/* scpJ */){
                          return new F(function(){return _lb/* scp8 */(0);});
                        }else{
                          return new F(function(){return _lb/* scp8 */(_lm/* scpJ */);});
                        }
                      }else{
                        return new F(function(){return _lb/* scp8 */(255);});
                      }
                    }
                  };
                  if(_l5/* scp0 */>=_l6/* scp1 */){
                    if(255>_l6/* scp1 */){
                      if(0>_l6/* scp1 */){
                        return new F(function(){return _l7/* scp2 */(0);});
                      }else{
                        return new F(function(){return _l7/* scp2 */(_l6/* scp1 */);});
                      }
                    }else{
                      return new F(function(){return _l7/* scp2 */(255);});
                    }
                  }else{
                    var _ln/* scpV */ = _l6/* scp1 */-1|0;
                    if(255>_ln/* scpV */){
                      if(0>_ln/* scpV */){
                        return new F(function(){return _l7/* scp2 */(0);});
                      }else{
                        return new F(function(){return _l7/* scp2 */(_ln/* scpV */);});
                      }
                    }else{
                      return new F(function(){return _l7/* scp2 */(255);});
                    }
                  }
                },
                _lo/* scq0 */ = E(_js/* scjR */);
                if(!_lo/* scq0 */._){
                  return B(_l3/* scoY */(0));
                }else{
                  return B(_l3/* scoY */(E(_lo/* scq0 */.a)));
                }
              });
            }else{
              return new T(function(){
                var _lp/* scq6 */ = function(_lq/* scq7 */){
                  var _lr/* scq8 */ = _lq/* scq7 */*256,
                  _ls/* scq9 */ = _lr/* scq8 */&4294967295,
                  _lt/* scqa */ = function(_lu/* scqb */){
                    var _lv/* scqe */ = E(_ju/* scjU */)*256,
                    _lw/* scqf */ = _lv/* scqe */&4294967295,
                    _lx/* scqg */ = function(_ly/* scqh */){
                      var _lz/* scqi */ = function(_lA/* scqj */){
                        var _lB/* scqk */ = _lA/* scqj */*256,
                        _lC/* scql */ = _lB/* scqk */&4294967295;
                        if(_lB/* scqk */>=_lC/* scql */){
                          return (255>_lC/* scql */) ? (0>_lC/* scql */) ? new T4(1,_lu/* scqb */,_ly/* scqh */,0,1) : new T4(1,_lu/* scqb */,_ly/* scqh */,_lC/* scql */,1) : new T4(1,_lu/* scqb */,_ly/* scqh */,255,1);
                        }else{
                          var _lD/* scqt */ = _lC/* scql */-1|0;
                          return (255>_lD/* scqt */) ? (0>_lD/* scqt */) ? new T4(1,_lu/* scqb */,_ly/* scqh */,0,1) : new T4(1,_lu/* scqb */,_ly/* scqh */,_lD/* scqt */,1) : new T4(1,_lu/* scqb */,_ly/* scqh */,255,1);
                        }
                      },
                      _lE/* scqy */ = E(_jw/* scjX */);
                      if(!_lE/* scqy */._){
                        return new F(function(){return _lz/* scqi */(0);});
                      }else{
                        return new F(function(){return _lz/* scqi */(E(_lE/* scqy */.a));});
                      }
                    };
                    if(_lv/* scqe */>=_lw/* scqf */){
                      if(255>_lw/* scqf */){
                        if(0>_lw/* scqf */){
                          return new F(function(){return _lx/* scqg */(0);});
                        }else{
                          return new F(function(){return _lx/* scqg */(_lw/* scqf */);});
                        }
                      }else{
                        return new F(function(){return _lx/* scqg */(255);});
                      }
                    }else{
                      var _lF/* scqJ */ = _lw/* scqf */-1|0;
                      if(255>_lF/* scqJ */){
                        if(0>_lF/* scqJ */){
                          return new F(function(){return _lx/* scqg */(0);});
                        }else{
                          return new F(function(){return _lx/* scqg */(_lF/* scqJ */);});
                        }
                      }else{
                        return new F(function(){return _lx/* scqg */(255);});
                      }
                    }
                  };
                  if(_lr/* scq8 */>=_ls/* scq9 */){
                    if(255>_ls/* scq9 */){
                      if(0>_ls/* scq9 */){
                        return new F(function(){return _lt/* scqa */(0);});
                      }else{
                        return new F(function(){return _lt/* scqa */(_ls/* scq9 */);});
                      }
                    }else{
                      return new F(function(){return _lt/* scqa */(255);});
                    }
                  }else{
                    var _lG/* scqV */ = _ls/* scq9 */-1|0;
                    if(255>_lG/* scqV */){
                      if(0>_lG/* scqV */){
                        return new F(function(){return _lt/* scqa */(0);});
                      }else{
                        return new F(function(){return _lt/* scqa */(_lG/* scqV */);});
                      }
                    }else{
                      return new F(function(){return _lt/* scqa */(255);});
                    }
                  }
                },
                _lH/* scr0 */ = E(_js/* scjR */);
                if(!_lH/* scr0 */._){
                  return B(_lp/* scq6 */(0));
                }else{
                  return B(_lp/* scq6 */(E(_lH/* scr0 */.a)));
                }
              });
            }
        }
      },
      _lI/* scr5 */ = E(_jp/* scjM */);
      switch(_lI/* scr5 */._){
        case 0:
          return new F(function(){return _jv/* scjV */(_/* EXTERNAL */, new T1(1,_lI/* scr5 */.a));});
          break;
        case 1:
          var _lJ/* scr9 */ = B(A1(_lI/* scr5 */.a,_/* EXTERNAL */));
          return new F(function(){return _jv/* scjV */(_/* EXTERNAL */, new T1(1,_lJ/* scr9 */));});
          break;
        case 2:
          var _lK/* scrl */ = rMV/* EXTERNAL */(E(E(_lI/* scr5 */.a).c)),
          _lL/* scro */ = E(_lK/* scrl */);
          if(!_lL/* scro */._){
            var _lM/* scrs */ = new T(function(){
              return B(A1(_lI/* scr5 */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_lL/* scro */.a));
              })));
            });
            return new F(function(){return _jv/* scjV */(_/* EXTERNAL */, new T1(1,_lM/* scrs */));});
          }else{
            return new F(function(){return _jv/* scjV */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _lN/* scrD */ = rMV/* EXTERNAL */(E(E(_lI/* scr5 */.a).c)),
          _lO/* scrG */ = E(_lN/* scrD */);
          if(!_lO/* scrG */._){
            var _lP/* scrM */ = B(A2(_lI/* scr5 */.b,E(_lO/* scrG */.a).a, _/* EXTERNAL */));
            return new F(function(){return _jv/* scjV */(_/* EXTERNAL */, new T1(1,_lP/* scrM */));});
          }else{
            return new F(function(){return _jv/* scjV */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _lQ/* scrR */ = function(_/* EXTERNAL */){
      var _lR/* scrT */ = function(_/* EXTERNAL */, _lS/* scrV */){
        var _lT/* scrW */ = E(_jq/* scjN */);
        switch(_lT/* scrW */._){
          case 0:
            return new T(function(){
              var _lU/* scrY */ = function(_lV/* scrZ */){
                var _lW/* scs0 */ = _lV/* scrZ */*256,
                _lX/* scs1 */ = _lW/* scs0 */&4294967295,
                _lY/* scs2 */ = function(_lZ/* scs3 */){
                  var _m0/* scs4 */ = function(_m1/* scs5 */){
                    var _m2/* scs6 */ = _m1/* scs5 */*256,
                    _m3/* scs7 */ = _m2/* scs6 */&4294967295,
                    _m4/* scs8 */ = function(_m5/* scs9 */){
                      var _m6/* scsa */ = E(_lT/* scrW */.a);
                      return (1>_m6/* scsa */) ? (0>_m6/* scsa */) ? new T4(1,_lZ/* scs3 */,0,_m5/* scs9 */,0) : new T4(1,_lZ/* scs3 */,0,_m5/* scs9 */,_m6/* scsa */) : new T4(1,_lZ/* scs3 */,0,_m5/* scs9 */,1);
                    };
                    if(_m2/* scs6 */>=_m3/* scs7 */){
                      if(255>_m3/* scs7 */){
                        if(0>_m3/* scs7 */){
                          return new F(function(){return _m4/* scs8 */(0);});
                        }else{
                          return new F(function(){return _m4/* scs8 */(_m3/* scs7 */);});
                        }
                      }else{
                        return new F(function(){return _m4/* scs8 */(255);});
                      }
                    }else{
                      var _m7/* scsn */ = _m3/* scs7 */-1|0;
                      if(255>_m7/* scsn */){
                        if(0>_m7/* scsn */){
                          return new F(function(){return _m4/* scs8 */(0);});
                        }else{
                          return new F(function(){return _m4/* scs8 */(_m7/* scsn */);});
                        }
                      }else{
                        return new F(function(){return _m4/* scs8 */(255);});
                      }
                    }
                  },
                  _m8/* scss */ = E(_lS/* scrV */);
                  if(!_m8/* scss */._){
                    return new F(function(){return _m0/* scs4 */(0);});
                  }else{
                    return new F(function(){return _m0/* scs4 */(E(_m8/* scss */.a));});
                  }
                };
                if(_lW/* scs0 */>=_lX/* scs1 */){
                  if(255>_lX/* scs1 */){
                    if(0>_lX/* scs1 */){
                      return new F(function(){return _lY/* scs2 */(0);});
                    }else{
                      return new F(function(){return _lY/* scs2 */(_lX/* scs1 */);});
                    }
                  }else{
                    return new F(function(){return _lY/* scs2 */(255);});
                  }
                }else{
                  var _m9/* scsD */ = _lX/* scs1 */-1|0;
                  if(255>_m9/* scsD */){
                    if(0>_m9/* scsD */){
                      return new F(function(){return _lY/* scs2 */(0);});
                    }else{
                      return new F(function(){return _lY/* scs2 */(_m9/* scsD */);});
                    }
                  }else{
                    return new F(function(){return _lY/* scs2 */(255);});
                  }
                }
              },
              _ma/* scsI */ = E(_js/* scjR */);
              if(!_ma/* scsI */._){
                return B(_lU/* scrY */(0));
              }else{
                return B(_lU/* scrY */(E(_ma/* scsI */.a)));
              }
            });
          case 1:
            var _mb/* scsO */ = B(A1(_lT/* scrW */.a,_/* EXTERNAL */)),
            _mc/* scsQ */ = _mb/* scsO */;
            return new T(function(){
              var _md/* scsR */ = function(_me/* scsS */){
                var _mf/* scsT */ = _me/* scsS */*256,
                _mg/* scsU */ = _mf/* scsT */&4294967295,
                _mh/* scsV */ = function(_mi/* scsW */){
                  var _mj/* scsX */ = function(_mk/* scsY */){
                    var _ml/* scsZ */ = _mk/* scsY */*256,
                    _mm/* sct0 */ = _ml/* scsZ */&4294967295,
                    _mn/* sct1 */ = function(_mo/* sct2 */){
                      var _mp/* sct3 */ = E(_mc/* scsQ */);
                      return (1>_mp/* sct3 */) ? (0>_mp/* sct3 */) ? new T4(1,_mi/* scsW */,0,_mo/* sct2 */,0) : new T4(1,_mi/* scsW */,0,_mo/* sct2 */,_mp/* sct3 */) : new T4(1,_mi/* scsW */,0,_mo/* sct2 */,1);
                    };
                    if(_ml/* scsZ */>=_mm/* sct0 */){
                      if(255>_mm/* sct0 */){
                        if(0>_mm/* sct0 */){
                          return new F(function(){return _mn/* sct1 */(0);});
                        }else{
                          return new F(function(){return _mn/* sct1 */(_mm/* sct0 */);});
                        }
                      }else{
                        return new F(function(){return _mn/* sct1 */(255);});
                      }
                    }else{
                      var _mq/* sctg */ = _mm/* sct0 */-1|0;
                      if(255>_mq/* sctg */){
                        if(0>_mq/* sctg */){
                          return new F(function(){return _mn/* sct1 */(0);});
                        }else{
                          return new F(function(){return _mn/* sct1 */(_mq/* sctg */);});
                        }
                      }else{
                        return new F(function(){return _mn/* sct1 */(255);});
                      }
                    }
                  },
                  _mr/* sctl */ = E(_lS/* scrV */);
                  if(!_mr/* sctl */._){
                    return new F(function(){return _mj/* scsX */(0);});
                  }else{
                    return new F(function(){return _mj/* scsX */(E(_mr/* sctl */.a));});
                  }
                };
                if(_mf/* scsT */>=_mg/* scsU */){
                  if(255>_mg/* scsU */){
                    if(0>_mg/* scsU */){
                      return new F(function(){return _mh/* scsV */(0);});
                    }else{
                      return new F(function(){return _mh/* scsV */(_mg/* scsU */);});
                    }
                  }else{
                    return new F(function(){return _mh/* scsV */(255);});
                  }
                }else{
                  var _ms/* sctw */ = _mg/* scsU */-1|0;
                  if(255>_ms/* sctw */){
                    if(0>_ms/* sctw */){
                      return new F(function(){return _mh/* scsV */(0);});
                    }else{
                      return new F(function(){return _mh/* scsV */(_ms/* sctw */);});
                    }
                  }else{
                    return new F(function(){return _mh/* scsV */(255);});
                  }
                }
              },
              _mt/* sctB */ = E(_js/* scjR */);
              if(!_mt/* sctB */._){
                return B(_md/* scsR */(0));
              }else{
                return B(_md/* scsR */(E(_mt/* sctB */.a)));
              }
            });
          case 2:
            var _mu/* sctO */ = rMV/* EXTERNAL */(E(E(_lT/* scrW */.a).c)),
            _mv/* sctR */ = E(_mu/* sctO */);
            return (_mv/* sctR */._==0) ? new T(function(){
              var _mw/* sctU */ = function(_mx/* sctV */){
                var _my/* sctW */ = _mx/* sctV */*256,
                _mz/* sctX */ = _my/* sctW */&4294967295,
                _mA/* sctY */ = function(_mB/* sctZ */){
                  var _mC/* scu0 */ = function(_mD/* scu1 */){
                    var _mE/* scu2 */ = _mD/* scu1 */*256,
                    _mF/* scu3 */ = _mE/* scu2 */&4294967295,
                    _mG/* scu4 */ = function(_mH/* scu5 */){
                      var _mI/* scu7 */ = B(A1(_lT/* scrW */.b,new T(function(){
                        return B(_fB/* Data.Tuple.fst */(_mv/* sctR */.a));
                      })));
                      return (1>_mI/* scu7 */) ? (0>_mI/* scu7 */) ? new T4(1,_mB/* sctZ */,0,_mH/* scu5 */,0) : new T4(1,_mB/* sctZ */,0,_mH/* scu5 */,_mI/* scu7 */) : new T4(1,_mB/* sctZ */,0,_mH/* scu5 */,1);
                    };
                    if(_mE/* scu2 */>=_mF/* scu3 */){
                      if(255>_mF/* scu3 */){
                        if(0>_mF/* scu3 */){
                          return new F(function(){return _mG/* scu4 */(0);});
                        }else{
                          return new F(function(){return _mG/* scu4 */(_mF/* scu3 */);});
                        }
                      }else{
                        return new F(function(){return _mG/* scu4 */(255);});
                      }
                    }else{
                      var _mJ/* scuk */ = _mF/* scu3 */-1|0;
                      if(255>_mJ/* scuk */){
                        if(0>_mJ/* scuk */){
                          return new F(function(){return _mG/* scu4 */(0);});
                        }else{
                          return new F(function(){return _mG/* scu4 */(_mJ/* scuk */);});
                        }
                      }else{
                        return new F(function(){return _mG/* scu4 */(255);});
                      }
                    }
                  },
                  _mK/* scup */ = E(_lS/* scrV */);
                  if(!_mK/* scup */._){
                    return new F(function(){return _mC/* scu0 */(0);});
                  }else{
                    return new F(function(){return _mC/* scu0 */(E(_mK/* scup */.a));});
                  }
                };
                if(_my/* sctW */>=_mz/* sctX */){
                  if(255>_mz/* sctX */){
                    if(0>_mz/* sctX */){
                      return new F(function(){return _mA/* sctY */(0);});
                    }else{
                      return new F(function(){return _mA/* sctY */(_mz/* sctX */);});
                    }
                  }else{
                    return new F(function(){return _mA/* sctY */(255);});
                  }
                }else{
                  var _mL/* scuA */ = _mz/* sctX */-1|0;
                  if(255>_mL/* scuA */){
                    if(0>_mL/* scuA */){
                      return new F(function(){return _mA/* sctY */(0);});
                    }else{
                      return new F(function(){return _mA/* sctY */(_mL/* scuA */);});
                    }
                  }else{
                    return new F(function(){return _mA/* sctY */(255);});
                  }
                }
              },
              _mM/* scuF */ = E(_js/* scjR */);
              if(!_mM/* scuF */._){
                return B(_mw/* sctU */(0));
              }else{
                return B(_mw/* sctU */(E(_mM/* scuF */.a)));
              }
            }) : new T(function(){
              var _mN/* scuL */ = function(_mO/* scuM */){
                var _mP/* scuN */ = _mO/* scuM */*256,
                _mQ/* scuO */ = _mP/* scuN */&4294967295,
                _mR/* scuP */ = function(_mS/* scuQ */){
                  var _mT/* scuR */ = function(_mU/* scuS */){
                    var _mV/* scuT */ = _mU/* scuS */*256,
                    _mW/* scuU */ = _mV/* scuT */&4294967295;
                    if(_mV/* scuT */>=_mW/* scuU */){
                      return (255>_mW/* scuU */) ? (0>_mW/* scuU */) ? new T4(1,_mS/* scuQ */,0,0,1) : new T4(1,_mS/* scuQ */,0,_mW/* scuU */,1) : new T4(1,_mS/* scuQ */,0,255,1);
                    }else{
                      var _mX/* scv2 */ = _mW/* scuU */-1|0;
                      return (255>_mX/* scv2 */) ? (0>_mX/* scv2 */) ? new T4(1,_mS/* scuQ */,0,0,1) : new T4(1,_mS/* scuQ */,0,_mX/* scv2 */,1) : new T4(1,_mS/* scuQ */,0,255,1);
                    }
                  },
                  _mY/* scv7 */ = E(_lS/* scrV */);
                  if(!_mY/* scv7 */._){
                    return new F(function(){return _mT/* scuR */(0);});
                  }else{
                    return new F(function(){return _mT/* scuR */(E(_mY/* scv7 */.a));});
                  }
                };
                if(_mP/* scuN */>=_mQ/* scuO */){
                  if(255>_mQ/* scuO */){
                    if(0>_mQ/* scuO */){
                      return new F(function(){return _mR/* scuP */(0);});
                    }else{
                      return new F(function(){return _mR/* scuP */(_mQ/* scuO */);});
                    }
                  }else{
                    return new F(function(){return _mR/* scuP */(255);});
                  }
                }else{
                  var _mZ/* scvi */ = _mQ/* scuO */-1|0;
                  if(255>_mZ/* scvi */){
                    if(0>_mZ/* scvi */){
                      return new F(function(){return _mR/* scuP */(0);});
                    }else{
                      return new F(function(){return _mR/* scuP */(_mZ/* scvi */);});
                    }
                  }else{
                    return new F(function(){return _mR/* scuP */(255);});
                  }
                }
              },
              _n0/* scvn */ = E(_js/* scjR */);
              if(!_n0/* scvn */._){
                return B(_mN/* scuL */(0));
              }else{
                return B(_mN/* scuL */(E(_n0/* scvn */.a)));
              }
            });
          default:
            var _n1/* scvA */ = rMV/* EXTERNAL */(E(E(_lT/* scrW */.a).c)),
            _n2/* scvD */ = E(_n1/* scvA */);
            if(!_n2/* scvD */._){
              var _n3/* scvJ */ = B(A2(_lT/* scrW */.b,E(_n2/* scvD */.a).a, _/* EXTERNAL */)),
              _n4/* scvL */ = _n3/* scvJ */;
              return new T(function(){
                var _n5/* scvM */ = function(_n6/* scvN */){
                  var _n7/* scvO */ = _n6/* scvN */*256,
                  _n8/* scvP */ = _n7/* scvO */&4294967295,
                  _n9/* scvQ */ = function(_na/* scvR */){
                    var _nb/* scvS */ = function(_nc/* scvT */){
                      var _nd/* scvU */ = _nc/* scvT */*256,
                      _ne/* scvV */ = _nd/* scvU */&4294967295,
                      _nf/* scvW */ = function(_ng/* scvX */){
                        var _nh/* scvY */ = E(_n4/* scvL */);
                        return (1>_nh/* scvY */) ? (0>_nh/* scvY */) ? new T4(1,_na/* scvR */,0,_ng/* scvX */,0) : new T4(1,_na/* scvR */,0,_ng/* scvX */,_nh/* scvY */) : new T4(1,_na/* scvR */,0,_ng/* scvX */,1);
                      };
                      if(_nd/* scvU */>=_ne/* scvV */){
                        if(255>_ne/* scvV */){
                          if(0>_ne/* scvV */){
                            return new F(function(){return _nf/* scvW */(0);});
                          }else{
                            return new F(function(){return _nf/* scvW */(_ne/* scvV */);});
                          }
                        }else{
                          return new F(function(){return _nf/* scvW */(255);});
                        }
                      }else{
                        var _ni/* scwb */ = _ne/* scvV */-1|0;
                        if(255>_ni/* scwb */){
                          if(0>_ni/* scwb */){
                            return new F(function(){return _nf/* scvW */(0);});
                          }else{
                            return new F(function(){return _nf/* scvW */(_ni/* scwb */);});
                          }
                        }else{
                          return new F(function(){return _nf/* scvW */(255);});
                        }
                      }
                    },
                    _nj/* scwg */ = E(_lS/* scrV */);
                    if(!_nj/* scwg */._){
                      return new F(function(){return _nb/* scvS */(0);});
                    }else{
                      return new F(function(){return _nb/* scvS */(E(_nj/* scwg */.a));});
                    }
                  };
                  if(_n7/* scvO */>=_n8/* scvP */){
                    if(255>_n8/* scvP */){
                      if(0>_n8/* scvP */){
                        return new F(function(){return _n9/* scvQ */(0);});
                      }else{
                        return new F(function(){return _n9/* scvQ */(_n8/* scvP */);});
                      }
                    }else{
                      return new F(function(){return _n9/* scvQ */(255);});
                    }
                  }else{
                    var _nk/* scwr */ = _n8/* scvP */-1|0;
                    if(255>_nk/* scwr */){
                      if(0>_nk/* scwr */){
                        return new F(function(){return _n9/* scvQ */(0);});
                      }else{
                        return new F(function(){return _n9/* scvQ */(_nk/* scwr */);});
                      }
                    }else{
                      return new F(function(){return _n9/* scvQ */(255);});
                    }
                  }
                },
                _nl/* scww */ = E(_js/* scjR */);
                if(!_nl/* scww */._){
                  return B(_n5/* scvM */(0));
                }else{
                  return B(_n5/* scvM */(E(_nl/* scww */.a)));
                }
              });
            }else{
              return new T(function(){
                var _nm/* scwC */ = function(_nn/* scwD */){
                  var _no/* scwE */ = _nn/* scwD */*256,
                  _np/* scwF */ = _no/* scwE */&4294967295,
                  _nq/* scwG */ = function(_nr/* scwH */){
                    var _ns/* scwI */ = function(_nt/* scwJ */){
                      var _nu/* scwK */ = _nt/* scwJ */*256,
                      _nv/* scwL */ = _nu/* scwK */&4294967295;
                      if(_nu/* scwK */>=_nv/* scwL */){
                        return (255>_nv/* scwL */) ? (0>_nv/* scwL */) ? new T4(1,_nr/* scwH */,0,0,1) : new T4(1,_nr/* scwH */,0,_nv/* scwL */,1) : new T4(1,_nr/* scwH */,0,255,1);
                      }else{
                        var _nw/* scwT */ = _nv/* scwL */-1|0;
                        return (255>_nw/* scwT */) ? (0>_nw/* scwT */) ? new T4(1,_nr/* scwH */,0,0,1) : new T4(1,_nr/* scwH */,0,_nw/* scwT */,1) : new T4(1,_nr/* scwH */,0,255,1);
                      }
                    },
                    _nx/* scwY */ = E(_lS/* scrV */);
                    if(!_nx/* scwY */._){
                      return new F(function(){return _ns/* scwI */(0);});
                    }else{
                      return new F(function(){return _ns/* scwI */(E(_nx/* scwY */.a));});
                    }
                  };
                  if(_no/* scwE */>=_np/* scwF */){
                    if(255>_np/* scwF */){
                      if(0>_np/* scwF */){
                        return new F(function(){return _nq/* scwG */(0);});
                      }else{
                        return new F(function(){return _nq/* scwG */(_np/* scwF */);});
                      }
                    }else{
                      return new F(function(){return _nq/* scwG */(255);});
                    }
                  }else{
                    var _ny/* scx9 */ = _np/* scwF */-1|0;
                    if(255>_ny/* scx9 */){
                      if(0>_ny/* scx9 */){
                        return new F(function(){return _nq/* scwG */(0);});
                      }else{
                        return new F(function(){return _nq/* scwG */(_ny/* scx9 */);});
                      }
                    }else{
                      return new F(function(){return _nq/* scwG */(255);});
                    }
                  }
                },
                _nz/* scxe */ = E(_js/* scjR */);
                if(!_nz/* scxe */._){
                  return B(_nm/* scwC */(0));
                }else{
                  return B(_nm/* scwC */(E(_nz/* scxe */.a)));
                }
              });
            }
        }
      },
      _nA/* scxj */ = E(_jp/* scjM */);
      switch(_nA/* scxj */._){
        case 0:
          return new F(function(){return _lR/* scrT */(_/* EXTERNAL */, new T1(1,_nA/* scxj */.a));});
          break;
        case 1:
          var _nB/* scxn */ = B(A1(_nA/* scxj */.a,_/* EXTERNAL */));
          return new F(function(){return _lR/* scrT */(_/* EXTERNAL */, new T1(1,_nB/* scxn */));});
          break;
        case 2:
          var _nC/* scxz */ = rMV/* EXTERNAL */(E(E(_nA/* scxj */.a).c)),
          _nD/* scxC */ = E(_nC/* scxz */);
          if(!_nD/* scxC */._){
            var _nE/* scxG */ = new T(function(){
              return B(A1(_nA/* scxj */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_nD/* scxC */.a));
              })));
            });
            return new F(function(){return _lR/* scrT */(_/* EXTERNAL */, new T1(1,_nE/* scxG */));});
          }else{
            return new F(function(){return _lR/* scrT */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _nF/* scxR */ = rMV/* EXTERNAL */(E(E(_nA/* scxj */.a).c)),
          _nG/* scxU */ = E(_nF/* scxR */);
          if(!_nG/* scxU */._){
            var _nH/* scy0 */ = B(A2(_nA/* scxj */.b,E(_nG/* scxU */.a).a, _/* EXTERNAL */));
            return new F(function(){return _lR/* scrT */(_/* EXTERNAL */, new T1(1,_nH/* scy0 */));});
          }else{
            return new F(function(){return _lR/* scrT */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _nI/* scy5 */ = E(_jo/* scjL */);
    switch(_nI/* scy5 */._){
      case 0:
        return new F(function(){return _jt/* scjS */(_/* EXTERNAL */, _nI/* scy5 */.a);});
        break;
      case 1:
        var _nJ/* scy8 */ = B(A1(_nI/* scy5 */.a,_/* EXTERNAL */));
        return new F(function(){return _jt/* scjS */(_/* EXTERNAL */, _nJ/* scy8 */);});
        break;
      case 2:
        var _nK/* scyj */ = rMV/* EXTERNAL */(E(E(_nI/* scy5 */.a).c)),
        _nL/* scym */ = E(_nK/* scyj */);
        if(!_nL/* scym */._){
          var _nM/* scyt */ = new T(function(){
            return B(A1(_nI/* scy5 */.b,new T(function(){
              return E(E(_nL/* scym */.a).a);
            })));
          });
          return new F(function(){return _jt/* scjS */(_/* EXTERNAL */, _nM/* scyt */);});
        }else{
          return new F(function(){return _lQ/* scrR */(_/* EXTERNAL */);});
        }
        break;
      default:
        var _nN/* scyD */ = rMV/* EXTERNAL */(E(E(_nI/* scy5 */.a).c)),
        _nO/* scyG */ = E(_nN/* scyD */);
        if(!_nO/* scyG */._){
          var _nP/* scyM */ = B(A2(_nI/* scy5 */.b,E(_nO/* scyG */.a).a, _/* EXTERNAL */));
          return new F(function(){return _jt/* scjS */(_/* EXTERNAL */, _nP/* scyM */);});
        }else{
          return new F(function(){return _lQ/* scrR */(_/* EXTERNAL */);});
        }
    }
  },
  _nQ/* scyQ */ = E(_jn/* scjK */);
  switch(_nQ/* scyQ */._){
    case 0:
      return new F(function(){return _jr/* scjP */(_/* EXTERNAL */, new T1(1,_nQ/* scyQ */.a));});
      break;
    case 1:
      var _nR/* scyU */ = B(A1(_nQ/* scyQ */.a,_/* EXTERNAL */));
      return new F(function(){return _jr/* scjP */(_/* EXTERNAL */, new T1(1,_nR/* scyU */));});
      break;
    case 2:
      var _nS/* scz6 */ = rMV/* EXTERNAL */(E(E(_nQ/* scyQ */.a).c)),
      _nT/* scz9 */ = E(_nS/* scz6 */);
      if(!_nT/* scz9 */._){
        var _nU/* sczd */ = new T(function(){
          return B(A1(_nQ/* scyQ */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_nT/* scz9 */.a));
          })));
        });
        return new F(function(){return _jr/* scjP */(_/* EXTERNAL */, new T1(1,_nU/* sczd */));});
      }else{
        return new F(function(){return _jr/* scjP */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
      }
      break;
    default:
      var _nV/* sczo */ = rMV/* EXTERNAL */(E(E(_nQ/* scyQ */.a).c)),
      _nW/* sczr */ = E(_nV/* sczo */);
      if(!_nW/* sczr */._){
        var _nX/* sczx */ = B(A2(_nQ/* scyQ */.b,E(_nW/* sczr */.a).a, _/* EXTERNAL */));
        return new F(function(){return _jr/* scjP */(_/* EXTERNAL */, new T1(1,_nX/* sczx */));});
      }else{
        return new F(function(){return _jr/* scjP */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
      }
  }
},
_nY/* lvl1 */ = new T(function(){
  return toJSStr/* EXTERNAL */(_6/* GHC.Types.[] */);
}),
_nZ/* lvl2 */ = "rgb(",
_o0/* lvl3 */ = ",",
_o1/* lvl5 */ = "rgba(",
_o2/* lvl4 */ = ")",
_o3/* lvl6 */ = new T2(1,_o2/* Core.Render.Internal.lvl4 */,_6/* GHC.Types.[] */),
_o4/* $wcolor2JSString */ = function(_o5/* sbXi */){
  var _o6/* sbXj */ = E(_o5/* sbXi */);
  if(!_o6/* sbXj */._){
    var _o7/* sbXS */ = jsCat/* EXTERNAL */(new T2(1,_nZ/* Core.Render.Internal.lvl2 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sbXj */.a);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sbXj */.b);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sbXj */.c);
    }),_o3/* Core.Render.Internal.lvl6 */)))))), E(_nY/* Core.Render.Internal.lvl1 */));
    return E(_o7/* sbXS */);
  }else{
    var _o8/* sbYB */ = jsCat/* EXTERNAL */(new T2(1,_o1/* Core.Render.Internal.lvl5 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sbXj */.a);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sbXj */.b);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sbXj */.c);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sbXj */.d);
    }),_o3/* Core.Render.Internal.lvl6 */)))))))), E(_nY/* Core.Render.Internal.lvl1 */));
    return E(_o8/* sbYB */);
  }
},
_o9/* $w$c<*> */ = function(_oa/* s1DM */, _ob/* s1DN */){
  var _oc/* s1DO */ = E(_oa/* s1DM */),
  _od/* s1E2 */ = function(_oe/* s1DR */){
    var _of/* s1DS */ = E(_ob/* s1DN */),
    _og/* s1DZ */ = function(_oh/* s1DV */){
      return new T2(0,E(new T1(0,new T(function(){
        return B(A1(_oe/* s1DR */,_oh/* s1DV */));
      }))),E(new T1(0,_/* EXTERNAL */)));
    };
    return new T2(0,E(_of/* s1DS */.a),E(new T2(2,_of/* s1DS */.b,new T1(1,_og/* s1DZ */))));
  };
  return new T2(0,E(_oc/* s1DO */.a),E(new T2(2,_oc/* s1DO */.b,new T1(1,_od/* s1E2 */))));
},
_oi/* <$ */ = function(_oj/* s35r */){
  return E(E(_oj/* s35r */).b);
},
_ok/* $fApplicativeSkeleton_$c*> */ = function(_ol/* s1E9 */, _om/* s1Ea */, _on/* s1Eb */){
  return new F(function(){return _o9/* Control.Monad.Skeleton.$w$c<*> */(B(A3(_oi/* GHC.Base.<$ */,_ol/* s1E9 */, _2E/* GHC.Base.id */, _om/* s1Ea */)), _on/* s1Eb */);});
},
_oo/* const */ = function(_op/* s3aC */, _oq/* s3aD */){
  return E(_op/* s3aC */);
},
_or/* fmap */ = function(_os/* s35n */){
  return E(E(_os/* s35n */).a);
},
_ot/* $fApplicativeSkeleton_$c<* */ = function(_ou/* s1E5 */, _ov/* s1E6 */, _ow/* s1E7 */){
  return new F(function(){return _o9/* Control.Monad.Skeleton.$w$c<*> */(B(A3(_or/* GHC.Base.fmap */,_ou/* s1E5 */, _oo/* GHC.Base.const */, _ov/* s1E6 */)), _ow/* s1E7 */);});
},
_ox/* a1 */ = function(_oy/* s1Dn */, _oz/* s1Do */){
  return new T2(0,E(new T1(0,_oz/* s1Do */)),E(new T1(0,_/* EXTERNAL */)));
},
_oA/* $fApplicativeSkeleton_$creturn */ = function(_oB/* B2 */, _oC/* B1 */){
  return new F(function(){return _ox/* Control.Monad.Skeleton.a1 */(_oB/* B2 */, _oC/* B1 */);});
},
_oD/* lvl1 */ = new T(function(){
  return B(_bo/* Control.Exception.Base.absentError */("w_s1yq Functor (Skeleton t)"));
}),
_oE/* lvl3 */ = new T(function(){
  return B(_oF/* Control.Monad.Skeleton.$fApplicativeSkeleton */(_oD/* Control.Monad.Skeleton.lvl1 */));
}),
_oG/* lvl4 */ = function(_oC/* B1 */){
  return new F(function(){return _oA/* Control.Monad.Skeleton.$fApplicativeSkeleton_$creturn */(_oE/* Control.Monad.Skeleton.lvl3 */, _oC/* B1 */);});
},
_oH/* $w$cpure */ = function(_oI/* s1Ek */, _oC/* B1 */){
  return new F(function(){return _oG/* Control.Monad.Skeleton.lvl4 */(_oC/* B1 */);});
},
_oJ/* lvl2 */ = function(_oC/* B1 */){
  return new F(function(){return _oH/* Control.Monad.Skeleton.$w$cpure */(_/* EXTERNAL */, _oC/* B1 */);});
},
_oF/* $fApplicativeSkeleton */ = function(_oK/* s1Eh */){
  return new T5(0,_oK/* s1Eh */,_oJ/* Control.Monad.Skeleton.lvl2 */,_o9/* Control.Monad.Skeleton.$w$c<*> */,function(_oB/* B2 */, _oC/* B1 */){
    return new F(function(){return _ok/* Control.Monad.Skeleton.$fApplicativeSkeleton_$c*> */(_oK/* s1Eh */, _oB/* B2 */, _oC/* B1 */);});
  },function(_oB/* B2 */, _oC/* B1 */){
    return new F(function(){return _ot/* Control.Monad.Skeleton.$fApplicativeSkeleton_$c<* */(_oK/* s1Eh */, _oB/* B2 */, _oC/* B1 */);});
  });
},
_oL/* $fMonadSkeleton_$c>> */ = function(_oM/* s1DC */, _oN/* s1DD */, _oO/* s1DE */){
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,B(_oP/* Control.Monad.Skeleton.$fMonadSkeleton */(_oM/* s1DC */)), _oN/* s1DD */, function(_oQ/* s1DG */){
    return E(_oO/* s1DE */);
  });});
},
_oR/* $fMonadSkeleton_$c>>= */ = function(_oS/* s1Dr */, _oT/* s1Ds */, _oU/* s1Dt */){
  var _oV/* s1Du */ = E(_oT/* s1Ds */);
  return new T2(0,E(_oV/* s1Du */.a),E(new T2(2,_oV/* s1Du */.b,new T1(1,_oU/* s1Dt */))));
},
_oW/* lvl */ = function(_oX/* s1DB */){
  return new F(function(){return err/* EXTERNAL */(_oX/* s1DB */);});
},
_oP/* $fMonadSkeleton */ = function(_oY/* s1DI */){
  return new T5(0,_oY/* s1DI */,function(_oB/* B2 */, _oC/* B1 */){
    return new F(function(){return _oR/* Control.Monad.Skeleton.$fMonadSkeleton_$c>>= */(_oY/* s1DI */, _oB/* B2 */, _oC/* B1 */);});
  },function(_oB/* B2 */, _oC/* B1 */){
    return new F(function(){return _oL/* Control.Monad.Skeleton.$fMonadSkeleton_$c>> */(_oY/* s1DI */, _oB/* B2 */, _oC/* B1 */);});
  },function(_oC/* B1 */){
    return new F(function(){return _oA/* Control.Monad.Skeleton.$fApplicativeSkeleton_$creturn */(_oY/* s1DI */, _oC/* B1 */);});
  },_oW/* Control.Monad.Skeleton.lvl */);
},
_oZ/* $dMonad */ = new T(function(){
  return B(_oP/* Control.Monad.Skeleton.$fMonadSkeleton */(_p0/* Control.Monad.Skeleton.$dApplicative */));
}),
_p1/* liftM */ = function(_p2/* s3mK */, _p3/* s3mL */, _p4/* s3mM */){
  var _p5/* s3mP */ = function(_p6/* s3mN */){
    return new F(function(){return A2(_6T/* GHC.Base.return */,_p2/* s3mK */, new T(function(){
      return B(A1(_p3/* s3mL */,_p6/* s3mN */));
    }));});
  };
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_p2/* s3mK */, _p4/* s3mM */, _p5/* s3mP */);});
},
_p7/* $fFunctorSkeleton_$cfmap */ = function(_oB/* B2 */, _oC/* B1 */){
  return new F(function(){return _p1/* GHC.Base.liftM */(_oZ/* Control.Monad.Skeleton.$dMonad */, _oB/* B2 */, _oC/* B1 */);});
},
_p8/* $fFunctorSkeleton_$c<$ */ = function(_p9/* s1El */, _pa/* s1Em */){
  return new F(function(){return _p7/* Control.Monad.Skeleton.$fFunctorSkeleton_$cfmap */(function(_pb/* s1En */){
    return E(_p9/* s1El */);
  }, _pa/* s1Em */);});
},
_pc/* $fFunctorSkeleton */ = new T(function(){
  return new T2(0,_p7/* Control.Monad.Skeleton.$fFunctorSkeleton_$cfmap */,_p8/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */);
}),
_p0/* $dApplicative */ = new T(function(){
  return B(_oF/* Control.Monad.Skeleton.$fApplicativeSkeleton */(_pc/* Control.Monad.Skeleton.$fFunctorSkeleton */));
}),
_pd/* lvl5 */ = function(_oC/* B1 */){
  return new F(function(){return _oA/* Control.Monad.Skeleton.$fApplicativeSkeleton_$creturn */(_p0/* Control.Monad.Skeleton.$dApplicative */, _oC/* B1 */);});
},
_pe/* a2 */ = function(_pf/* s1Ep */){
  return new T2(0,E(new T2(1,_pf/* s1Ep */,_pd/* Control.Monad.Skeleton.lvl5 */)),E(new T1(0,_/* EXTERNAL */)));
},
_pg/* bone */ = function(_oC/* B1 */){
  return new F(function(){return _pe/* Control.Monad.Skeleton.a2 */(_oC/* B1 */);});
},
_ph/* clip_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.restore();})");
}),
_pi/* clip5 */ = function(_pj/* scaU */, _/* EXTERNAL */){
  var _pk/* scb1 */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), E(_pj/* scaU */));
  return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_pl/* clip4 */ = new T2(0,_pi/* Core.Render.Internal.clip5 */,_7/* GHC.Tuple.() */),
_pm/* clip3 */ = new T(function(){
  return B(_pg/* Control.Monad.Skeleton.bone */(_pl/* Core.Render.Internal.clip4 */));
}),
_pn/* clip2 */ = function(_po/* scb4 */){
  return E(_pm/* Core.Render.Internal.clip3 */);
},
_pp/* clip1 */ = new T1(1,_pn/* Core.Render.Internal.clip2 */),
_pq/* clip_f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.beginPath();})");
}),
_pr/* clip_f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.save();})");
}),
_ps/* getImage2 */ = function(_pt/* sbTz */, _pu/* sbTA */, _/* EXTERNAL */){
  var _pv/* sbTC */ = E(_pt/* sbTz */);
  switch(_pv/* sbTC */._){
    case 0:
      return new F(function(){return A2(_pu/* sbTA */,_pv/* sbTC */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _pw/* sbTF */ = B(A1(_pv/* sbTC */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_pu/* sbTA */,_pw/* sbTF */, _/* EXTERNAL */);});
      break;
    case 2:
      var _px/* sbTQ */ = rMV/* EXTERNAL */(E(E(_pv/* sbTC */.a).c)),
      _py/* sbTT */ = E(_px/* sbTQ */);
      if(!_py/* sbTT */._){
        var _pz/* sbTX */ = new T(function(){
          return B(A1(_pv/* sbTC */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_py/* sbTT */.a));
          })));
        });
        return new F(function(){return A2(_pu/* sbTA */,_pz/* sbTX */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _pA/* sbU7 */ = rMV/* EXTERNAL */(E(E(_pv/* sbTC */.a).c)),
      _pB/* sbUa */ = E(_pA/* sbU7 */);
      if(!_pB/* sbUa */._){
        var _pC/* sbUg */ = B(A2(_pv/* sbTC */.b,E(_pB/* sbUa */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_pu/* sbTA */,_pC/* sbUg */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
  }
},
_pD/* lvl10 */ = "shadowBlur",
_pE/* lvl7 */ = "shadowColor",
_pF/* lvl8 */ = "shadowOffsetX",
_pG/* lvl9 */ = "shadowOffsetY",
_pH/* $wshadowed */ = function(_pI/* scAB */, _pJ/* scAC */, _pK/* scAD */, _pL/* scAE */, _pM/* scAF */){
  var _pN/* scBW */ = function(_pO/* scAG */, _/* EXTERNAL */){
    var _pP/* scBV */ = function(_pQ/* scAI */, _/* EXTERNAL */){
      var _pR/* scBU */ = function(_pS/* scAK */, _/* EXTERNAL */){
        return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_pK/* scAD */, function(_pT/* scAM */, _/* EXTERNAL */){
          var _pU/* scAO */ = E(_pL/* scAE */),
          _pV/* scAT */ = B(_jm/* Core.Render.Internal.$wa */(_pU/* scAO */.a, _pU/* scAO */.b, _pU/* scAO */.c, _pU/* scAO */.d, _/* EXTERNAL */)),
          _pW/* scAW */ = E(_pO/* scAG */),
          _pX/* scB1 */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _pW/* scAW */),
          _pY/* scB7 */ = E(_ic/* Haste.DOM.Core.jsSet_f1 */),
          _pZ/* scBa */ = __app3/* EXTERNAL */(_pY/* scB7 */, _pW/* scAW */, E(_pE/* Core.Render.Internal.lvl7 */), B(_o4/* Core.Render.Internal.$wcolor2JSString */(_pV/* scAT */))),
          _q0/* scBi */ = String/* EXTERNAL */(E(_pQ/* scAI */)),
          _q1/* scBm */ = __app3/* EXTERNAL */(_pY/* scB7 */, _pW/* scAW */, E(_pF/* Core.Render.Internal.lvl8 */), _q0/* scBi */),
          _q2/* scBu */ = String/* EXTERNAL */(E(_pS/* scAK */)),
          _q3/* scBy */ = __app3/* EXTERNAL */(_pY/* scB7 */, _pW/* scAW */, E(_pG/* Core.Render.Internal.lvl9 */), _q2/* scBu */),
          _q4/* scBG */ = String/* EXTERNAL */(E(_pT/* scAM */)),
          _q5/* scBK */ = __app3/* EXTERNAL */(_pY/* scB7 */, _pW/* scAW */, E(_pD/* Core.Render.Internal.lvl10 */), _q4/* scBG */),
          _q6/* scBQ */ = __app1/* EXTERNAL */(E(_pq/* Core.Render.Internal.clip_f3 */), _pW/* scAW */);
          return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _/* EXTERNAL */);});
      };
      return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_pJ/* scAC */, _pR/* scBU */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_pI/* scAB */, _pP/* scBV */, _/* EXTERNAL */);});
  },
  _q7/* scBY */ = B(_pg/* Control.Monad.Skeleton.bone */(new T2(0,_pN/* scBW */,_7/* GHC.Tuple.() */)));
  return new T2(0,E(_q7/* scBY */.a),E(new T2(2,new T2(2,_q7/* scBY */.b,new T1(1,function(_q8/* scC1 */){
    return E(_pM/* scAF */);
  })),_pp/* Core.Render.Internal.clip1 */)));
},
_q9/* $fAffineShape2 */ = function(_qa/* sjFg */, _qb/* sjFh */, _qc/* sjFi */, _qd/* sjFj */, _/* EXTERNAL */){
  var _qe/* sjFl */ = E(_qa/* sjFg */);
  switch(_qe/* sjFl */._){
    case 0:
      return new F(function(){return A(_qb/* sjFh */,[_qe/* sjFl */.a, _qc/* sjFi */, _qd/* sjFj */, _/* EXTERNAL */]);});
      break;
    case 1:
      var _qf/* sjFo */ = B(A1(_qe/* sjFl */.a,_/* EXTERNAL */));
      return new F(function(){return A(_qb/* sjFh */,[_qf/* sjFo */, _qc/* sjFi */, _qd/* sjFj */, _/* EXTERNAL */]);});
      break;
    case 2:
      var _qg/* sjFz */ = rMV/* EXTERNAL */(E(E(_qe/* sjFl */.a).c)),
      _qh/* sjFC */ = E(_qg/* sjFz */);
      if(!_qh/* sjFC */._){
        var _qi/* sjFG */ = new T(function(){
          return B(A1(_qe/* sjFl */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_qh/* sjFC */.a));
          })));
        });
        return new F(function(){return A(_qb/* sjFh */,[_qi/* sjFG */, _qc/* sjFi */, _qd/* sjFj */, _/* EXTERNAL */]);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _qj/* sjFQ */ = rMV/* EXTERNAL */(E(E(_qe/* sjFl */.a).c)),
      _qk/* sjFT */ = E(_qj/* sjFQ */);
      if(!_qk/* sjFT */._){
        var _ql/* sjFZ */ = B(A2(_qe/* sjFl */.b,E(_qk/* sjFT */.a).a, _/* EXTERNAL */));
        return new F(function(){return A(_qb/* sjFh */,[_ql/* sjFZ */, _qc/* sjFi */, _qd/* sjFj */, _/* EXTERNAL */]);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
  }
},
_qm/* $fAffineShape_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,_){ctx.restore();})");
}),
_qn/* $fApplicativeShape4 */ = function(_/* EXTERNAL */){
  return _av/* GHC.Types.False */;
},
_qo/* $fApplicativeShape3 */ = function(_qp/* sjDq */, _/* EXTERNAL */){
  return new F(function(){return _qn/* Core.Shape.Internal.$fApplicativeShape4 */(_/* EXTERNAL */);});
},
_qq/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,_){ctx.save();})");
}),
_qr/* f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.scale(x,y);})");
}),
_qs/* f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(str,x,y,ctx,_){ctx.strokeText(str,x,y);})");
}),
_qt/* f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(str,x,y,ctx,_){ctx.fillText(str,x,y);})");
}),
_qu/* f5 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.translate(x,y);})");
}),
_qv/* lvl */ = "alphabetic",
_qw/* lvl1 */ = "middle",
_qx/* lvl2 */ = "hanging",
_qy/* lvl3 */ = "right",
_qz/* lvl4 */ = "center",
_qA/* lvl5 */ = "left",
_qB/* lvl6 */ = "(function(fn,a,b,ctx){ctx.font=\"10px \"+fn;ctx.textAlign=a;ctx.textBaseline=b;})",
_qC/* $wtext */ = function(_qD/* skk3 */, _qE/* skk4 */, _qF/* skk5 */, _qG/* skk6 */, _qH/* skk7 */, _qI/* skk8 */, _qJ/* skk9 */){
  var _qK/* skmh */ = function(_qL/* skka */, _qM/* skkb */, _qN/* skkc */, _/* EXTERNAL */){
    var _qO/* skmg */ = function(_qP/* skke */, _qQ/* skkf */, _qR/* skkg */, _/* EXTERNAL */){
      var _qS/* skmf */ = function(_qT/* skki */, _qU/* skkj */, _qV/* skkk */, _/* EXTERNAL */){
        var _qW/* skme */ = function(_qX/* skkm */, _qY/* skkn */, _qZ/* skko */, _/* EXTERNAL */){
          var _r0/* skkq */ = E(_qY/* skkn */),
          _r1/* skku */ = E(_qZ/* skko */),
          _r2/* skkx */ = __app2/* EXTERNAL */(E(_qq/* Core.Shape.Internal.f1 */), _r0/* skkq */, _r1/* skku */),
          _r3/* skkC */ = function(_r4/* skkD */){
            var _r5/* skkE */ = function(_r6/* skkF */){
              var _r7/* skkJ */ = eval/* EXTERNAL */(E(_qB/* Core.Shape.Internal.lvl6 */)),
              _r8/* skkR */ = __app4/* EXTERNAL */(E(_r7/* skkJ */), E(_qD/* skk3 */), _r4/* skkD */, _r6/* skkF */, _r0/* skkq */),
              _r9/* skl5 */ = __app4/* EXTERNAL */(E(_qu/* Core.Shape.Internal.f5 */), E(_qP/* skke */), E(_qT/* skki */), _r0/* skkq */, _r1/* skku */),
              _ra/* skla */ = E(_qX/* skkm */)/10,
              _rb/* sklg */ = __app4/* EXTERNAL */(E(_qr/* Core.Shape.Internal.f2 */), _ra/* skla */, _ra/* skla */, _r0/* skkq */, _r1/* skku */);
              if(!_r1/* skku */){
                var _rc/* sklw */ = __app5/* EXTERNAL */(E(_qs/* Core.Shape.Internal.f3 */), toJSStr/* EXTERNAL */(E(_qL/* skka */)), 0, 0, _r0/* skkq */, false),
                _rd/* sklC */ = __app2/* EXTERNAL */(E(_qm/* Core.Shape.Internal.$fAffineShape_f1 */), _r0/* skkq */, false);
                return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }else{
                var _re/* sklR */ = __app5/* EXTERNAL */(E(_qt/* Core.Shape.Internal.f4 */), toJSStr/* EXTERNAL */(E(_qL/* skka */)), 0, 0, _r0/* skkq */, true),
                _rf/* sklX */ = __app2/* EXTERNAL */(E(_qm/* Core.Shape.Internal.$fAffineShape_f1 */), _r0/* skkq */, true);
                return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }
            };
            switch(E(_qG/* skk6 */)){
              case 0:
                return new F(function(){return _r5/* skkE */(E(_qx/* Core.Shape.Internal.lvl2 */));});
                break;
              case 1:
                return new F(function(){return _r5/* skkE */(E(_qw/* Core.Shape.Internal.lvl1 */));});
                break;
              default:
                return new F(function(){return _r5/* skkE */(E(_qv/* Core.Shape.Internal.lvl */));});
            }
          };
          switch(E(_qF/* skk5 */)){
            case 0:
              return new F(function(){return _r3/* skkC */(E(_qA/* Core.Shape.Internal.lvl5 */));});
              break;
            case 1:
              return new F(function(){return _r3/* skkC */(E(_qz/* Core.Shape.Internal.lvl4 */));});
              break;
            default:
              return new F(function(){return _r3/* skkC */(E(_qy/* Core.Shape.Internal.lvl3 */));});
          }
        };
        return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_qJ/* skk9 */, _qW/* skme */, _qU/* skkj */, _qV/* skkk */, _/* EXTERNAL */);});
      };
      return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_qI/* skk8 */, _qS/* skmf */, _qQ/* skkf */, _qR/* skkg */, _/* EXTERNAL */);});
    };
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_qH/* skk7 */, _qO/* skmg */, _qM/* skkb */, _qN/* skkc */, _/* EXTERNAL */);});
  };
  return new T3(0,_qo/* Core.Shape.Internal.$fApplicativeShape3 */,function(_rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_qE/* skk4 */, _qK/* skmh */, _rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_ri/* BottomBase */ = 2,
_rj/* Just */ = function(_rk/* B1 */){
  return new T1(1,_rk/* B1 */);
},
_rl/* LeftAlign */ = 0,
_rm/* fill2 */ = "fillStyle",
_rn/* fill_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.fill();})");
}),
_ro/* fill1 */ = function(_rp/* scCd */, _rq/* scCe */){
  return new F(function(){return _pg/* Control.Monad.Skeleton.bone */(new T2(0,function(_rr/* scCf */, _/* EXTERNAL */){
    var _rs/* scCh */ = E(_rp/* scCd */),
    _rt/* scCm */ = B(_jm/* Core.Render.Internal.$wa */(_rs/* scCh */.a, _rs/* scCh */.b, _rs/* scCh */.c, _rs/* scCh */.d, _/* EXTERNAL */)),
    _ru/* scCp */ = E(_rr/* scCf */),
    _rv/* scCx */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), _ru/* scCp */, E(_rm/* Core.Render.Internal.fill2 */), B(_o4/* Core.Render.Internal.$wcolor2JSString */(_rt/* scCm */))),
    _rw/* scCD */ = __app1/* EXTERNAL */(E(_pq/* Core.Render.Internal.clip_f3 */), _ru/* scCp */),
    _rx/* scCK */ = B(A3(E(_rq/* scCe */).b,_ru/* scCp */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _ry/* scCQ */ = __app1/* EXTERNAL */(E(_rn/* Core.Render.Internal.fill_f1 */), _ru/* scCp */);
    return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */));});
},
_rz/* $fAffineShape3 */ = function(_rA/* sjG3 */, _rB/* sjG4 */, _/* EXTERNAL */){
  var _rC/* sjG6 */ = E(_rA/* sjG3 */);
  switch(_rC/* sjG6 */._){
    case 0:
      return new F(function(){return A2(_rB/* sjG4 */,_rC/* sjG6 */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _rD/* sjG9 */ = B(A1(_rC/* sjG6 */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_rB/* sjG4 */,_rD/* sjG9 */, _/* EXTERNAL */);});
      break;
    case 2:
      var _rE/* sjGk */ = rMV/* EXTERNAL */(E(E(_rC/* sjG6 */.a).c)),
      _rF/* sjGn */ = E(_rE/* sjGk */);
      if(!_rF/* sjGn */._){
        var _rG/* sjGr */ = new T(function(){
          return B(A1(_rC/* sjG6 */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_rF/* sjGn */.a));
          })));
        });
        return new F(function(){return A2(_rB/* sjG4 */,_rG/* sjGr */, _/* EXTERNAL */);});
      }else{
        return _av/* GHC.Types.False */;
      }
      break;
    default:
      var _rH/* sjGB */ = rMV/* EXTERNAL */(E(E(_rC/* sjG6 */.a).c)),
      _rI/* sjGE */ = E(_rH/* sjGB */);
      if(!_rI/* sjGE */._){
        var _rJ/* sjGK */ = B(A2(_rC/* sjG6 */.b,E(_rI/* sjGE */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_rB/* sjG4 */,_rJ/* sjGK */, _/* EXTERNAL */);});
      }else{
        return _av/* GHC.Types.False */;
      }
  }
},
_rK/* bezier_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.moveTo(x,y);})");
}),
_rL/* line_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.lineTo(x,y);})");
}),
_rM/* $wrect */ = function(_rN/* sk4P */, _rO/* sk4Q */, _rP/* sk4R */, _rQ/* sk4S */){
  var _rR/* sk6U */ = function(_rS/* sk5R */, _rT/* sk5S */, _rU/* sk5T */, _/* EXTERNAL */){
    var _rV/* sk6T */ = function(_rW/* sk5V */, _rX/* sk5W */, _rY/* sk5X */, _/* EXTERNAL */){
      var _rZ/* sk6S */ = function(_s0/* sk5Z */, _s1/* sk60 */, _s2/* sk61 */, _/* EXTERNAL */){
        return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_rQ/* sk4S */, function(_s3/* sk63 */, _s4/* sk64 */, _s5/* sk65 */, _/* EXTERNAL */){
          var _s6/* sk67 */ = E(_rS/* sk5R */),
          _s7/* sk6b */ = E(_rW/* sk5V */),
          _s8/* sk6f */ = E(_s4/* sk64 */),
          _s9/* sk6j */ = E(_s5/* sk65 */),
          _sa/* sk6m */ = __app4/* EXTERNAL */(E(_rK/* Core.Shape.Internal.bezier_f2 */), _s6/* sk67 */, _s7/* sk6b */, _s8/* sk6f */, _s9/* sk6j */),
          _sb/* sk6r */ = _s6/* sk67 */+E(_s0/* sk5Z */),
          _sc/* sk6u */ = E(_rL/* Core.Shape.Internal.line_f1 */),
          _sd/* sk6x */ = __app4/* EXTERNAL */(_sc/* sk6u */, _sb/* sk6r */, _s7/* sk6b */, _s8/* sk6f */, _s9/* sk6j */),
          _se/* sk6C */ = _s7/* sk6b */+E(_s3/* sk63 */),
          _sf/* sk6G */ = __app4/* EXTERNAL */(_sc/* sk6u */, _sb/* sk6r */, _se/* sk6C */, _s8/* sk6f */, _s9/* sk6j */),
          _sg/* sk6K */ = __app4/* EXTERNAL */(_sc/* sk6u */, _s6/* sk67 */, _se/* sk6C */, _s8/* sk6f */, _s9/* sk6j */),
          _sh/* sk6O */ = __app4/* EXTERNAL */(_sc/* sk6u */, _s6/* sk67 */, _s7/* sk6b */, _s8/* sk6f */, _s9/* sk6j */);
          return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _s1/* sk60 */, _s2/* sk61 */, _/* EXTERNAL */);});
      };
      return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_rP/* sk4R */, _rZ/* sk6S */, _rX/* sk5W */, _rY/* sk5X */, _/* EXTERNAL */);});
    };
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_rO/* sk4Q */, _rV/* sk6T */, _rT/* sk5S */, _rU/* sk5T */, _/* EXTERNAL */);});
  },
  _si/* sk5Q */ = function(_sj/* sk4T */, _/* EXTERNAL */){
    var _sk/* sk4V */ = E(_sj/* sk4T */),
    _sl/* sk5P */ = function(_sm/* sk4Y */, _/* EXTERNAL */){
      var _sn/* sk5O */ = function(_so/* sk50 */, _/* EXTERNAL */){
        var _sp/* sk5N */ = function(_sq/* sk52 */, _/* EXTERNAL */){
          var _sr/* sk5M */ = function(_ss/* sk54 */, _/* EXTERNAL */){
            return new T(function(){
              var _st/* sk5a */ = E(_sq/* sk52 */),
              _su/* sk5c */ = function(_sv/* sk5d */){
                var _sw/* sk5i */ = E(_ss/* sk54 */),
                _sx/* sk5m */ = E(_sk/* sk4V */.b)-E(_so/* sk50 */)-_sw/* sk5i *//2;
                return (_sx/* sk5m */==0) ? 0<_sw/* sk5i *//2 : (_sx/* sk5m */<=0) ?  -_sx/* sk5m */<_sw/* sk5i *//2 : _sx/* sk5m */<_sw/* sk5i *//2;
              },
              _sy/* sk5y */ = E(_sk/* sk4V */.a)-E(_sm/* sk4Y */)-_st/* sk5a *//2;
              if(!_sy/* sk5y */){
                if(0>=_st/* sk5a *//2){
                  return false;
                }else{
                  return B(_su/* sk5c */(_/* EXTERNAL */));
                }
              }else{
                if(_sy/* sk5y */<=0){
                  if( -_sy/* sk5y */>=_st/* sk5a *//2){
                    return false;
                  }else{
                    return B(_su/* sk5c */(_/* EXTERNAL */));
                  }
                }else{
                  if(_sy/* sk5y */>=_st/* sk5a *//2){
                    return false;
                  }else{
                    return B(_su/* sk5c */(_/* EXTERNAL */));
                  }
                }
              }
            });
          };
          return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_rQ/* sk4S */, _sr/* sk5M */, _/* EXTERNAL */);});
        };
        return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_rP/* sk4R */, _sp/* sk5N */, _/* EXTERNAL */);});
      };
      return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_rO/* sk4Q */, _sn/* sk5O */, _/* EXTERNAL */);});
    };
    return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_rN/* sk4P */, _sl/* sk5P */, _/* EXTERNAL */);});
  };
  return new T3(0,_si/* sk5Q */,function(_rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_rN/* sk4P */, _rR/* sk6U */, _rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_sz/* a15 */ = 0,
_sA/* lvl4 */ = new T1(0,_sz/* Motion.Main.a15 */),
_sB/* size */ = 200,
_sC/* sz */ = new T1(0,_sB/* Motion.Main.size */),
_sD/* shape */ = new T(function(){
  var _sE/* saIR */ = B(_rM/* Core.Shape.Internal.$wrect */(_sA/* Motion.Main.lvl4 */, _sA/* Motion.Main.lvl4 */, _sC/* Motion.Main.sz */, _sC/* Motion.Main.sz */));
  return new T3(0,_sE/* saIR */.a,_sE/* saIR */.b,_sE/* saIR */.c);
}),
_sF/* black1 */ = new T1(0,_f3/* Core.Render.Internal.applyTransform2 */),
_sG/* white */ = new T4(0,_sF/* Core.Render.Internal.black1 */,_sF/* Core.Render.Internal.black1 */,_sF/* Core.Render.Internal.black1 */,_sF/* Core.Render.Internal.black1 */),
_sH/* a17 */ = new T(function(){
  return B(_ro/* Core.Render.Internal.fill1 */(_sG/* Core.Render.Internal.white */, _sD/* Motion.Main.shape */));
}),
_sI/* a21 */ = function(_sJ/* saIV */, _sK/* saIW */){
  return new F(function(){return A1(_sK/* saIW */,new T2(0,_7/* GHC.Tuple.() */,_sJ/* saIV */));});
},
_sL/* black2 */ = new T1(0,_f2/* Core.Render.Internal.applyTransform1 */),
_sM/* black */ = new T4(0,_sL/* Core.Render.Internal.black2 */,_sL/* Core.Render.Internal.black2 */,_sL/* Core.Render.Internal.black2 */,_sF/* Core.Render.Internal.black1 */),
_sN/* Leave */ = 2,
_sO/* lvl2 */ = function(_sP/* sJMh */){
  switch(E(_sP/* sJMh */)){
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
_sQ/* lvl3 */ = function(_sR/* sJMj */){
  return (E(_sR/* sJMj */)==2) ? true : false;
},
_sS/* lvl4 */ = function(_sT/* sJMl */){
  switch(E(_sT/* sJMl */)){
    case 5:
      return true;
    case 6:
      return true;
    default:
      return false;
  }
},
_sU/* waitFor */ = function(_sV/* s6eh */, _sW/* s6ei */, _sX/* s6ej */){
  var _sY/* s6ek */ = new T(function(){
    return B(_sU/* Core.Util.waitFor */(_sV/* s6eh */, _sW/* s6ei */, _sX/* s6ej */));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_sV/* s6eh */, _sX/* s6ej */, function(_sZ/* s6el */){
    if(!B(A1(_sW/* s6ei */,_sZ/* s6el */))){
      return E(_sY/* s6ek */);
    }else{
      return new F(function(){return A2(_6T/* GHC.Base.return */,_sV/* s6eh */, _sZ/* s6el */);});
    }
  });});
},
_t0/* button */ = function(_t1/* sJMn */, _t2/* sJMo */, _t3/* sJMp */, _t4/* sJMq */){
  var _t5/* sJMr */ = new T(function(){
    var _t6/* sJMs */ = new T(function(){
      var _t7/* sJMA */ = function(_t8/* sJMt */, _t9/* sJMu */){
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_t4/* sJMq */, function(_ta/* sJMv */){
          return new F(function(){return A1(_t9/* sJMu */,new T2(0,_ta/* sJMv */,_t8/* sJMt */));});
        })));
      };
      return B(_sU/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _sS/* Core.UI.lvl4 */, _t7/* sJMA */));
    }),
    _tb/* sJMX */ = function(_tc/* sJMB */, _td/* sJMC */){
      var _te/* sJMD */ = new T(function(){
        var _tf/* sJMQ */ = function(_tg/* sJME */){
          var _th/* sJMF */ = E(_tg/* sJME */),
          _ti/* sJMH */ = _th/* sJMF */.b,
          _tj/* sJMI */ = E(_th/* sJMF */.a);
          if(_tj/* sJMI */==6){
            return new F(function(){return A1(_td/* sJMC */,new T2(0,_sN/* Core.View.Leave */,_ti/* sJMH */));});
          }else{
            return new F(function(){return A2(_t3/* sJMp */,_ti/* sJMH */, function(_tk/* sJMJ */){
              return new F(function(){return A1(_td/* sJMC */,new T2(0,_tj/* sJMI */,E(_tk/* sJMJ */).b));});
            });});
          }
        };
        return B(A2(_t6/* sJMs */,_tc/* sJMB */, _tf/* sJMQ */));
      });
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_t4/* sJMq */, function(_tl/* sJMR */){
        var _tm/* sJMS */ = E(_tl/* sJMR */);
        if(_tm/* sJMS */==3){
          return E(_te/* sJMD */);
        }else{
          return new F(function(){return A1(_td/* sJMC */,new T2(0,_tm/* sJMS */,_tc/* sJMB */));});
        }
      })));
    };
    return B(_sU/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _sQ/* Core.UI.lvl3 */, _tb/* sJMX */));
  }),
  _tn/* sJMY */ = new T(function(){
    var _to/* sJN6 */ = function(_tp/* sJMZ */, _tq/* sJN0 */){
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_t4/* sJMq */, function(_tr/* sJN1 */){
        return new F(function(){return A1(_tq/* sJN0 */,new T2(0,_tr/* sJN1 */,_tp/* sJMZ */));});
      })));
    };
    return B(_sU/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _sO/* Core.UI.lvl2 */, _to/* sJN6 */));
  }),
  _ts/* sJN7 */ = function(_tt/* sJN8 */){
    var _tu/* sJN9 */ = new T(function(){
      return B(A1(_t1/* sJMn */,_tt/* sJN8 */));
    }),
    _tv/* sJNv */ = function(_tw/* sJNa */){
      var _tx/* sJNb */ = function(_ty/* sJNc */){
        return new F(function(){return A2(_ts/* sJN7 */,E(_ty/* sJNc */).b, _tw/* sJNa */);});
      },
      _tz/* sJNg */ = function(_tA/* sJNh */){
        return new F(function(){return A2(_t5/* sJMr */,E(_tA/* sJNh */).b, _tx/* sJNb */);});
      },
      _tB/* sJNl */ = function(_tC/* sJNm */){
        return new F(function(){return A2(_t2/* sJMo */,E(_tC/* sJNm */).b, _tz/* sJNg */);});
      };
      return new F(function(){return A1(_tu/* sJN9 */,function(_tD/* sJNq */){
        return new F(function(){return A2(_tn/* sJMY */,E(_tD/* sJNq */).b, _tB/* sJNl */);});
      });});
    };
    return E(_tv/* sJNv */);
  };
  return E(_ts/* sJN7 */);
},
_tE/* clip_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.clip();})");
}),
_tF/* clip */ = function(_tG/* scb5 */, _tH/* scb6 */){
  var _tI/* scbC */ = B(_pg/* Control.Monad.Skeleton.bone */(new T2(0,function(_tJ/* scb7 */, _/* EXTERNAL */){
    var _tK/* scb9 */ = E(_tJ/* scb7 */),
    _tL/* scbe */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _tK/* scb9 */),
    _tM/* scbk */ = __app1/* EXTERNAL */(E(_pq/* Core.Render.Internal.clip_f3 */), _tK/* scb9 */),
    _tN/* scbr */ = B(A3(E(_tG/* scb5 */).b,_tK/* scb9 */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _tO/* scbx */ = __app1/* EXTERNAL */(E(_tE/* Core.Render.Internal.clip_f2 */), _tK/* scb9 */);
    return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */)));
  return new T2(0,E(_tI/* scbC */.a),E(new T2(2,new T2(2,_tI/* scbC */.b,new T1(1,function(_tP/* scbF */){
    return E(_tH/* scb6 */);
  })),_pp/* Core.Render.Internal.clip1 */)));
},
_tQ/* easeTo2 */ = function(_tR/* sbeA */, _tS/* sbeB */){
  return new F(function(){return A1(_tS/* sbeB */,new T2(0,_7/* GHC.Tuple.() */,_tR/* sbeA */));});
},
_tT/* easeTo1 */ = function(_tU/* sbeD */, _tV/* B2 */, _tW/* B1 */){
  return new F(function(){return _tQ/* Core.Ease.easeTo2 */(_tV/* B2 */, _tW/* B1 */);});
},
_tX/* easeIn */ = function(_tY/* saXI */, _tZ/* saXJ */){
  return new F(function(){return A1(_tY/* saXI */,_tZ/* saXJ */);});
},
_u0/* linear */ = function(_tV/* B2 */, _tW/* B1 */){
  return new F(function(){return _tX/* Core.Ease.easeIn */(_tV/* B2 */, _tW/* B1 */);});
},
_u1/* a19 */ = 0.2,
_u2/* lvl7 */ = new T1(0,_u1/* Motion.Main.a19 */),
_u3/* a20 */ = 1,
_u4/* lvl9 */ = new T1(0,_u3/* Motion.Main.a20 */),
_u5/* lvl10 */ = new T4(0,_u2/* Motion.Main.lvl7 */,_u2/* Motion.Main.lvl7 */,_u2/* Motion.Main.lvl7 */,_u4/* Motion.Main.lvl9 */),
_u6/* lvl11 */ = "mplus",
_u7/* lvl12 */ = 1.2,
_u8/* lvl13 */ = new T1(0,_u7/* Motion.Main.lvl12 */),
_u9/* liftA1 */ = function(_ua/* s3h5 */, _ub/* s3h6 */, _uc/* s3h7 */, _/* EXTERNAL */){
  var _ud/* s3h9 */ = B(A1(_ub/* s3h6 */,_/* EXTERNAL */)),
  _ue/* s3hc */ = B(A1(_uc/* s3h7 */,_/* EXTERNAL */));
  return new T(function(){
    return B(A2(_ua/* s3h5 */,_ud/* s3h9 */, _ue/* s3hc */));
  });
},
_uf/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Unable to operate opLift"));
}),
_ug/* $wpoly_fail */ = function(_uh/* sb4A */){
  return new F(function(){return err/* EXTERNAL */(_uf/* Core.Ease.lvl */);});
},
_ui/* lvl1 */ = new T(function(){
  return B(_ug/* Core.Ease.$wpoly_fail */(_/* EXTERNAL */));
}),
_uj/* opLift */ = function(_uk/* sb4B */, _ul/* sb4C */, _um/* sb4D */){
  var _un/* sb4E */ = function(_uo/* sb4F */){
    var _up/* sb77 */ = function(_/* EXTERNAL */){
      var _uq/* sb4H */ = function(_/* EXTERNAL */, _ur/* sb4J */){
        var _us/* sb4K */ = E(_um/* sb4D */);
        switch(_us/* sb4K */._){
          case 0:
            return new T(function(){
              return B(A2(_uk/* sb4B */,_ur/* sb4J */, _us/* sb4K */.a));
            });
          case 1:
            var _ut/* sb4O */ = B(A1(_us/* sb4K */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sb4B */,_ur/* sb4J */, _ut/* sb4O */));
            });
          case 2:
            var _uu/* sb50 */ = rMV/* EXTERNAL */(E(E(_us/* sb4K */.a).c)),
            _uv/* sb53 */ = E(_uu/* sb50 */);
            return (_uv/* sb53 */._==0) ? new T(function(){
              var _uw/* sb57 */ = new T(function(){
                return B(A1(_us/* sb4K */.b,new T(function(){
                  return B(_fB/* Data.Tuple.fst */(_uv/* sb53 */.a));
                })));
              });
              return B(A2(_uk/* sb4B */,_ur/* sb4J */, _uw/* sb57 */));
            }) : E(_ui/* Core.Ease.lvl1 */);
          default:
            var _ux/* sb5j */ = rMV/* EXTERNAL */(E(E(_us/* sb4K */.a).c)),
            _uy/* sb5m */ = E(_ux/* sb5j */);
            if(!_uy/* sb5m */._){
              var _uz/* sb5s */ = B(A2(_us/* sb4K */.b,E(_uy/* sb5m */.a).a, _/* EXTERNAL */));
              return new T(function(){
                return B(A2(_uk/* sb4B */,_ur/* sb4J */, _uz/* sb5s */));
              });
            }else{
              return E(_ui/* Core.Ease.lvl1 */);
            }
        }
      },
      _uA/* sb5y */ = function(_/* EXTERNAL */){
        var _uB/* sb5A */ = E(_um/* sb4D */);
        switch(_uB/* sb5A */._){
          case 0:
            return E(_ui/* Core.Ease.lvl1 */);
          case 1:
            var _uC/* sb5E */ = B(A1(_uB/* sb5A */.a,_/* EXTERNAL */));
            return E(_ui/* Core.Ease.lvl1 */);
          case 2:
            var _uD/* sb5Q */ = rMV/* EXTERNAL */(E(E(_uB/* sb5A */.a).c));
            return (E(_uD/* sb5Q */)._==0) ? E(_ui/* Core.Ease.lvl1 */) : E(_ui/* Core.Ease.lvl1 */);
          default:
            var _uE/* sb67 */ = rMV/* EXTERNAL */(E(E(_uB/* sb5A */.a).c)),
            _uF/* sb6a */ = E(_uE/* sb67 */);
            if(!_uF/* sb6a */._){
              var _uG/* sb6g */ = B(A2(_uB/* sb5A */.b,E(_uF/* sb6a */.a).a, _/* EXTERNAL */));
              return E(_ui/* Core.Ease.lvl1 */);
            }else{
              return E(_ui/* Core.Ease.lvl1 */);
            }
        }
      },
      _uH/* sb6m */ = E(_ul/* sb4C */);
      switch(_uH/* sb6m */._){
        case 0:
          return new F(function(){return _uq/* sb4H */(_/* EXTERNAL */, _uH/* sb6m */.a);});
          break;
        case 1:
          var _uI/* sb6p */ = B(A1(_uH/* sb6m */.a,_/* EXTERNAL */));
          return new F(function(){return _uq/* sb4H */(_/* EXTERNAL */, _uI/* sb6p */);});
          break;
        case 2:
          var _uJ/* sb6A */ = rMV/* EXTERNAL */(E(E(_uH/* sb6m */.a).c)),
          _uK/* sb6D */ = E(_uJ/* sb6A */);
          if(!_uK/* sb6D */._){
            var _uL/* sb6K */ = new T(function(){
              return B(A1(_uH/* sb6m */.b,new T(function(){
                return E(E(_uK/* sb6D */.a).a);
              })));
            });
            return new F(function(){return _uq/* sb4H */(_/* EXTERNAL */, _uL/* sb6K */);});
          }else{
            return new F(function(){return _uA/* sb5y */(_/* EXTERNAL */);});
          }
          break;
        default:
          var _uM/* sb6U */ = rMV/* EXTERNAL */(E(E(_uH/* sb6m */.a).c)),
          _uN/* sb6X */ = E(_uM/* sb6U */);
          if(!_uN/* sb6X */._){
            var _uO/* sb73 */ = B(A2(_uH/* sb6m */.b,E(_uN/* sb6X */.a).a, _/* EXTERNAL */));
            return new F(function(){return _uq/* sb4H */(_/* EXTERNAL */, _uO/* sb73 */);});
          }else{
            return new F(function(){return _uA/* sb5y */(_/* EXTERNAL */);});
          }
      }
    };
    return new T1(1,_up/* sb77 */);
  },
  _uP/* sb78 */ = E(_ul/* sb4C */);
  switch(_uP/* sb78 */._){
    case 0:
      var _uQ/* sb79 */ = _uP/* sb78 */.a,
      _uR/* sb7a */ = E(_um/* sb4D */);
      switch(_uR/* sb7a */._){
        case 0:
          return new T1(0,new T(function(){
            return B(A2(_uk/* sb4B */,_uQ/* sb79 */, _uR/* sb7a */.a));
          }));
        case 1:
          var _uS/* sb7j */ = function(_/* EXTERNAL */){
            var _uT/* sb7f */ = B(A1(_uR/* sb7a */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sb4B */,_uQ/* sb79 */, _uT/* sb7f */));
            });
          };
          return new T1(1,_uS/* sb7j */);
        case 2:
          var _uU/* sb7m */ = new T(function(){
            return B(A1(_uk/* sb4B */,_uQ/* sb79 */));
          }),
          _uV/* sb7p */ = function(_uW/* sb7n */){
            return new F(function(){return A1(_uU/* sb7m */,new T(function(){
              return B(A1(_uR/* sb7a */.b,_uW/* sb7n */));
            }));});
          };
          return new T2(2,_uR/* sb7a */.a,_uV/* sb7p */);
        default:
          var _uX/* sb7s */ = new T(function(){
            return B(A1(_uk/* sb4B */,_uQ/* sb79 */));
          }),
          _uY/* sb7z */ = function(_uZ/* sb7t */, _/* EXTERNAL */){
            var _v0/* sb7v */ = B(A2(_uR/* sb7a */.b,_uZ/* sb7t */, _/* EXTERNAL */));
            return new T(function(){
              return B(A1(_uX/* sb7s */,_v0/* sb7v */));
            });
          };
          return new T2(3,_uR/* sb7a */.a,_uY/* sb7z */);
      }
      break;
    case 1:
      var _v1/* sb7A */ = _uP/* sb78 */.a,
      _v2/* sb7B */ = E(_um/* sb4D */);
      switch(_v2/* sb7B */._){
        case 0:
          var _v3/* sb7I */ = function(_/* EXTERNAL */){
            var _v4/* sb7E */ = B(A1(_v1/* sb7A */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sb4B */,_v4/* sb7E */, _v2/* sb7B */.a));
            });
          };
          return new T1(1,_v3/* sb7I */);
        case 1:
          return new T1(1,function(_/* EXTERNAL */){
            return new F(function(){return _u9/* GHC.Base.liftA1 */(_uk/* sb4B */, _v1/* sb7A */, _v2/* sb7B */.a, _/* EXTERNAL */);});
          });
        case 2:
          var _v5/* sb7U */ = function(_v6/* sb7N */, _/* EXTERNAL */){
            var _v7/* sb7P */ = B(A1(_v1/* sb7A */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sb4B */,_v7/* sb7P */, new T(function(){
                return B(A1(_v2/* sb7B */.b,_v6/* sb7N */));
              })));
            });
          };
          return new T2(3,_v2/* sb7B */.a,_v5/* sb7U */);
        default:
          var _v8/* sb86 */ = function(_v9/* sb7X */, _/* EXTERNAL */){
            var _va/* sb7Z */ = B(A1(_v1/* sb7A */,_/* EXTERNAL */)),
            _vb/* sb82 */ = B(A2(_v2/* sb7B */.b,_v9/* sb7X */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sb4B */,_va/* sb7Z */, _vb/* sb82 */));
            });
          };
          return new T2(3,_v2/* sb7B */.a,_v8/* sb86 */);
      }
      break;
    case 2:
      var _vc/* sb87 */ = _uP/* sb78 */.a,
      _vd/* sb88 */ = _uP/* sb78 */.b,
      _ve/* sb89 */ = E(_um/* sb4D */);
      switch(_ve/* sb89 */._){
        case 0:
          var _vf/* sb8d */ = function(_vg/* sb8b */){
            return new F(function(){return A2(_uk/* sb4B */,new T(function(){
              return B(A1(_vd/* sb88 */,_vg/* sb8b */));
            }), _ve/* sb89 */.a);});
          };
          return new T2(2,_vc/* sb87 */,_vf/* sb8d */);
        case 1:
          var _vh/* sb8m */ = function(_vi/* sb8f */, _/* EXTERNAL */){
            var _vj/* sb8h */ = B(A1(_ve/* sb89 */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sb4B */,new T(function(){
                return B(A1(_vd/* sb88 */,_vi/* sb8f */));
              }), _vj/* sb8h */));
            });
          };
          return new T2(3,_vc/* sb87 */,_vh/* sb8m */);
        default:
          return new F(function(){return _un/* sb4E */(_/* EXTERNAL */);});
      }
      break;
    default:
      var _vk/* sb8n */ = _uP/* sb78 */.a,
      _vl/* sb8o */ = _uP/* sb78 */.b,
      _vm/* sb8p */ = E(_um/* sb4D */);
      switch(_vm/* sb8p */._){
        case 0:
          var _vn/* sb8x */ = function(_vo/* sb8r */, _/* EXTERNAL */){
            var _vp/* sb8t */ = B(A2(_vl/* sb8o */,_vo/* sb8r */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sb4B */,_vp/* sb8t */, _vm/* sb8p */.a));
            });
          };
          return new T2(3,_vk/* sb8n */,_vn/* sb8x */);
        case 1:
          var _vq/* sb8I */ = function(_vr/* sb8z */, _/* EXTERNAL */){
            var _vs/* sb8B */ = B(A2(_vl/* sb8o */,_vr/* sb8z */, _/* EXTERNAL */)),
            _vt/* sb8E */ = B(A1(_vm/* sb8p */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sb4B */,_vs/* sb8B */, _vt/* sb8E */));
            });
          };
          return new T2(3,_vk/* sb8n */,_vq/* sb8I */);
        default:
          return new F(function(){return _un/* sb4E */(_/* EXTERNAL */);});
      }
  }
},
_vu/* timesDouble */ = function(_vv/* s18yK */, _vw/* s18yL */){
  return E(_vv/* s18yK */)*E(_vw/* s18yL */);
},
_vx/* lvl14 */ = new T(function(){
  return B(_uj/* Core.Ease.opLift */(_vu/* GHC.Float.timesDouble */, _sC/* Motion.Main.sz */, _u8/* Motion.Main.lvl13 */));
}),
_vy/* lvl15 */ = 2,
_vz/* lvl16 */ = new T1(0,_vy/* Motion.Main.lvl15 */),
_vA/* lvl17 */ = new T(function(){
  return B(_uj/* Core.Ease.opLift */(_in/* GHC.Float.divideDouble */, _sC/* Motion.Main.sz */, _vz/* Motion.Main.lvl16 */));
}),
_vB/* lvl18 */ = new T(function(){
  return B(_uj/* Core.Ease.opLift */(_vu/* GHC.Float.timesDouble */, _sC/* Motion.Main.sz */, _u2/* Motion.Main.lvl7 */));
}),
_vC/* lvl19 */ = 15,
_vD/* lvl2 */ = 6,
_vE/* lvl20 */ = function(_vF/* saIY */){
  var _vG/* saIZ */ = E(_vF/* saIY */);
  return new T0(2);
},
_vH/* lvl21 */ = new T4(0,_vD/* Motion.Main.lvl2 */,_vD/* Motion.Main.lvl2 */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_vI/* lvl22 */ = new T2(0,_vD/* Motion.Main.lvl2 */,_vH/* Motion.Main.lvl21 */),
_vJ/* lvl23 */ = new T2(0,_vI/* Motion.Main.lvl22 */,_6/* GHC.Types.[] */),
_vK/* lvl3 */ = 10,
_vL/* a16 */ = 3,
_vM/* lvl5 */ = new T1(0,_vL/* Motion.Main.a16 */),
_vN/* a18 */ = 5,
_vO/* lvl6 */ = new T1(0,_vN/* Motion.Main.a18 */),
_vP/* lvl8 */ = new T4(0,_sA/* Motion.Main.lvl4 */,_sA/* Motion.Main.lvl4 */,_sA/* Motion.Main.lvl4 */,_u2/* Motion.Main.lvl7 */),
_vQ/* $fAffineShape1 */ = function(_vR/* sjO4 */, _vS/* sjO5 */, _vT/* sjO6 */, _/* EXTERNAL */){
  var _vU/* sjOf */ = __app2/* EXTERNAL */(E(_qm/* Core.Shape.Internal.$fAffineShape_f1 */), E(_vS/* sjO5 */), E(_vT/* sjO6 */));
  return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_vV/* $w$caffine */ = function(_vW/* sjOi */, _vX/* sjOj */, _vY/* sjOk */, _vZ/* sjOl */, _w0/* sjOm */, _w1/* sjOn */, _w2/* sjOo */){
  var _w3/* sjQ8 */ = function(_w4/* sjPK */, _w5/* sjPL */, _w6/* sjPM */, _/* EXTERNAL */){
    var _w7/* sjQ7 */ = function(_w8/* sjPO */, _w9/* sjPP */, _wa/* sjPQ */, _/* EXTERNAL */){
      var _wb/* sjQ6 */ = function(_wc/* sjPS */, _wd/* sjPT */, _we/* sjPU */, _/* EXTERNAL */){
        var _wf/* sjQ5 */ = function(_wg/* sjPW */, _wh/* sjPX */, _wi/* sjPY */, _/* EXTERNAL */){
          return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_w0/* sjOm */, function(_wj/* sjQ0 */, _wk/* sjQ1 */, _wl/* sjQ2 */, _/* EXTERNAL */){
            return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_w1/* sjOn */, _vQ/* Core.Shape.Internal.$fAffineShape1 */, _wk/* sjQ1 */, _wl/* sjQ2 */, _/* EXTERNAL */);});
          }, _wh/* sjPX */, _wi/* sjPY */, _/* EXTERNAL */);});
        };
        return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_vZ/* sjOl */, _wf/* sjQ5 */, _wd/* sjPT */, _we/* sjPU */, _/* EXTERNAL */);});
      };
      return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_vY/* sjOk */, _wb/* sjQ6 */, _w9/* sjPP */, _wa/* sjPQ */, _/* EXTERNAL */);});
    };
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_vX/* sjOj */, _w7/* sjQ7 */, _w5/* sjPL */, _w6/* sjPM */, _/* EXTERNAL */);});
  },
  _wm/* sjPJ */ = function(_wn/* sjOp */, _/* EXTERNAL */){
    var _wo/* sjOr */ = E(_wn/* sjOp */),
    _wp/* sjOs */ = _wo/* sjOr */.a,
    _wq/* sjOt */ = _wo/* sjOr */.b,
    _wr/* sjPI */ = function(_ws/* sjOu */, _/* EXTERNAL */){
      var _wt/* sjPH */ = function(_wu/* sjOw */, _/* EXTERNAL */){
        var _wv/* sjPG */ = function(_ww/* sjOy */, _/* EXTERNAL */){
          var _wx/* sjPF */ = function(_wy/* sjOA */, _/* EXTERNAL */){
            var _wz/* sjPE */ = function(_wA/* sjOC */, _/* EXTERNAL */){
              var _wB/* sjPD */ = function(_wC/* sjOE */){
                var _wD/* sjOF */ = new T(function(){
                  return E(_wu/* sjOw */)*E(_wy/* sjOA */)-E(_ws/* sjOu */)*E(_wA/* sjOC */);
                });
                return new F(function(){return A1(_w2/* sjOo */,new T2(0,new T(function(){
                  var _wE/* sjOR */ = E(_wu/* sjOw */),
                  _wF/* sjOX */ = E(_wA/* sjOC */);
                  return ( -(_wE/* sjOR */*E(_wC/* sjOE */))+_wE/* sjOR */*E(_wq/* sjOt */)+_wF/* sjOX */*E(_ww/* sjOy */)-_wF/* sjOX */*E(_wp/* sjOs */))/E(_wD/* sjOF */);
                }),new T(function(){
                  var _wG/* sjPf */ = E(_ws/* sjOu */),
                  _wH/* sjPl */ = E(_wy/* sjOA */);
                  return (_wG/* sjPf */*E(_wC/* sjOE */)-_wG/* sjPf */*E(_wq/* sjOt */)-_wH/* sjPl */*E(_ww/* sjOy */)+_wH/* sjPl */*E(_wp/* sjOs */))/E(_wD/* sjOF */);
                })));});
              };
              return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_w1/* sjOn */, _wB/* sjPD */, _/* EXTERNAL */);});
            };
            return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_w0/* sjOm */, _wz/* sjPE */, _/* EXTERNAL */);});
          };
          return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_vZ/* sjOl */, _wx/* sjPF */, _/* EXTERNAL */);});
        };
        return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_vY/* sjOk */, _wv/* sjPG */, _/* EXTERNAL */);});
      };
      return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_vX/* sjOj */, _wt/* sjPH */, _/* EXTERNAL */);});
    };
    return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_vW/* sjOi */, _wr/* sjPI */, _/* EXTERNAL */);});
  };
  return new T3(0,_wm/* sjPJ */,function(_rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_vW/* sjOi */, _w3/* sjQ8 */, _rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_wI/* forceTo_b1 */ = 1,
_wJ/* $wforceTo */ = function(_wK/* saXZ */, _wL/* saY0 */){
  var _wM/* saY1 */ = new T(function(){
    var _wN/* saYi */ = function(_wO/* saY2 */, _wP/* saY3 */, _wQ/* saY4 */){
      return new F(function(){return A1(_wQ/* saY4 */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_wL/* saY0 */,new T4(0,_wL/* saY0 */,_wL/* saY0 */,_wI/* Core.Ease.forceTo_b1 */,new T(function(){
        return E(E(E(_wO/* saY2 */).b).d);
      })))),_wP/* saY3 */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _wK/* saXZ */, _wN/* saYi */));
  }),
  _wR/* saYJ */ = function(_wS/* saYj */, _wT/* saYk */){
    var _wU/* saYl */ = new T(function(){
      return B(A2(_wM/* saY1 */,_wS/* saYj */, _wT/* saYk */));
    }),
    _wV/* saYG */ = function(_wW/* saYm */){
      var _wX/* saYn */ = new T(function(){
        var _wY/* saYo */ = E(_wW/* saYm */),
        _wZ/* saYr */ = E(_wY/* saYo */.a),
        _x0/* saYs */ = E(_wY/* saYo */.b),
        _x1/* saYx */ = E(_x0/* saYs */.a),
        _x2/* saYy */ = E(_x0/* saYs */.b),
        _x3/* saYA */ = E(_x0/* saYs */.c),
        _x4/* saYB */ = E(_x0/* saYs */.d);
        return E(_wU/* saYl */);
      });
      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_wK/* saXZ */, _wW/* saYm */, function(_x5/* saYC */){
        return E(_wX/* saYn */);
      })));
    };
    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_wK/* saXZ */, _wV/* saYG */)));
  };
  return E(_wR/* saYJ */);
},
_x6/* $winsert */ = function(_x7/* s3sqy */, _x8/* s3sqz */, _x9/* s3sqA */){
  var _xa/* s3sqB */ = E(_x8/* s3sqz */),
  _xb/* s3sqC */ = E(_x9/* s3sqA */);
  switch(_xb/* s3sqC */._){
    case 0:
      var _xc/* s3sqD */ = _xb/* s3sqC */.a,
      _xd/* s3sqE */ = _xb/* s3sqC */.b,
      _xe/* s3sqF */ = _xb/* s3sqC */.c,
      _xf/* s3sqG */ = _xb/* s3sqC */.d,
      _xg/* s3sqH */ = _xd/* s3sqE */>>>0;
      if(((_x7/* s3sqy */>>>0&((_xg/* s3sqH */-1>>>0^4294967295)>>>0^_xg/* s3sqH */)>>>0)>>>0&4294967295)==_xc/* s3sqD */){
        return ((_x7/* s3sqy */>>>0&_xg/* s3sqH */)>>>0==0) ? new T4(0,_xc/* s3sqD */,_xd/* s3sqE */,E(B(_x6/* Data.IntMap.Strict.$winsert */(_x7/* s3sqy */, _xa/* s3sqB */, _xe/* s3sqF */))),E(_xf/* s3sqG */)) : new T4(0,_xc/* s3sqD */,_xd/* s3sqE */,E(_xe/* s3sqF */),E(B(_x6/* Data.IntMap.Strict.$winsert */(_x7/* s3sqy */, _xa/* s3sqB */, _xf/* s3sqG */))));
      }else{
        var _xh/* s3sqU */ = (_x7/* s3sqy */>>>0^_xc/* s3sqD */>>>0)>>>0,
        _xi/* s3sqX */ = (_xh/* s3sqU */|_xh/* s3sqU */>>>1)>>>0,
        _xj/* s3sqZ */ = (_xi/* s3sqX */|_xi/* s3sqX */>>>2)>>>0,
        _xk/* s3sr1 */ = (_xj/* s3sqZ */|_xj/* s3sqZ */>>>4)>>>0,
        _xl/* s3sr3 */ = (_xk/* s3sr1 */|_xk/* s3sr1 */>>>8)>>>0,
        _xm/* s3sr5 */ = (_xl/* s3sr3 */|_xl/* s3sr3 */>>>16)>>>0,
        _xn/* s3sr7 */ = (_xm/* s3sr5 */^_xm/* s3sr5 */>>>1)>>>0&4294967295,
        _xo/* s3sra */ = _xn/* s3sr7 */>>>0;
        return ((_x7/* s3sqy */>>>0&_xo/* s3sra */)>>>0==0) ? new T4(0,(_x7/* s3sqy */>>>0&((_xo/* s3sra */-1>>>0^4294967295)>>>0^_xo/* s3sra */)>>>0)>>>0&4294967295,_xn/* s3sr7 */,E(new T2(1,_x7/* s3sqy */,_xa/* s3sqB */)),E(_xb/* s3sqC */)) : new T4(0,(_x7/* s3sqy */>>>0&((_xo/* s3sra */-1>>>0^4294967295)>>>0^_xo/* s3sra */)>>>0)>>>0&4294967295,_xn/* s3sr7 */,E(_xb/* s3sqC */),E(new T2(1,_x7/* s3sqy */,_xa/* s3sqB */)));
      }
      break;
    case 1:
      var _xp/* s3srr */ = _xb/* s3sqC */.a;
      if(_x7/* s3sqy */!=_xp/* s3srr */){
        var _xq/* s3srv */ = (_x7/* s3sqy */>>>0^_xp/* s3srr */>>>0)>>>0,
        _xr/* s3sry */ = (_xq/* s3srv */|_xq/* s3srv */>>>1)>>>0,
        _xs/* s3srA */ = (_xr/* s3sry */|_xr/* s3sry */>>>2)>>>0,
        _xt/* s3srC */ = (_xs/* s3srA */|_xs/* s3srA */>>>4)>>>0,
        _xu/* s3srE */ = (_xt/* s3srC */|_xt/* s3srC */>>>8)>>>0,
        _xv/* s3srG */ = (_xu/* s3srE */|_xu/* s3srE */>>>16)>>>0,
        _xw/* s3srI */ = (_xv/* s3srG */^_xv/* s3srG */>>>1)>>>0&4294967295,
        _xx/* s3srL */ = _xw/* s3srI */>>>0;
        return ((_x7/* s3sqy */>>>0&_xx/* s3srL */)>>>0==0) ? new T4(0,(_x7/* s3sqy */>>>0&((_xx/* s3srL */-1>>>0^4294967295)>>>0^_xx/* s3srL */)>>>0)>>>0&4294967295,_xw/* s3srI */,E(new T2(1,_x7/* s3sqy */,_xa/* s3sqB */)),E(_xb/* s3sqC */)) : new T4(0,(_x7/* s3sqy */>>>0&((_xx/* s3srL */-1>>>0^4294967295)>>>0^_xx/* s3srL */)>>>0)>>>0&4294967295,_xw/* s3srI */,E(_xb/* s3sqC */),E(new T2(1,_x7/* s3sqy */,_xa/* s3sqB */)));
      }else{
        return new T2(1,_x7/* s3sqy */,_xa/* s3sqB */);
      }
      break;
    default:
      return new T2(1,_x7/* s3sqy */,_xa/* s3sqB */);
  }
},
_xy/* Cancel */ = 6,
_xz/* Drag */ = 4,
_xA/* Enter */ = 0,
_xB/* Move */ = 1,
_xC/* Press */ = 3,
_xD/* Release */ = 5,
_xE/* lvl23 */ = function(_xF/* sfEz */, _xG/* sfEA */){
  return new F(function(){return A1(_xG/* sfEA */,new T2(0,_7/* GHC.Tuple.() */,_xF/* sfEz */));});
},
_xH/* lvl24 */ = new T1(1,_6/* GHC.Types.[] */),
_xI/* lvl */ = 0,
_xJ/* lvl25 */ = new T4(0,_xI/* Core.View.lvl */,_xI/* Core.View.lvl */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_xK/* lvl26 */ = new T2(0,_xI/* Core.View.lvl */,_xJ/* Core.View.lvl25 */),
_xL/* lvl27 */ = new T2(0,_xK/* Core.View.lvl26 */,_6/* GHC.Types.[] */),
_xM/* lvl1 */ = 1,
_xN/* lvl28 */ = new T4(0,_xM/* Core.View.lvl1 */,_xM/* Core.View.lvl1 */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_xO/* lvl29 */ = new T2(0,_xM/* Core.View.lvl1 */,_xN/* Core.View.lvl28 */),
_xP/* lvl30 */ = new T2(0,_xO/* Core.View.lvl29 */,_6/* GHC.Types.[] */),
_xQ/* fork */ = function(_xR/* srPv */){
  return E(E(_xR/* srPv */).c);
},
_xS/* lvl */ = new T1(1,_6/* GHC.Types.[] */),
_xT/* spawn1 */ = function(_xU/* sJti */){
  var _xV/* sJtp */ = function(_/* EXTERNAL */){
    var _xW/* sJtk */ = nMV/* EXTERNAL */(_xS/* Haste.Concurrent.lvl */);
    return new T(function(){
      return B(A1(_xU/* sJti */,_xW/* sJtk */));
    });
  };
  return new T1(0,_xV/* sJtp */);
},
_xX/* spawn */ = function(_xY/* sJtK */, _xZ/* sJtL */){
  var _y0/* sJtM */ = new T(function(){
    return B(_xQ/* Haste.Concurrent.Monad.fork */(_xY/* sJtK */));
  }),
  _y1/* sJtN */ = B(_9x/* Haste.Concurrent.Monad.$p1MonadConc */(_xY/* sJtK */)),
  _y2/* sJtT */ = function(_y3/* sJtP */){
    var _y4/* sJtR */ = new T(function(){
      return B(A1(_y0/* sJtM */,new T(function(){
        return B(A1(_xZ/* sJtL */,_y3/* sJtP */));
      })));
    });
    return new F(function(){return A3(_9z/* GHC.Base.>> */,_y1/* sJtN */, _y4/* sJtR */, new T(function(){
      return B(A2(_6T/* GHC.Base.return */,_y1/* sJtN */, _y3/* sJtP */));
    }));});
  };
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_y1/* sJtN */, new T(function(){
    return B(A2(_2V/* Haste.Concurrent.Monad.liftConc */,_xY/* sJtK */, _xT/* Haste.Concurrent.spawn1 */));
  }), _y2/* sJtT */);});
},
_y5/* makeView */ = function(_y6/* sfEC */, _y7/* sfED */, _y8/* sfEE */, _y9/* sfEF */){
  var _ya/* sfEG */ = new T(function(){
    return B(A1(_y6/* sfEC */,_sN/* Core.View.Leave */));
  }),
  _yb/* sfEH */ = new T(function(){
    return B(A1(_y6/* sfEC */,_xA/* Core.View.Enter */));
  }),
  _yc/* sfEI */ = new T(function(){
    return B(A1(_y6/* sfEC */,_xz/* Core.View.Drag */));
  }),
  _yd/* sfEJ */ = new T(function(){
    return B(_xX/* Haste.Concurrent.spawn */(_8l/* Core.World.Internal.$fMonadConcWorld */, _y9/* sfEF */));
  }),
  _ye/* sfEK */ = new T(function(){
    return B(A1(_y6/* sfEC */,_xy/* Core.View.Cancel */));
  }),
  _yf/* sfEL */ = new T(function(){
    return B(A1(_y6/* sfEC */,_xD/* Core.View.Release */));
  }),
  _yg/* sfEM */ = new T(function(){
    return B(A1(_y6/* sfEC */,_xC/* Core.View.Press */));
  }),
  _yh/* sfEN */ = new T(function(){
    return B(A1(_y6/* sfEC */,_xB/* Core.View.Move */));
  }),
  _yi/* sfK2 */ = function(_yj/* sfEO */){
    var _yk/* sfEP */ = new T(function(){
      return B(A1(_yd/* sfEJ */,_yj/* sfEO */));
    }),
    _yl/* sfK1 */ = function(_ym/* sfEQ */){
      var _yn/* sfK0 */ = function(_yo/* sfER */){
        var _yp/* sfES */ = E(_yo/* sfER */),
        _yq/* sfET */ = _yp/* sfES */.a,
        _yr/* sfEU */ = _yp/* sfES */.b,
        _ys/* sfEV */ = new T(function(){
          var _yt/* sfEW */ = E(_ya/* sfEG */);
          if(!_yt/* sfEW */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sfET */, _yt/* sfEW */.a));
          }
        }),
        _yu/* sfEY */ = new T(function(){
          var _yv/* sfEZ */ = E(_yb/* sfEH */);
          if(!_yv/* sfEZ */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sfET */, _yv/* sfEZ */.a));
          }
        }),
        _yw/* sfF1 */ = new T(function(){
          var _yx/* sfF2 */ = E(_yc/* sfEI */);
          if(!_yx/* sfF2 */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sfET */, _yx/* sfF2 */.a));
          }
        }),
        _yy/* sfF4 */ = new T(function(){
          var _yz/* sfF5 */ = E(_ye/* sfEK */);
          if(!_yz/* sfF5 */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sfET */, _yz/* sfF5 */.a));
          }
        }),
        _yA/* sfF7 */ = new T(function(){
          var _yB/* sfF8 */ = E(_yf/* sfEL */);
          if(!_yB/* sfF8 */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sfET */, _yB/* sfF8 */.a));
          }
        }),
        _yC/* sfFa */ = new T(function(){
          var _yD/* sfFb */ = E(_yg/* sfEM */);
          if(!_yD/* sfFb */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sfET */, _yD/* sfFb */.a));
          }
        }),
        _yE/* sfFd */ = new T(function(){
          var _yF/* sfFe */ = E(_yh/* sfEN */);
          if(!_yF/* sfFe */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sfET */, _yF/* sfFe */.a));
          }
        }),
        _yG/* sfJZ */ = function(_/* EXTERNAL */){
          var _yH/* sfFh */ = nMV/* EXTERNAL */(_xP/* Core.View.lvl30 */),
          _yI/* sfFj */ = _yH/* sfFh */,
          _yJ/* sfJX */ = function(_/* EXTERNAL */){
            var _yK/* sfFm */ = nMV/* EXTERNAL */(_xL/* Core.View.lvl27 */),
            _yL/* sfFo */ = _yK/* sfFm */,
            _yM/* sfJV */ = function(_/* EXTERNAL */){
              var _yN/* sfFr */ = nMV/* EXTERNAL */(_xL/* Core.View.lvl27 */),
              _yO/* sfFt */ = _yN/* sfFr */,
              _yP/* sfJT */ = function(_/* EXTERNAL */){
                var _yQ/* sfFw */ = nMV/* EXTERNAL */(_xL/* Core.View.lvl27 */),
                _yR/* sfFy */ = _yQ/* sfFw */,
                _yS/* sfJR */ = function(_/* EXTERNAL */){
                  var _yT/* sfFB */ = nMV/* EXTERNAL */(_xP/* Core.View.lvl30 */),
                  _yU/* sfFD */ = _yT/* sfFB */,
                  _yV/* sfJP */ = function(_/* EXTERNAL */){
                    var _yW/* sfFG */ = nMV/* EXTERNAL */(_xL/* Core.View.lvl27 */),
                    _yX/* sfFI */ = _yW/* sfFG */,
                    _yY/* sfFK */ = new T(function(){
                      var _yZ/* sfGx */ = function(_z0/* sfFL */, _z1/* sfFM */, _z2/* sfFN */, _z3/* sfFO */, _z4/* sfFP */, _z5/* sfFQ */){
                        var _z6/* sfFR */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yI/* sfFj */, _z0/* sfFL */));
                        }),
                        _z7/* sfFS */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yL/* sfFo */, _z1/* sfFM */));
                        }),
                        _z8/* sfFT */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yO/* sfFt */, _z2/* sfFN */));
                        }),
                        _z9/* sfFU */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yR/* sfFy */, _z3/* sfFO */));
                        }),
                        _za/* sfFV */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yU/* sfFD */, _z4/* sfFP */));
                        }),
                        _zb/* sfFW */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yX/* sfFI */, _z5/* sfFQ */));
                        }),
                        _zc/* sfGw */ = function(_zd/* sfFX */){
                          var _ze/* sfFY */ = new T(function(){
                            return B(A1(_z6/* sfFR */,_zd/* sfFX */));
                          }),
                          _zf/* sfGv */ = function(_zg/* sfFZ */){
                            var _zh/* sfG0 */ = function(_zi/* sfG1 */){
                              return new F(function(){return A1(_zg/* sfFZ */,new T2(0,_7/* GHC.Tuple.() */,E(_zi/* sfG1 */).b));});
                            },
                            _zj/* sfG6 */ = function(_zk/* sfG7 */){
                              return new F(function(){return A2(_zb/* sfFW */,E(_zk/* sfG7 */).b, _zh/* sfG0 */);});
                            },
                            _zl/* sfGb */ = function(_zm/* sfGc */){
                              return new F(function(){return A2(_za/* sfFV */,E(_zm/* sfGc */).b, _zj/* sfG6 */);});
                            },
                            _zn/* sfGg */ = function(_zo/* sfGh */){
                              return new F(function(){return A2(_z9/* sfFU */,E(_zo/* sfGh */).b, _zl/* sfGb */);});
                            },
                            _zp/* sfGl */ = function(_zq/* sfGm */){
                              return new F(function(){return A2(_z8/* sfFT */,E(_zq/* sfGm */).b, _zn/* sfGg */);});
                            };
                            return new F(function(){return A1(_ze/* sfFY */,function(_zr/* sfGq */){
                              return new F(function(){return A2(_z7/* sfFS */,E(_zr/* sfGq */).b, _zp/* sfGl */);});
                            });});
                          };
                          return E(_zf/* sfGv */);
                        };
                        return E(_zc/* sfGw */);
                      };
                      return B(_pg/* Control.Monad.Skeleton.bone */(new T2(2,_yZ/* sfGx */,_7/* GHC.Tuple.() */)));
                    }),
                    _zs/* sfGz */ = new T(function(){
                      var _zt/* sfGA */ = E(_y8/* sfEE */);
                      return new T2(0,E(_zt/* sfGA */.a),E(new T2(2,_zt/* sfGA */.b,new T1(1,function(_zu/* sfGD */){
                        return E(_yY/* sfFK */);
                      }))));
                    }),
                    _zv/* sfGH */ = new T(function(){
                      var _zw/* sfGY */ = B(_vV/* Core.Shape.Internal.$w$caffine */(new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yI/* sfFj */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yL/* sfFo */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yO/* sfFt */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yR/* sfFy */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yU/* sfFD */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yX/* sfFI */),_2E/* GHC.Base.id */), E(_y7/* sfED */).a));
                      return new T3(0,_zw/* sfGY */.a,_zw/* sfGY */.b,_zw/* sfGY */.c);
                    }),
                    _zx/* sfJN */ = function(_/* EXTERNAL */){
                      var _zy/* sfH3 */ = nMV/* EXTERNAL */(_xH/* Core.View.lvl24 */),
                      _zz/* sfH5 */ = _zy/* sfH3 */,
                      _zA/* sfJJ */ = new T(function(){
                        var _zB/* sfHT */ = function(_zC/* sfIr */){
                          return new F(function(){return _zD/* sfHS */(E(_zC/* sfIr */).b);});
                        },
                        _zE/* sfHV */ = function(_zF/* sfIz */){
                          var _zG/* sfIA */ = new T(function(){
                            return B(A2(_yE/* sfFd */,_zF/* sfIz */, _zH/* sfHU */));
                          }),
                          _zI/* sfIB */ = new T(function(){
                            return B(A2(_ys/* sfEV */,_zF/* sfIz */, _zB/* sfHT */));
                          }),
                          _zJ/* sfIC */ = new T(function(){
                            return B(A2(_yC/* sfFa */,_zF/* sfIz */, _zK/* sfHR */));
                          }),
                          _zL/* sfID */ = new T(function(){
                            return B(_zE/* sfHV */(_zF/* sfIz */));
                          }),
                          _zM/* sfIU */ = function(_zN/* sfIE */){
                            var _zO/* sfIF */ = E(_zN/* sfIE */);
                            if(!_zO/* sfIF */._){
                              return (!E(_zO/* sfIF */.a)) ? E(_zL/* sfID */) : E(_zJ/* sfIC */);
                            }else{
                              var _zP/* sfIT */ = function(_/* EXTERNAL */){
                                var _zQ/* sfIO */ = B(A2(E(_zv/* sfGH */).a,_zO/* sfIF */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_zQ/* sfIO */)){
                                    return E(_zI/* sfIB */);
                                  }else{
                                    return E(_zG/* sfIA */);
                                  }
                                });
                              };
                              return new T1(0,_zP/* sfIT */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zz/* sfH5 */, _zM/* sfIU */)));
                        },
                        _zH/* sfHU */ = function(_zR/* sfIv */){
                          return new F(function(){return _zE/* sfHV */(E(_zR/* sfIv */).b);});
                        },
                        _zD/* sfHS */ = function(_zS/* sfI6 */){
                          var _zT/* sfI7 */ = new T(function(){
                            return B(_zD/* sfHS */(_zS/* sfI6 */));
                          }),
                          _zU/* sfI8 */ = new T(function(){
                            return B(A2(_yu/* sfEY */,_zS/* sfI6 */, _zH/* sfHU */));
                          }),
                          _zV/* sfIo */ = function(_zW/* sfI9 */){
                            var _zX/* sfIa */ = E(_zW/* sfI9 */);
                            if(!_zX/* sfIa */._){
                              return E(_zT/* sfI7 */);
                            }else{
                              var _zY/* sfIn */ = function(_/* EXTERNAL */){
                                var _zZ/* sfIi */ = B(A2(E(_zv/* sfGH */).a,_zX/* sfIa */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_zZ/* sfIi */)){
                                    return E(_zT/* sfI7 */);
                                  }else{
                                    return E(_zU/* sfI8 */);
                                  }
                                });
                              };
                              return new T1(0,_zY/* sfIn */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zz/* sfH5 */, _zV/* sfIo */)));
                        },
                        _A0/* sfHW */ = function(_A1/* sfIX */){
                          var _A2/* sfIY */ = new T(function(){
                            return B(A2(_yw/* sfF1 */,_A1/* sfIX */, _zK/* sfHR */));
                          }),
                          _A3/* sfIZ */ = new T(function(){
                            return B(A2(_ys/* sfEV */,_A1/* sfIX */, _A4/* sfHQ */));
                          }),
                          _A5/* sfJ0 */ = new T(function(){
                            return B(_A0/* sfHW */(_A1/* sfIX */));
                          }),
                          _A6/* sfJ1 */ = new T(function(){
                            return B(A2(_yA/* sfF7 */,_A1/* sfIX */, _zH/* sfHU */));
                          }),
                          _A7/* sfJi */ = function(_A8/* sfJ2 */){
                            var _A9/* sfJ3 */ = E(_A8/* sfJ2 */);
                            if(!_A9/* sfJ3 */._){
                              return (!E(_A9/* sfJ3 */.a)) ? E(_A6/* sfJ1 */) : E(_A5/* sfJ0 */);
                            }else{
                              var _Aa/* sfJh */ = function(_/* EXTERNAL */){
                                var _Ab/* sfJc */ = B(A2(E(_zv/* sfGH */).a,_A9/* sfJ3 */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_Ab/* sfJc */)){
                                    return E(_A3/* sfIZ */);
                                  }else{
                                    return E(_A2/* sfIY */);
                                  }
                                });
                              };
                              return new T1(0,_Aa/* sfJh */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zz/* sfH5 */, _A7/* sfJi */)));
                        },
                        _zK/* sfHR */ = function(_Ac/* sfI2 */){
                          return new F(function(){return _A0/* sfHW */(E(_Ac/* sfI2 */).b);});
                        },
                        _Ad/* sfHX */ = function(_Ae/* sfJl */){
                          var _Af/* sfJm */ = new T(function(){
                            return B(A2(_yu/* sfEY */,_Ae/* sfJl */, _zK/* sfHR */));
                          }),
                          _Ag/* sfJn */ = new T(function(){
                            return B(A2(_yw/* sfF1 */,_Ae/* sfJl */, _A4/* sfHQ */));
                          }),
                          _Ah/* sfJo */ = new T(function(){
                            return B(_Ad/* sfHX */(_Ae/* sfJl */));
                          }),
                          _Ai/* sfJp */ = new T(function(){
                            return B(A2(_yy/* sfF4 */,_Ae/* sfJl */, _zB/* sfHT */));
                          }),
                          _Aj/* sfJG */ = function(_Ak/* sfJq */){
                            var _Al/* sfJr */ = E(_Ak/* sfJq */);
                            if(!_Al/* sfJr */._){
                              return (!E(_Al/* sfJr */.a)) ? E(_Ai/* sfJp */) : E(_Ah/* sfJo */);
                            }else{
                              var _Am/* sfJF */ = function(_/* EXTERNAL */){
                                var _An/* sfJA */ = B(A2(E(_zv/* sfGH */).a,_Al/* sfJr */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_An/* sfJA */)){
                                    return E(_Ag/* sfJn */);
                                  }else{
                                    return E(_Af/* sfJm */);
                                  }
                                });
                              };
                              return new T1(0,_Am/* sfJF */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zz/* sfH5 */, _Aj/* sfJG */)));
                        },
                        _A4/* sfHQ */ = function(_Ao/* sfHY */){
                          return new F(function(){return _Ad/* sfHX */(E(_Ao/* sfHY */).b);});
                        };
                        return B(_zD/* sfHS */(_yr/* sfEU */));
                      }),
                      _Ap/* sfHP */ = new T(function(){
                        var _Aq/* sfHO */ = function(_Ar/* sfHE */){
                          var _As/* sfHF */ = E(_Ar/* sfHE */);
                          return new F(function(){return A1(_ym/* sfEQ */,new T2(0,new T(function(){
                            return new T3(0,E(_As/* sfHF */.a),_zs/* sfGz */,E(_yq/* sfET */));
                          }),_As/* sfHF */.b));});
                        },
                        _At/* sfHD */ = function(_Au/* sfH7 */, _Av/* sfH8 */, _Aw/* sfH9 */){
                          var _Ax/* sfHa */ = new T(function(){
                            return E(E(_Au/* sfH7 */).d);
                          }),
                          _Ay/* sfHg */ = new T(function(){
                            return E(E(_Ax/* sfHa */).a);
                          }),
                          _Az/* sfHA */ = new T(function(){
                            var _AA/* sfHk */ = E(_Au/* sfH7 */);
                            return new T4(0,E(_AA/* sfHk */.a),_AA/* sfHk */.b,E(_AA/* sfHk */.c),E(new T2(0,new T(function(){
                              return E(_Ay/* sfHg */)+1|0;
                            }),new T(function(){
                              return B(_x6/* Data.IntMap.Strict.$winsert */(E(_Ay/* sfHg */), _zz/* sfH5 */, E(_Ax/* sfHa */).b));
                            }))));
                          });
                          return new F(function(){return A1(_Aw/* sfH9 */,new T2(0,new T2(0,_Ay/* sfHg */,_Az/* sfHA */),_Av/* sfH8 */));});
                        };
                        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _yr/* sfEU */, _At/* sfHD */, _yr/* sfEU */, _Aq/* sfHO */]));
                      });
                      return new T1(1,new T2(1,_Ap/* sfHP */,new T2(1,_zA/* sfJJ */,_6/* GHC.Types.[] */)));
                    };
                    return new T1(0,_zx/* sfJN */);
                  };
                  return new T1(0,_yV/* sfJP */);
                };
                return new T1(0,_yS/* sfJR */);
              };
              return new T1(0,_yP/* sfJT */);
            };
            return new T1(0,_yM/* sfJV */);
          };
          return new T1(0,_yJ/* sfJX */);
        };
        return new T1(0,_yG/* sfJZ */);
      };
      return new F(function(){return A1(_yk/* sfEP */,_yn/* sfK0 */);});
    };
    return E(_yl/* sfK1 */);
  };
  return E(_yi/* sfK2 */);
},
_AB/* $wconsView */ = function(_AC/* saJ2 */, _AD/* saJ3 */, _AE/* saJ4 */){
  var _AF/* saJ5 */ = new T(function(){
    var _AG/* saJc */ = new T(function(){
      return B(_ro/* Core.Render.Internal.fill1 */(_u5/* Motion.Main.lvl10 */, new T(function(){
        var _AH/* saJ7 */ = B(_qC/* Core.Shape.Internal.$wtext */(_u6/* Motion.Main.lvl11 */, new T1(0,_AE/* saJ4 */), _rl/* Core.Shape.Internal.LeftAlign */, _ri/* Core.Shape.Internal.BottomBase */, _vx/* Motion.Main.lvl14 */, _vA/* Motion.Main.lvl17 */, _vB/* Motion.Main.lvl18 */));
        return new T3(0,_AH/* saJ7 */.a,_AH/* saJ7 */.b,_AH/* saJ7 */.c);
      })));
    });
    return B(_pH/* Core.Render.Internal.$wshadowed */(_sA/* Motion.Main.lvl4 */, _vM/* Motion.Main.lvl5 */, _vO/* Motion.Main.lvl6 */, _vP/* Motion.Main.lvl8 */, _AG/* saJc */));
  }),
  _AI/* saJd */ = function(_AJ/* saJe */){
    return E(_AF/* saJ5 */);
  },
  _AK/* saJg */ = new T(function(){
    return B(A1(_AD/* saJ3 */,_AC/* saJ2 */));
  }),
  _AL/* saK1 */ = function(_AM/* saJh */){
    var _AN/* saJi */ = new T(function(){
      return B(A1(_AK/* saJg */,_AM/* saJh */));
    }),
    _AO/* saK0 */ = function(_AP/* saJj */){
      var _AQ/* saJZ */ = function(_AR/* saJk */){
        var _AS/* saJl */ = E(_AR/* saJk */),
        _AT/* saJo */ = E(_AS/* saJl */.a),
        _AU/* saJr */ = new T(function(){
          var _AV/* saJs */ = B(_tF/* Core.Render.Internal.clip */(_sD/* Motion.Main.shape */, _AT/* saJo */.a));
          return new T2(0,E(_AV/* saJs */.a),E(new T2(2,_AV/* saJs */.b,new T1(1,_AI/* saJd */))));
        }),
        _AW/* saJY */ = function(_/* EXTERNAL */){
          var _AX/* saJx */ = nMV/* EXTERNAL */(_vJ/* Motion.Main.lvl23 */);
          return new T(function(){
            var _AY/* saJB */ = new T(function(){
              return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _vK/* Motion.Main.lvl3 */, _u0/* Core.Ease.linear */, _AX/* saJx */, _vD/* Motion.Main.lvl2 */, _tT/* Core.Ease.easeTo1 */));
            }),
            _AZ/* saJC */ = new T(function(){
              return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _vK/* Motion.Main.lvl3 */, _u0/* Core.Ease.linear */, _AX/* saJx */, _vC/* Motion.Main.lvl19 */, _tT/* Core.Ease.easeTo1 */));
            }),
            _B0/* saJW */ = function(_B1/* saJN */){
              var _B2/* saJO */ = new T(function(){
                return B(_t0/* Core.UI.button */(_AY/* saJB */, _AZ/* saJC */, _sI/* Motion.Main.a21 */, _B1/* saJN */));
              }),
              _B3/* saJV */ = function(_B4/* saJP */, _B5/* saJQ */){
                return new T1(1,new T2(1,new T(function(){
                  return B(A2(_B2/* saJO */,_B4/* saJP */, _B5/* saJQ */));
                }),new T2(1,new T(function(){
                  return B(A2(_AT/* saJo */.b,_B4/* saJP */, _vE/* Motion.Main.lvl20 */));
                }),_6/* GHC.Types.[] */)));
              };
              return E(_B3/* saJV */);
            },
            _B6/* saJM */ = new T(function(){
              var _B7/* saJF */ = B(_pH/* Core.Render.Internal.$wshadowed */(_sA/* Motion.Main.lvl4 */, _vM/* Motion.Main.lvl5 */, new T2(2,new T3(0,_vK/* Motion.Main.lvl3 */,_u0/* Core.Ease.linear */,_AX/* saJx */),_2E/* GHC.Base.id */), _sM/* Core.Render.Internal.black */, _sH/* Motion.Main.a17 */));
              return new T2(0,E(_B7/* saJF */.a),E(new T2(2,_B7/* saJF */.b,new T1(1,function(_B8/* saJI */){
                return E(_AU/* saJr */);
              }))));
            });
            return B(A(_y5/* Core.View.makeView */,[_rj/* GHC.Base.Just */, _sD/* Motion.Main.shape */, _B6/* saJM */, _B0/* saJW */, _AS/* saJl */.b, _AP/* saJj */]));
          });
        };
        return new T1(0,_AW/* saJY */);
      };
      return new F(function(){return A1(_AN/* saJi */,_AQ/* saJZ */);});
    };
    return E(_AO/* saK0 */);
  };
  return E(_AL/* saK1 */);
},
_B9/* waitUntil2 */ = new T1(1,_6/* GHC.Types.[] */),
_Ba/* $wa6 */ = function(_Bb/* sbWf */, _Bc/* sbWg */, _Bd/* sbWh */){
  return function(_/* EXTERNAL */){
    var _Be/* sbWj */ = nMV/* EXTERNAL */(_B9/* Core.World.Internal.waitUntil2 */),
    _Bf/* sbWl */ = _Be/* sbWj */;
    return new T(function(){
      var _Bg/* sbWJ */ = function(_Bh/* sbWv */){
        var _Bi/* sbWz */ = new T(function(){
          return B(A1(_Bd/* sbWh */,new T2(0,_7/* GHC.Tuple.() */,E(_Bh/* sbWv */).b)));
        }),
        _Bj/* sbWB */ = function(_Bk/* sbWC */){
          return E(_Bi/* sbWz */);
        };
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Bf/* sbWl */, function(_Bl/* sbWD */){
          return new T1(0,B(_9p/* Haste.Concurrent.$wa */(_cp/* Core.World.Internal.switch2 */, _Bj/* sbWB */)));
        })));
      },
      _Bm/* sbWu */ = function(_Bn/* sbWn */, _Bo/* sbWo */){
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Bf/* sbWl */, _7/* GHC.Tuple.() */, function(_Bp/* sbWp */){
          return new F(function(){return A1(_Bo/* sbWo */,new T2(0,_Bp/* sbWp */,_Bn/* sbWn */));});
        })));
      };
      return B(A3(_Bb/* sbWf */,_Bm/* sbWu */, _Bc/* sbWg */, _Bg/* sbWJ */));
    });
  };
},
_Bq/* a */ = 100,
_Br/* a4 */ = function(_Bs/* s5eF */, _Bt/* s5eG */){
  var _Bu/* s5eM */ = B(A1(_Bs/* s5eF */,new T(function(){
    return 1-(1-E(_Bt/* s5eG */));
  })));
  return 1-(1-_Bu/* s5eM */*_Bu/* s5eM */);
},
_Bv/* dur */ = 20,
_Bw/* e */ = function(_Bx/* s5ev */, _By/* s5ew */){
  var _Bz/* s5eB */ = B(A1(_Bx/* s5ev */,new T(function(){
    return 1-E(_By/* s5ew */);
  })));
  return 1-_Bz/* s5eB */*_Bz/* s5eB */;
},
_BA/* lvl */ = 50,
_BB/* lvl1 */ = 3,
_BC/* lvl10 */ = function(_BD/* s5eR */){
  return  -E(_BD/* s5eR */);
},
_BE/* lvl9 */ = 0,
_BF/* lvl11 */ = new T4(0,_BE/* Motion.Bounce.lvl9 */,_BE/* Motion.Bounce.lvl9 */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_BG/* lvl12 */ = new T2(0,_BE/* Motion.Bounce.lvl9 */,_BF/* Motion.Bounce.lvl11 */),
_BH/* lvl13 */ = new T2(0,_BG/* Motion.Bounce.lvl12 */,_6/* GHC.Types.[] */),
_BI/* lvl14 */ = new T4(0,_Bq/* Motion.Bounce.a */,_Bq/* Motion.Bounce.a */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_BJ/* lvl15 */ = new T2(0,_Bq/* Motion.Bounce.a */,_BI/* Motion.Bounce.lvl14 */),
_BK/* lvl16 */ = new T2(0,_BJ/* Motion.Bounce.lvl15 */,_6/* GHC.Types.[] */),
_BL/* lvl2 */ = -30,
_BM/* lvl3 */ = 30,
_BN/* lvl4 */ = -10,
_BO/* lvl5 */ = 0,
_BP/* lvl6 */ = new T1(0,_Bq/* Motion.Bounce.a */),
_BQ/* a1 */ = 50,
_BR/* lvl7 */ = new T1(0,_BQ/* Motion.Bounce.a1 */),
_BS/* a2 */ = 75,
_BT/* lvl8 */ = new T1(0,_BS/* Motion.Bounce.a2 */),
_BU/* plusDouble */ = function(_BV/* s18yY */, _BW/* s18yZ */){
  return E(_BV/* s18yY */)+E(_BW/* s18yZ */);
},
_BX/* Zero */ = 0,
_BY/* sleep1 */ = function(_BZ/* sc1D */, _C0/* sc1E */, _C1/* sc1F */){
  var _C2/* sc3v */ = function(_C3/* sc1G */){
    var _C4/* sc1H */ = E(_C3/* sc1G */),
    _C5/* sc1J */ = _C4/* sc1H */.b,
    _C6/* sc1K */ = new T(function(){
      return E(_C4/* sc1H */.a)+E(_BZ/* sc1D */)|0;
    }),
    _C7/* sc3u */ = function(_/* EXTERNAL */){
      var _C8/* sc1R */ = nMV/* EXTERNAL */(_B9/* Core.World.Internal.waitUntil2 */),
      _C9/* sc1T */ = _C8/* sc1R */;
      return new T(function(){
        var _Ca/* sc3s */ = function(_Cb/* sc3i */){
          var _Cc/* sc3m */ = new T(function(){
            return B(A1(_C1/* sc1F */,new T2(0,_7/* GHC.Tuple.() */,E(_Cb/* sc3i */).b)));
          });
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_C9/* sc1T */, function(_Cd/* sc3o */){
            return E(_Cc/* sc3m */);
          })));
        },
        _Ce/* sc1V */ = new T2(0,_C6/* sc1K */,_C9/* sc1T */),
        _Cf/* sc3h */ = function(_Cg/* sc1X */){
          var _Ch/* sc1Y */ = new T(function(){
            var _Ci/* sc1Z */ = E(_Cg/* sc1X */),
            _Cj/* sc24 */ = E(_Ci/* sc1Z */.c);
            if(!_Cj/* sc24 */._){
              var _Ck/* sc24#result */ = E(new T3(1,1,_Ce/* sc1V */,E(_aC/* Data.PQueue.Internals.Nil */)));
            }else{
              var _Cl/* sc25 */ = _Cj/* sc24 */.a,
              _Cm/* sc27 */ = _Cj/* sc24 */.c,
              _Cn/* sc28 */ = E(_Cj/* sc24 */.b),
              _Co/* sc2b */ = E(_C6/* sc1K */),
              _Cp/* sc2d */ = E(_Cn/* sc28 */.a);
              if(_Co/* sc2b */>=_Cp/* sc2d */){
                if(_Co/* sc2b */!=_Cp/* sc2d */){
                  var _Cq/* sc2i#result */ = new T3(1,_Cl/* sc25 */+1|0,_Cn/* sc28 */,E(B(_aD/* Data.PQueue.Internals.$wincr */(function(_Cr/* sc2j */, _Cs/* sc2k */){
                    var _Ct/* sc2r */ = E(E(_Cr/* sc2j */).a),
                    _Cu/* sc2t */ = E(E(_Cs/* sc2k */).a);
                    return (_Ct/* sc2r */>=_Cu/* sc2t */) ? _Ct/* sc2r */==_Cu/* sc2t */ : true;
                  }, _Ce/* sc1V */, _BX/* Data.PQueue.Internals.Zero */, _Cm/* sc27 */))));
                }else{
                  var _Cq/* sc2i#result */ = new T3(1,_Cl/* sc25 */+1|0,_Ce/* sc1V */,E(B(_aD/* Data.PQueue.Internals.$wincr */(function(_Cv/* sc2B */, _Cw/* sc2C */){
                    var _Cx/* sc2J */ = E(E(_Cv/* sc2B */).a),
                    _Cy/* sc2L */ = E(E(_Cw/* sc2C */).a);
                    return (_Cx/* sc2J */>=_Cy/* sc2L */) ? _Cx/* sc2J */==_Cy/* sc2L */ : true;
                  }, _Cn/* sc28 */, _BX/* Data.PQueue.Internals.Zero */, _Cm/* sc27 */))));
                }
                var _Cz/* sc2g#result */ = _Cq/* sc2i#result */;
              }else{
                var _Cz/* sc2g#result */ = new T3(1,_Cl/* sc25 */+1|0,_Ce/* sc1V */,E(B(_aD/* Data.PQueue.Internals.$wincr */(function(_CA/* sc2T */, _CB/* sc2U */){
                  var _CC/* sc31 */ = E(E(_CA/* sc2T */).a),
                  _CD/* sc33 */ = E(E(_CB/* sc2U */).a);
                  return (_CC/* sc31 */>=_CD/* sc33 */) ? _CC/* sc31 */==_CD/* sc33 */ : true;
                }, _Cn/* sc28 */, _BX/* Data.PQueue.Internals.Zero */, _Cm/* sc27 */))));
              }
              var _Ck/* sc24#result */ = _Cz/* sc2g#result */;
            }
            return new T4(0,E(_Ci/* sc1Z */.a),_Ci/* sc1Z */.b,E(_Ck/* sc24#result */),E(_Ci/* sc1Z */.d));
          });
          return function(_CE/* sc3d */, _CF/* sc3e */){
            return new F(function(){return A1(_CF/* sc3e */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,_Ch/* sc1Y */),_CE/* sc3d */));});
          };
        };
        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _C5/* sc1J */, _Cf/* sc3h */, _C5/* sc1J */, _Ca/* sc3s */]));
      });
    };
    return new T1(0,_C7/* sc3u */);
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _C0/* sc1E */, _ar/* Core.World.Internal.a3 */, _C0/* sc1E */, _C2/* sc3v */]);});
},
_CG/* $wa */ = function(_CH/* s5eV */, _CI/* s5eW */, _CJ/* s5eX */){
  return function(_/* EXTERNAL */){
    var _CK/* s5eZ */ = nMV/* EXTERNAL */(_BK/* Motion.Bounce.lvl16 */),
    _CL/* s5f1 */ = _CK/* s5eZ */,
    _CM/* s5f3 */ = function(_CN/* s5f4 */){
      return new F(function(){return _iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Bv/* Motion.Bounce.dur */, _Br/* Motion.Bounce.a4 */, _CL/* s5f1 */, _Bq/* Motion.Bounce.a */, function(_CO/* s5f5 */){
        return E(_CN/* s5f4 */);
      });});
    },
    _CP/* s5f7 */ = function(_CQ/* s5f8 */){
      return new F(function(){return _iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Bv/* Motion.Bounce.dur */, _Bw/* Motion.Bounce.e */, _CL/* s5f1 */, _BM/* Motion.Bounce.lvl3 */, function(_CR/* s5f9 */){
        return E(_CQ/* s5f8 */);
      });});
    },
    _CS/* s5mL */ = function(_/* EXTERNAL */){
      var _CT/* s5fc */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
      _CU/* s5fe */ = _CT/* s5fc */,
      _CV/* s5fg */ = new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_CU/* s5fe */),
      _CW/* s5mJ */ = function(_/* EXTERNAL */){
        var _CX/* s5fi */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
        _CY/* s5fk */ = _CX/* s5fi */,
        _CZ/* s5mH */ = function(_/* EXTERNAL */){
          var _D0/* s5fn */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
          _D1/* s5fp */ = _D0/* s5fn */,
          _D2/* s5fr */ = new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_D1/* s5fp */),
          _D3/* s5mF */ = function(_/* EXTERNAL */){
            var _D4/* s5ft */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
            _D5/* s5fv */ = _D4/* s5ft */,
            _D6/* s5mD */ = function(_/* EXTERNAL */){
              var _D7/* s5fy */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
              _D8/* s5fA */ = _D7/* s5fy */,
              _D9/* s5mB */ = function(_/* EXTERNAL */){
                var _Da/* s5fD */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                _Db/* s5fF */ = _Da/* s5fD */,
                _Dc/* s5mz */ = function(_/* EXTERNAL */){
                  var _Dd/* s5fI */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                  _De/* s5fK */ = _Dd/* s5fI */,
                  _Df/* s5fM */ = new T(function(){
                    return B(_wJ/* Core.Ease.$wforceTo */(_De/* s5fK */, _BL/* Motion.Bounce.lvl2 */));
                  }),
                  _Dg/* s5mx */ = function(_/* EXTERNAL */){
                    var _Dh/* s5fO */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                    _Di/* s5fQ */ = _Dh/* s5fO */,
                    _Dj/* s5mv */ = function(_/* EXTERNAL */){
                      var _Dk/* s5fT */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                      _Dl/* s5fV */ = _Dk/* s5fT */,
                      _Dm/* s5fX */ = new T(function(){
                        return B(_wJ/* Core.Ease.$wforceTo */(_Dl/* s5fV */, _BB/* Motion.Bounce.lvl1 */));
                      }),
                      _Dn/* s5mt */ = function(_/* EXTERNAL */){
                        var _Do/* s5fZ */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                        _Dp/* s5g1 */ = _Do/* s5fZ */,
                        _Dq/* s5g3 */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_Dp/* s5g1 */, _BB/* Motion.Bounce.lvl1 */));
                        }),
                        _Dr/* s5mr */ = function(_/* EXTERNAL */){
                          var _Ds/* s5g5 */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                          _Dt/* s5g7 */ = _Ds/* s5g5 */,
                          _Du/* s5mp */ = function(_/* EXTERNAL */){
                            var _Dv/* s5ga */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                            _Dw/* s5gc */ = _Dv/* s5ga */;
                            return new T(function(){
                              var _Dx/* s5gf */ = function(_Dy/* s5gk */){
                                return new F(function(){return _Dz/* s5gh */(E(_Dy/* s5gk */).b);});
                              },
                              _DA/* s5gg */ = function(_DB/* s5go */){
                                return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_BO/* Motion.Bounce.lvl5 */, E(_DB/* s5go */).b, _Dx/* s5gf */);});
                              },
                              _Dz/* s5gh */ = function(_DC/* s5gs */){
                                var _DD/* s5l7 */ = function(_DE/* s5gt */){
                                  var _DF/* s5gu */ = new T(function(){
                                    var _DG/* s5l0 */ = function(_DH/* s5gv */){
                                      var _DI/* s5gw */ = new T(function(){
                                        var _DJ/* s5kT */ = function(_DK/* s5gx */){
                                          var _DL/* s5gy */ = new T(function(){
                                            var _DM/* s5kM */ = function(_DN/* s5gz */){
                                              var _DO/* s5gA */ = new T(function(){
                                                var _DP/* s5kF */ = function(_DQ/* s5gB */){
                                                  var _DR/* s5gC */ = new T(function(){
                                                    var _DS/* s5gD */ = new T(function(){
                                                      return E(E(_DQ/* s5gB */).a);
                                                    }),
                                                    _DT/* s5gH */ = new T(function(){
                                                      return B(_wJ/* Core.Ease.$wforceTo */(_CU/* s5fe */, new T(function(){
                                                        return (E(E(_DE/* s5gt */).a)+E(_DS/* s5gD */))*0.7;
                                                      })));
                                                    }),
                                                    _DU/* s5ky */ = function(_DV/* s5gS */){
                                                      var _DW/* s5gT */ = new T(function(){
                                                        var _DX/* s5gU */ = new T(function(){
                                                          return E(E(_DV/* s5gS */).a);
                                                        }),
                                                        _DY/* s5gY */ = new T(function(){
                                                          return B(_wJ/* Core.Ease.$wforceTo */(_CY/* s5fk */, new T(function(){
                                                            return (E(E(_DH/* s5gv */).a)+E(_DX/* s5gU */))*0.7;
                                                          })));
                                                        }),
                                                        _DZ/* s5kr */ = function(_E0/* s5h9 */){
                                                          var _E1/* s5ha */ = new T(function(){
                                                            var _E2/* s5hb */ = new T(function(){
                                                              return E(E(_E0/* s5h9 */).a);
                                                            }),
                                                            _E3/* s5hf */ = new T(function(){
                                                              return B(_wJ/* Core.Ease.$wforceTo */(_D1/* s5fp */, new T(function(){
                                                                return (E(E(_DK/* s5gx */).a)+E(_E2/* s5hb */))*0.7;
                                                              })));
                                                            }),
                                                            _E4/* s5kk */ = function(_E5/* s5hq */){
                                                              var _E6/* s5hr */ = new T(function(){
                                                                var _E7/* s5hs */ = new T(function(){
                                                                  return E(E(_E5/* s5hq */).a);
                                                                }),
                                                                _E8/* s5hw */ = new T(function(){
                                                                  return B(_wJ/* Core.Ease.$wforceTo */(_D5/* s5fv */, new T(function(){
                                                                    return (E(E(_DN/* s5gz */).a)+E(_E7/* s5hs */))*0.7;
                                                                  })));
                                                                }),
                                                                _E9/* s5hH */ = function(_Ea/* s5hI */){
                                                                  return new F(function(){return A2(_E8/* s5hw */,E(_Ea/* s5hI */).b, _DA/* s5gg */);});
                                                                },
                                                                _Eb/* s5hM */ = function(_Ec/* s5hN */){
                                                                  return new F(function(){return A2(_E3/* s5hf */,E(_Ec/* s5hN */).b, _E9/* s5hH */);});
                                                                },
                                                                _Ed/* s5hR */ = function(_Ee/* s5hS */){
                                                                  return new F(function(){return A2(_DY/* s5gY */,E(_Ee/* s5hS */).b, _Eb/* s5hM */);});
                                                                },
                                                                _Ef/* s5hW */ = function(_Eg/* s5hX */){
                                                                  return new F(function(){return A2(_DT/* s5gH */,E(_Eg/* s5hX */).b, _Ed/* s5hR */);});
                                                                },
                                                                _Eh/* s5kd */ = function(_Ei/* s5i1 */){
                                                                  var _Ej/* s5i2 */ = new T(function(){
                                                                    var _Ek/* s5i3 */ = new T(function(){
                                                                      return E(E(_Ei/* s5i1 */).a);
                                                                    }),
                                                                    _El/* s5i7 */ = new T(function(){
                                                                      return B(_wJ/* Core.Ease.$wforceTo */(_Dl/* s5fV */, new T(function(){
                                                                        return E(_Ek/* s5i3 */)*0.7;
                                                                      })));
                                                                    }),
                                                                    _Em/* s5ic */ = new T(function(){
                                                                      return B(_wJ/* Core.Ease.$wforceTo */(_D8/* s5fA */, new T(function(){
                                                                        return (E(_DS/* s5gD */)+E(_Ek/* s5i3 */))*0.7;
                                                                      })));
                                                                    }),
                                                                    _En/* s5k6 */ = function(_Eo/* s5ik */){
                                                                      var _Ep/* s5il */ = new T(function(){
                                                                        var _Eq/* s5im */ = new T(function(){
                                                                          return E(E(_Eo/* s5ik */).a);
                                                                        }),
                                                                        _Er/* s5iq */ = new T(function(){
                                                                          return B(_wJ/* Core.Ease.$wforceTo */(_Dp/* s5g1 */, new T(function(){
                                                                            return E(_Eq/* s5im */)*0.7;
                                                                          })));
                                                                        }),
                                                                        _Es/* s5iv */ = new T(function(){
                                                                          return B(_wJ/* Core.Ease.$wforceTo */(_Db/* s5fF */, new T(function(){
                                                                            return (E(_DX/* s5gU */)+E(_Eq/* s5im */))*0.7;
                                                                          })));
                                                                        }),
                                                                        _Et/* s5jZ */ = function(_Eu/* s5iD */){
                                                                          var _Ev/* s5iE */ = new T(function(){
                                                                            var _Ew/* s5iF */ = new T(function(){
                                                                              return E(E(_Eu/* s5iD */).a);
                                                                            }),
                                                                            _Ex/* s5iJ */ = new T(function(){
                                                                              return B(_wJ/* Core.Ease.$wforceTo */(_Dt/* s5g7 */, new T(function(){
                                                                                return E(_Ew/* s5iF */)*0.7;
                                                                              })));
                                                                            }),
                                                                            _Ey/* s5iO */ = new T(function(){
                                                                              return B(_wJ/* Core.Ease.$wforceTo */(_De/* s5fK */, new T(function(){
                                                                                return (E(_E2/* s5hb */)+E(_Ew/* s5iF */))*0.7;
                                                                              })));
                                                                            }),
                                                                            _Ez/* s5jS */ = function(_EA/* s5iW */){
                                                                              var _EB/* s5iX */ = new T(function(){
                                                                                var _EC/* s5iY */ = new T(function(){
                                                                                  return E(E(_EA/* s5iW */).a);
                                                                                }),
                                                                                _ED/* s5j2 */ = new T(function(){
                                                                                  return B(_wJ/* Core.Ease.$wforceTo */(_Dw/* s5gc */, new T(function(){
                                                                                    return E(_EC/* s5iY */)*0.7;
                                                                                  })));
                                                                                }),
                                                                                _EE/* s5j7 */ = new T(function(){
                                                                                  return B(_wJ/* Core.Ease.$wforceTo */(_Di/* s5fQ */, new T(function(){
                                                                                    return (E(_E7/* s5hs */)+E(_EC/* s5iY */))*0.7;
                                                                                  })));
                                                                                }),
                                                                                _EF/* s5jf */ = function(_EG/* s5jg */){
                                                                                  return new F(function(){return A2(_EE/* s5j7 */,E(_EG/* s5jg */).b, _Ef/* s5hW */);});
                                                                                },
                                                                                _EH/* s5jk */ = function(_EI/* s5jl */){
                                                                                  return new F(function(){return A2(_Ey/* s5iO */,E(_EI/* s5jl */).b, _EF/* s5jf */);});
                                                                                },
                                                                                _EJ/* s5jp */ = function(_EK/* s5jq */){
                                                                                  return new F(function(){return A2(_Es/* s5iv */,E(_EK/* s5jq */).b, _EH/* s5jk */);});
                                                                                },
                                                                                _EL/* s5ju */ = function(_EM/* s5jv */){
                                                                                  return new F(function(){return A2(_Em/* s5ic */,E(_EM/* s5jv */).b, _EJ/* s5jp */);});
                                                                                },
                                                                                _EN/* s5jz */ = function(_EO/* s5jA */){
                                                                                  return new F(function(){return A2(_ED/* s5j2 */,E(_EO/* s5jA */).b, _EL/* s5ju */);});
                                                                                },
                                                                                _EP/* s5jE */ = function(_EQ/* s5jF */){
                                                                                  return new F(function(){return A2(_Ex/* s5iJ */,E(_EQ/* s5jF */).b, _EN/* s5jz */);});
                                                                                };
                                                                                return B(A2(_El/* s5i7 */,_DC/* s5gs */, function(_ER/* s5jJ */){
                                                                                  return new F(function(){return A2(_Er/* s5iq */,E(_ER/* s5jJ */).b, _EP/* s5jE */);});
                                                                                }));
                                                                              });
                                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Dw/* s5gc */, _EA/* s5iW */, function(_ES/* s5jO */){
                                                                                return E(_EB/* s5iX */);
                                                                              })));
                                                                            };
                                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Dw/* s5gc */, _Ez/* s5jS */)));
                                                                          });
                                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Dt/* s5g7 */, _Eu/* s5iD */, function(_ET/* s5jV */){
                                                                            return E(_Ev/* s5iE */);
                                                                          })));
                                                                        };
                                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Dt/* s5g7 */, _Et/* s5jZ */)));
                                                                      });
                                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Dp/* s5g1 */, _Eo/* s5ik */, function(_EU/* s5k2 */){
                                                                        return E(_Ep/* s5il */);
                                                                      })));
                                                                    };
                                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Dp/* s5g1 */, _En/* s5k6 */)));
                                                                  });
                                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Dl/* s5fV */, _Ei/* s5i1 */, function(_EV/* s5k9 */){
                                                                    return E(_Ej/* s5i2 */);
                                                                  })));
                                                                };
                                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Dl/* s5fV */, _Eh/* s5kd */)));
                                                              });
                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Di/* s5fQ */, _E5/* s5hq */, function(_EW/* s5kg */){
                                                                return E(_E6/* s5hr */);
                                                              })));
                                                            };
                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Di/* s5fQ */, _E4/* s5kk */)));
                                                          });
                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_De/* s5fK */, _E0/* s5h9 */, function(_EX/* s5kn */){
                                                            return E(_E1/* s5ha */);
                                                          })));
                                                        };
                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_De/* s5fK */, _DZ/* s5kr */)));
                                                      });
                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Db/* s5fF */, _DV/* s5gS */, function(_EY/* s5ku */){
                                                        return E(_DW/* s5gT */);
                                                      })));
                                                    };
                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Db/* s5fF */, _DU/* s5ky */)));
                                                  });
                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_D8/* s5fA */, _DQ/* s5gB */, function(_EZ/* s5kB */){
                                                    return E(_DR/* s5gC */);
                                                  })));
                                                };
                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_D8/* s5fA */, _DP/* s5kF */)));
                                              });
                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_D5/* s5fv */, _DN/* s5gz */, function(_F0/* s5kI */){
                                                return E(_DO/* s5gA */);
                                              })));
                                            };
                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_D5/* s5fv */, _DM/* s5kM */)));
                                          });
                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_D1/* s5fp */, _DK/* s5gx */, function(_F1/* s5kP */){
                                            return E(_DL/* s5gy */);
                                          })));
                                        };
                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_D1/* s5fp */, _DJ/* s5kT */)));
                                      });
                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_CY/* s5fk */, _DH/* s5gv */, function(_F2/* s5kW */){
                                        return E(_DI/* s5gw */);
                                      })));
                                    };
                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_CY/* s5fk */, _DG/* s5l0 */)));
                                  });
                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_CU/* s5fe */, _DE/* s5gt */, function(_F3/* s5l3 */){
                                    return E(_DF/* s5gu */);
                                  })));
                                };
                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_CU/* s5fe */, _DD/* s5l7 */)));
                              },
                              _F4/* s5la */ = new T(function(){
                                return B(_wJ/* Core.Ease.$wforceTo */(_Dw/* s5gc */, _BN/* Motion.Bounce.lvl4 */));
                              }),
                              _F5/* s5lc */ = function(_F6/* s5lm */){
                                return new F(function(){return _F7/* s5lj */(E(_F6/* s5lm */).b);});
                              },
                              _F8/* s5ld */ = function(_F9/* s5lq */){
                                return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_BA/* Motion.Bounce.lvl */, E(_F9/* s5lq */).b, _F5/* s5lc */);});
                              },
                              _Fa/* s5le */ = function(_Fb/* s5lu */){
                                return new F(function(){return A2(_Dq/* s5g3 */,E(_Fb/* s5lu */).b, _F8/* s5ld */);});
                              },
                              _Fc/* s5lf */ = function(_Fd/* s5ly */){
                                return new F(function(){return A2(_Dm/* s5fX */,E(_Fd/* s5ly */).b, _Fa/* s5le */);});
                              },
                              _Fe/* s5lg */ = function(_Ff/* s5lC */){
                                return new F(function(){return A2(_Df/* s5fM */,E(_Ff/* s5lC */).b, _Fc/* s5lf */);});
                              },
                              _Fg/* s5lh */ = function(_Fh/* s5lG */){
                                return new T1(0,B(_Ba/* Core.World.Internal.$wa6 */(_CM/* s5f3 */, E(_Fh/* s5lG */).b, _Fe/* s5lg */)));
                              },
                              _Fi/* s5li */ = function(_Fj/* s5lM */){
                                return new T1(0,B(_Ba/* Core.World.Internal.$wa6 */(_CP/* s5f7 */, E(_Fj/* s5lM */).b, _Fg/* s5lh */)));
                              },
                              _F7/* s5lj */ = function(_Fk/* s5lS */){
                                return new F(function(){return A2(_F4/* s5la */,_Fk/* s5lS */, _Fi/* s5li */);});
                              },
                              _Fl/* s5ml */ = function(_Fm/* s5mf */, _Fn/* s5mg */){
                                return new T1(1,new T2(1,new T(function(){
                                  return B(_F7/* s5lj */(_Fm/* s5mf */));
                                }),new T2(1,new T(function(){
                                  return B(_Dz/* s5gh */(_Fm/* s5mf */));
                                }),_6/* GHC.Types.[] */)));
                              },
                              _Fo/* s5me */ = new T(function(){
                                var _Fp/* s5md */ = new T(function(){
                                  var _Fq/* s5m9 */ = B(_rM/* Core.Shape.Internal.$wrect */(new T(function(){
                                    return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, _BT/* Motion.Bounce.lvl8 */, new T2(2,_CV/* s5fg */,_BC/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, new T2(2,new T3(0,_Bv/* Motion.Bounce.dur */,_Bw/* Motion.Bounce.e */,_CL/* s5f1 */),_2E/* GHC.Base.id */), new T2(2,_D2/* s5fr */,_BC/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, _BR/* Motion.Bounce.lvl7 */, new T2(2,_CV/* s5fg */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_CY/* s5fk */),_2E/* GHC.Base.id */)));
                                  }), new T(function(){
                                    return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, _BP/* Motion.Bounce.lvl6 */, new T2(2,_D2/* s5fr */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_D5/* s5fv */),_2E/* GHC.Base.id */)));
                                  })));
                                  return new T3(0,_Fq/* s5m9 */.a,_Fq/* s5m9 */.b,_Fq/* s5m9 */.c);
                                });
                                return B(_ro/* Core.Render.Internal.fill1 */(_CH/* s5eV */, _Fp/* s5md */));
                              });
                              return B(A1(_CJ/* s5eX */,new T2(0,new T2(0,_Fo/* s5me */,_Fl/* s5ml */),_CI/* s5eW */)));
                            });
                          };
                          return new T1(0,_Du/* s5mp */);
                        };
                        return new T1(0,_Dr/* s5mr */);
                      };
                      return new T1(0,_Dn/* s5mt */);
                    };
                    return new T1(0,_Dj/* s5mv */);
                  };
                  return new T1(0,_Dg/* s5mx */);
                };
                return new T1(0,_Dc/* s5mz */);
              };
              return new T1(0,_D9/* s5mB */);
            };
            return new T1(0,_D6/* s5mD */);
          };
          return new T1(0,_D3/* s5mF */);
        };
        return new T1(0,_CZ/* s5mH */);
      };
      return new T1(0,_CW/* s5mJ */);
    };
    return new T1(0,_CS/* s5mL */);
  };
},
_Fr/* bounceMot1 */ = function(_Fs/* s5mO */, _Ft/* s5mP */, _Fu/* s5mQ */){
  return new T1(0,B(_CG/* Motion.Bounce.$wa */(_Fs/* s5mO */, _Ft/* s5mP */, _Fu/* s5mQ */)));
},
_Fv/* lvl24 */ = 0.3,
_Fw/* lvl25 */ = new T1(0,_Fv/* Motion.Main.lvl24 */),
_Fx/* lvl26 */ = new T4(0,_sA/* Motion.Main.lvl4 */,_Fw/* Motion.Main.lvl25 */,_u4/* Motion.Main.lvl9 */,_u4/* Motion.Main.lvl9 */),
_Fy/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bounce"));
}),
_Fz/* lvl28 */ = new T(function(){
  return B(_AB/* Motion.Main.$wconsView */(_Fx/* Motion.Main.lvl26 */, _Fr/* Motion.Bounce.bounceMot1 */, _Fy/* Motion.Main.lvl27 */));
}),
_FA/* negateDouble */ = function(_FB/* s18yz */){
  return  -E(_FB/* s18yz */);
},
_FC/* $fAffineRender1 */ = function(_FD/* sbR4 */, _FE/* sbR5 */, _FF/* sbR6 */, _FG/* sbR7 */){
  var _FH/* sbSb */ = new T(function(){
    var _FI/* sbS9 */ = new T(function(){
      var _FJ/* sbS6 */ = new T(function(){
        var _FK/* sbRD */ = E(_FF/* sbR6 */);
        switch(_FK/* sbRD */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_FK/* sbRD */.a);
            }));
            break;
          case 1:
            var _FL/* sbRP */ = function(_/* EXTERNAL */){
              var _FM/* sbRL */ = B(A1(_FK/* sbRD */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_FA/* GHC.Float.negateDouble */(_FM/* sbRL */));
              });
            };
            return new T1(1,_FL/* sbRP */);
            break;
          case 2:
            return new T2(2,_FK/* sbRD */.a,function(_FN/* sbRS */){
              return  -B(A1(_FK/* sbRD */.b,_FN/* sbRS */));
            });
            break;
          default:
            var _FO/* sbS5 */ = function(_FP/* sbRZ */, _/* EXTERNAL */){
              var _FQ/* sbS1 */ = B(A2(_FK/* sbRD */.b,_FP/* sbRZ */, _/* EXTERNAL */));
              return new T(function(){
                return B(_FA/* GHC.Float.negateDouble */(_FQ/* sbS1 */));
              });
            };
            return new T2(3,_FK/* sbRD */.a,_FO/* sbS5 */);
        }
      }),
      _FR/* sbRC */ = new T(function(){
        var _FS/* sbR9 */ = E(_FE/* sbR5 */);
        switch(_FS/* sbR9 */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_FS/* sbR9 */.a);
            }));
            break;
          case 1:
            var _FT/* sbRl */ = function(_/* EXTERNAL */){
              var _FU/* sbRh */ = B(A1(_FS/* sbR9 */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_FA/* GHC.Float.negateDouble */(_FU/* sbRh */));
              });
            };
            return new T1(1,_FT/* sbRl */);
            break;
          case 2:
            return new T2(2,_FS/* sbR9 */.a,function(_FV/* sbRo */){
              return  -B(A1(_FS/* sbR9 */.b,_FV/* sbRo */));
            });
            break;
          default:
            var _FW/* sbRB */ = function(_FX/* sbRv */, _/* EXTERNAL */){
              var _FY/* sbRx */ = B(A2(_FS/* sbR9 */.b,_FX/* sbRv */, _/* EXTERNAL */));
              return new T(function(){
                return B(_FA/* GHC.Float.negateDouble */(_FY/* sbRx */));
              });
            };
            return new T2(3,_FS/* sbR9 */.a,_FW/* sbRB */);
        }
      });
      return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_FR/* sbRC */,_FJ/* sbS6 */),_FG/* sbR7 */,_7/* GHC.Tuple.() */)));
    });
    return B(_pg/* Control.Monad.Skeleton.bone */(new T3(7,_FD/* sbR4 */,_FI/* sbS9 */,_7/* GHC.Tuple.() */)));
  });
  return new F(function(){return _pg/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_FE/* sbR5 */,_FF/* sbR6 */),_FH/* sbSb */,_7/* GHC.Tuple.() */));});
},
_FZ/* lvl */ = 0,
_G0/* lvl1 */ = 20,
_G1/* lvl2 */ = 0.9999999999999998,
_G2/* lvl3 */ = new T4(0,_FZ/* Motion.Grow.lvl */,_FZ/* Motion.Grow.lvl */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_G3/* lvl4 */ = new T2(0,_FZ/* Motion.Grow.lvl */,_G2/* Motion.Grow.lvl3 */),
_G4/* lvl5 */ = new T2(0,_G3/* Motion.Grow.lvl4 */,_6/* GHC.Types.[] */),
_G5/* $wa1 */ = function(_G6/* s7gN */, _G7/* s7gO */, _G8/* s7gP */){
  return function(_/* EXTERNAL */){
    var _G9/* s7gR */ = nMV/* EXTERNAL */(_G4/* Motion.Grow.lvl5 */);
    return new T(function(){
      var _Ga/* s7gU */ = function(_Gb/* s7gV */, _Gc/* s7gW */){
        return 1-B(A1(_Gb/* s7gV */,new T(function(){
          var _Gd/* s7gZ */ = E(_Gc/* s7gW */)/0.3-_G6/* s7gN *//4*2.3333333333333335;
          if(1>_Gd/* s7gZ */){
            if(0>_Gd/* s7gZ */){
              return E(_G1/* Motion.Grow.lvl2 */);
            }else{
              var _Ge/* s7h8 */ = 1-_Gd/* s7gZ */;
              return _Ge/* s7h8 */*_Ge/* s7h8 */*(2.70158*_Ge/* s7h8 */-1.70158);
            }
          }else{
            return E(_FZ/* Motion.Grow.lvl */);
          }
        })));
      },
      _Gf/* s7hl */ = new T3(0,_G0/* Motion.Grow.lvl1 */,function(_Gg/* s7hh */, _Gh/* s7hi */){
        return new F(function(){return _Ga/* s7gU */(_Gg/* s7hh */, _Gh/* s7hi */);});
      },_G9/* s7gR */),
      _Gi/* s7hm */ = E(_G6/* s7gN */);
      if(_Gi/* s7hm */==4){
        return B(A1(_G8/* s7gP */,new T2(0,new T2(1,_Gf/* s7hl */,_6/* GHC.Types.[] */),_G7/* s7gO */)));
      }else{
        return new T1(0,B(_G5/* Motion.Grow.$wa1 */(_Gi/* s7hm */+1|0, _G7/* s7gO */, function(_Gj/* s7ho */){
          var _Gk/* s7hp */ = E(_Gj/* s7ho */);
          return new F(function(){return A1(_G8/* s7gP */,new T2(0,new T2(1,_Gf/* s7hl */,_Gk/* s7hp */.a),_Gk/* s7hp */.b));});
        })));
      }
    });
  };
},
_Gl/* $wcenterRect */ = function(_Gm/* skho */, _Gn/* skhp */, _Go/* skhq */, _Gp/* skhr */){
  var _Gq/* skjx */ = function(_Gr/* skik */, _Gs/* skil */, _Gt/* skim */, _/* EXTERNAL */){
    var _Gu/* skjw */ = function(_Gv/* skio */, _Gw/* skip */, _Gx/* skiq */, _/* EXTERNAL */){
      var _Gy/* skjv */ = function(_Gz/* skis */){
        var _GA/* skit */ = new T(function(){
          return E(_Gz/* skis */)/2;
        }),
        _GB/* skju */ = function(_GC/* skix */, _GD/* skiy */, _GE/* skiz */, _/* EXTERNAL */){
          var _GF/* skiB */ = E(_Gr/* skik */),
          _GG/* skiD */ = E(_GA/* skit */),
          _GH/* skiF */ = _GF/* skiB */+_GG/* skiD */,
          _GI/* skiL */ = _GF/* skiB */-_GG/* skiD */,
          _GJ/* skiO */ = E(_Gv/* skio */),
          _GK/* skiS */ = E(_GC/* skix */)/2,
          _GL/* skiW */ = _GJ/* skiO */+_GK/* skiS */,
          _GM/* skiZ */ = _GJ/* skiO */-_GK/* skiS */,
          _GN/* skj2 */ = E(_GD/* skiy */),
          _GO/* skj6 */ = E(_GE/* skiz */),
          _GP/* skj9 */ = __app4/* EXTERNAL */(E(_rK/* Core.Shape.Internal.bezier_f2 */), _GI/* skiL */, _GM/* skiZ */, _GN/* skj2 */, _GO/* skj6 */),
          _GQ/* skjc */ = E(_rL/* Core.Shape.Internal.line_f1 */),
          _GR/* skjf */ = __app4/* EXTERNAL */(_GQ/* skjc */, _GH/* skiF */, _GJ/* skiO */-_GK/* skiS */, _GN/* skj2 */, _GO/* skj6 */),
          _GS/* skjj */ = __app4/* EXTERNAL */(_GQ/* skjc */, _GH/* skiF */, _GL/* skiW */, _GN/* skj2 */, _GO/* skj6 */),
          _GT/* skjn */ = __app4/* EXTERNAL */(_GQ/* skjc */, _GF/* skiB */-_GG/* skiD */, _GL/* skiW */, _GN/* skj2 */, _GO/* skj6 */),
          _GU/* skjr */ = __app4/* EXTERNAL */(_GQ/* skjc */, _GI/* skiL */, _GM/* skiZ */, _GN/* skj2 */, _GO/* skj6 */);
          return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        };
        return function(_gd/* _fa_1 */, _ge/* _fa_2 */, _GV/* _fa_3 */){
          return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_Gp/* skhr */, _GB/* skju */, _gd/* _fa_1 */, _ge/* _fa_2 */, _GV/* _fa_3 */);});
        };
      };
      return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_Go/* skhq */, _Gy/* skjv */, _Gw/* skip */, _Gx/* skiq */, _/* EXTERNAL */);});
    };
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_Gn/* skhp */, _Gu/* skjw */, _Gs/* skil */, _Gt/* skim */, _/* EXTERNAL */);});
  },
  _GW/* skij */ = function(_GX/* skhs */, _/* EXTERNAL */){
    var _GY/* skhu */ = E(_GX/* skhs */),
    _GZ/* skii */ = function(_H0/* skhx */, _/* EXTERNAL */){
      var _H1/* skih */ = function(_H2/* skhz */, _/* EXTERNAL */){
        var _H3/* skig */ = function(_H4/* skhB */, _/* EXTERNAL */){
          var _H5/* skif */ = function(_H6/* skhD */, _/* EXTERNAL */){
            return new T(function(){
              var _H7/* skhJ */ = function(_H8/* skhK */){
                if(_H8/* skhK */>=E(_H4/* skhB */)/2){
                  return false;
                }else{
                  var _H9/* skhU */ = E(_GY/* skhu */.b)-E(_H2/* skhz */);
                  return (_H9/* skhU */==0) ? 0<E(_H6/* skhD */)/2 : (_H9/* skhU */<=0) ?  -_H9/* skhU */<E(_H6/* skhD */)/2 : _H9/* skhU */<E(_H6/* skhD */)/2;
                }
              },
              _Ha/* skia */ = E(_GY/* skhu */.a)-E(_H0/* skhx */);
              if(!_Ha/* skia */){
                return B(_H7/* skhJ */(0));
              }else{
                if(_Ha/* skia */<=0){
                  return B(_H7/* skhJ */( -_Ha/* skia */));
                }else{
                  return B(_H7/* skhJ */(_Ha/* skia */));
                }
              }
            });
          };
          return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_Gp/* skhr */, _H5/* skif */, _/* EXTERNAL */);});
        };
        return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_Go/* skhq */, _H3/* skig */, _/* EXTERNAL */);});
      };
      return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_Gn/* skhp */, _H1/* skih */, _/* EXTERNAL */);});
    };
    return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_Gm/* skho */, _GZ/* skii */, _/* EXTERNAL */);});
  };
  return new T3(0,_GW/* skij */,function(_rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_Gm/* skho */, _Gq/* skjx */, _rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_Hb/* a3 */ = new T1(0,_/* EXTERNAL */),
_Hc/* a4 */ = new T1(0,_6/* GHC.Types.[] */),
_Hd/* a5 */ = new T2(0,E(_Hc/* Motion.Grow.a4 */),E(_Hb/* Motion.Grow.a3 */)),
_He/* a */ = function(_Hf/* s7gK */, _Hg/* s7gL */){
  return new F(function(){return A1(_Hg/* s7gL */,new T2(0,_7/* GHC.Tuple.() */,_Hf/* s7gK */));});
},
_Hh/* ds */ = 1,
_Hi/* go */ = function(_Hj/* s7hB */){
  var _Hk/* s7hC */ = E(_Hj/* s7hB */);
  if(!_Hk/* s7hC */._){
    return E(_He/* Motion.Grow.a */);
  }else{
    var _Hl/* s7hF */ = new T(function(){
      var _Hm/* s7hG */ = E(_Hk/* s7hC */.a);
      return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Hm/* s7hG */.a, _Hm/* s7hG */.b, _Hm/* s7hG */.c, _Hh/* Motion.Grow.ds */, _tT/* Core.Ease.easeTo1 */));
    }),
    _Hn/* s7hK */ = new T(function(){
      return B(_Hi/* Motion.Grow.go */(_Hk/* s7hC */.b));
    }),
    _Ho/* s7hU */ = function(_Hp/* s7hL */){
      var _Hq/* s7hM */ = new T(function(){
        return B(A1(_Hl/* s7hF */,_Hp/* s7hL */));
      }),
      _Hr/* s7hT */ = function(_Hs/* s7hN */){
        return new F(function(){return A1(_Hq/* s7hM */,function(_Ht/* s7hO */){
          return new F(function(){return A2(_Hn/* s7hK */,E(_Ht/* s7hO */).b, _Hs/* s7hN */);});
        });});
      };
      return E(_Hr/* s7hT */);
    };
    return E(_Ho/* s7hU */);
  }
},
_Hu/* go1 */ = function(_Hv/* s7hV */){
  var _Hw/* s7hW */ = E(_Hv/* s7hV */);
  if(!_Hw/* s7hW */._){
    return E(_He/* Motion.Grow.a */);
  }else{
    var _Hx/* s7hZ */ = new T(function(){
      var _Hy/* s7i0 */ = E(_Hw/* s7hW */.a),
      _Hz/* s7if */ = function(_HA/* s7i4 */){
        var _HB/* s7i5 */ = new T(function(){
          return B(A1(_Hy/* s7i0 */.b,_HA/* s7i4 */));
        }),
        _HC/* s7ie */ = function(_HD/* s7i6 */){
          return 1-B(A1(_HB/* s7i5 */,new T(function(){
            return 1-E(_HD/* s7i6 */);
          })));
        };
        return E(_HC/* s7ie */);
      };
      return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Hy/* s7i0 */.a, _Hz/* s7if */, _Hy/* s7i0 */.c, _FZ/* Motion.Grow.lvl */, _tT/* Core.Ease.easeTo1 */));
    }),
    _HE/* s7ig */ = new T(function(){
      return B(_Hu/* Motion.Grow.go1 */(_Hw/* s7hW */.b));
    }),
    _HF/* s7iq */ = function(_HG/* s7ih */){
      var _HH/* s7ii */ = new T(function(){
        return B(A1(_Hx/* s7hZ */,_HG/* s7ih */));
      }),
      _HI/* s7ip */ = function(_HJ/* s7ij */){
        return new F(function(){return A1(_HH/* s7ii */,function(_HK/* s7ik */){
          return new F(function(){return A2(_HE/* s7ig */,E(_HK/* s7ik */).b, _HJ/* s7ij */);});
        });});
      };
      return E(_HI/* s7ip */);
    };
    return E(_HF/* s7iq */);
  }
},
_HL/* eftInt */ = function(_HM/* smpW */, _HN/* smpX */){
  if(_HM/* smpW */<=_HN/* smpX */){
    var _HO/* smq0 */ = function(_HP/* smq1 */){
      return new T2(1,_HP/* smq1 */,new T(function(){
        if(_HP/* smq1 */!=_HN/* smpX */){
          return B(_HO/* smq0 */(_HP/* smq1 */+1|0));
        }else{
          return __Z/* EXTERNAL */;
        }
      }));
    };
    return new F(function(){return _HO/* smq0 */(_HM/* smpW */);});
  }else{
    return __Z/* EXTERNAL */;
  }
},
_HQ/* iforM1 */ = new T(function(){
  return B(_HL/* GHC.Enum.eftInt */(0, 2147483647));
}),
_HR/* a2 */ = 40,
_HS/* lvl10 */ = new T1(0,_HR/* Motion.Grow.a2 */),
_HT/* lvl11 */ = 40,
_HU/* lvl8 */ = new T1(0,_G0/* Motion.Grow.lvl1 */),
_HV/* lvl6 */ = 50,
_HW/* lvl7 */ = new T1(0,_HV/* Motion.Grow.lvl6 */),
_HX/* lvl9 */ = new T(function(){
  return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, _HW/* Motion.Grow.lvl7 */, _HU/* Motion.Grow.lvl8 */));
}),
_HY/* morph */ = function(_HZ/* saZ5 */){
  return new T2(2,_HZ/* saZ5 */,_2E/* GHC.Base.id */);
},
_I0/* $wa */ = function(_I1/* s7ir */, _I2/* s7is */, _I3/* s7it */){
  var _I4/* s7iu */ = function(_I5/* s7iv */, _I6/* s7iw */){
    var _I7/* s7ix */ = E(_I5/* s7iv */);
    if(!_I7/* s7ix */._){
      return E(_Hd/* Motion.Grow.a5 */);
    }else{
      var _I8/* s7iA */ = E(_I6/* s7iw */);
      if(!_I8/* s7iA */._){
        return E(_Hd/* Motion.Grow.a5 */);
      }else{
        var _I9/* s7iB */ = _I8/* s7iA */.a,
        _Ia/* s7iD */ = new T(function(){
          return 4-E(_I7/* s7ix */.a);
        }),
        _Ib/* s7iW */ = new T(function(){
          var _Ic/* s7iV */ = new T(function(){
            var _Id/* s7iR */ = B(_Gl/* Core.Shape.Internal.$wcenterRect */(_HX/* Motion.Grow.lvl9 */, new T(function(){
              return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, B(_uj/* Core.Ease.opLift */(_vu/* GHC.Float.timesDouble */, new T1(0,_Ia/* s7iD */), _HS/* Motion.Grow.lvl10 */)), _HU/* Motion.Grow.lvl8 */));
            }), _HS/* Motion.Grow.lvl10 */, _HS/* Motion.Grow.lvl10 */));
            return new T3(0,_Id/* s7iR */.a,_Id/* s7iR */.b,_Id/* s7iR */.c);
          });
          return B(_ro/* Core.Render.Internal.fill1 */(_I1/* s7ir */, _Ic/* s7iV */));
        }),
        _Ie/* s7iX */ = B(_FC/* Core.Render.Internal.$fAffineRender1 */(new T2(0,new T(function(){
          return B(_HY/* Core.Ease.morph */(_I9/* s7iB */));
        }),new T(function(){
          return B(_HY/* Core.Ease.morph */(_I9/* s7iB */));
        })), _HX/* Motion.Grow.lvl9 */, new T(function(){
          return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, B(_uj/* Core.Ease.opLift */(_vu/* GHC.Float.timesDouble */, new T1(0,_Ia/* s7iD */), _HS/* Motion.Grow.lvl10 */)), _HS/* Motion.Grow.lvl10 */));
        }), _Ib/* s7iW */)),
        _If/* s7j0 */ = new T(function(){
          return B(_I4/* s7iu */(_I7/* s7ix */.b, _I8/* s7iA */.b));
        }),
        _Ig/* s7jb */ = function(_Ih/* s7j1 */){
          var _Ii/* s7j2 */ = E(_If/* s7j0 */);
          return new T2(0,E(_Ii/* s7j2 */.a),E(new T2(2,_Ii/* s7j2 */.b,new T1(1,function(_Ij/* s7j5 */){
            return new T2(0,E(new T1(0,new T2(1,_Ih/* s7j1 */,_Ij/* s7j5 */))),E(_Hb/* Motion.Grow.a3 */));
          }))));
        };
        return new T2(0,E(_Ie/* s7iX */.a),E(new T2(2,_Ie/* s7iX */.b,new T1(1,_Ig/* s7jb */))));
      }
    }
  },
  _Ik/* s7jN */ = function(_Il/* s7je */){
    var _Im/* s7jf */ = E(_Il/* s7je */),
    _In/* s7jg */ = _Im/* s7jf */.a,
    _Io/* s7ji */ = new T(function(){
      return B(_Hu/* Motion.Grow.go1 */(_In/* s7jg */));
    }),
    _Ip/* s7jj */ = new T(function(){
      return B(_Hi/* Motion.Grow.go */(_In/* s7jg */));
    }),
    _Iq/* s7jk */ = function(_Ir/* s7jl */){
      var _Is/* s7jm */ = new T(function(){
        return B(A1(_Ip/* s7jj */,_Ir/* s7jl */));
      }),
      _It/* s7jI */ = function(_Iu/* s7jn */){
        var _Iv/* s7jo */ = function(_Iw/* s7jp */){
          return new F(function(){return A2(_Iq/* s7jk */,E(_Iw/* s7jp */).b, _Iu/* s7jn */);});
        },
        _Ix/* s7jt */ = function(_Iy/* s7ju */){
          return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_HT/* Motion.Grow.lvl11 */, E(_Iy/* s7ju */).b, _Iv/* s7jo */);});
        },
        _Iz/* s7jy */ = function(_IA/* s7jz */){
          return new F(function(){return A2(_Io/* s7ji */,E(_IA/* s7jz */).b, _Ix/* s7jt */);});
        };
        return new F(function(){return A1(_Is/* s7jm */,function(_IB/* s7jD */){
          return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_HT/* Motion.Grow.lvl11 */, E(_IB/* s7jD */).b, _Iz/* s7jy */);});
        });});
      };
      return E(_It/* s7jI */);
    },
    _IC/* s7jK */ = new T(function(){
      return B(_p8/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
        return B(_I4/* s7iu */(_HQ/* Core.Util.iforM1 */, _In/* s7jg */));
      })));
    });
    return new F(function(){return A1(_I3/* s7it */,new T2(0,new T2(0,_IC/* s7jK */,_Iq/* s7jk */),_Im/* s7jf */.b));});
  };
  return new F(function(){return _G5/* Motion.Grow.$wa1 */(0, _I2/* s7is */, _Ik/* s7jN */);});
},
_ID/* growMot1 */ = function(_IE/* s7jO */, _IF/* s7jP */, _IG/* s7jQ */){
  return new T1(0,B(_I0/* Motion.Grow.$wa */(_IE/* s7jO */, _IF/* s7jP */, _IG/* s7jQ */)));
},
_IH/* lvl29 */ = 0.8,
_II/* lvl30 */ = new T1(0,_IH/* Motion.Main.lvl29 */),
_IJ/* lvl31 */ = new T4(0,_Fw/* Motion.Main.lvl25 */,_II/* Motion.Main.lvl30 */,_sA/* Motion.Main.lvl4 */,_u4/* Motion.Main.lvl9 */),
_IK/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Grow"));
}),
_IL/* lvl33 */ = new T(function(){
  return B(_AB/* Motion.Main.$wconsView */(_IJ/* Motion.Main.lvl31 */, _ID/* Motion.Grow.growMot1 */, _IK/* Motion.Main.lvl32 */));
}),
_IM/* lvl34 */ = new T4(0,_u4/* Motion.Main.lvl9 */,_u2/* Motion.Main.lvl7 */,_sA/* Motion.Main.lvl4 */,_u4/* Motion.Main.lvl9 */),
_IN/* lvl35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Speed"));
}),
_IO/* speedMot1 */ = function(_IP/* saf2 */, _IQ/* saf3 */){
  return new F(function(){return A1(_IQ/* saf3 */,new T2(0,_7/* GHC.Tuple.() */,_IP/* saf2 */));});
},
_IR/* speedMot14 */ = 0,
_IS/* speedMot13 */ = new T1(0,_IR/* Motion.Speed.speedMot14 */),
_IT/* speedMot12 */ = new T2(0,_IS/* Motion.Speed.speedMot13 */,_IS/* Motion.Speed.speedMot13 */),
_IU/* intToInt64# */ = function(_IV/* sf6 */){
  var _IW/* sf8 */ = hs_intToInt64/* EXTERNAL */(_IV/* sf6 */);
  return E(_IW/* sf8 */);
},
_IX/* integerToInt64 */ = function(_IY/* s1S1 */){
  var _IZ/* s1S2 */ = E(_IY/* s1S1 */);
  if(!_IZ/* s1S2 */._){
    return new F(function(){return _IU/* GHC.IntWord64.intToInt64# */(_IZ/* s1S2 */.a);});
  }else{
    return new F(function(){return I_toInt64/* EXTERNAL */(_IZ/* s1S2 */.a);});
  }
},
_J0/* $cfromInteger3 */ = function(_J1/* s2dWF */){
  return new F(function(){return _IX/* GHC.Integer.Type.integerToInt64 */(_J1/* s2dWF */);});
},
_J2/* $fNumInt64_$c* */ = function(_J3/* s2dXh */, _J4/* s2dXi */){
  return new F(function(){return hs_timesInt64/* EXTERNAL */(E(_J3/* s2dXh */), E(_J4/* s2dXi */));});
},
_J5/* $fNumInt64_$c+ */ = function(_J6/* s2dXB */, _J7/* s2dXC */){
  return new F(function(){return hs_plusInt64/* EXTERNAL */(E(_J6/* s2dXB */), E(_J7/* s2dXC */));});
},
_J8/* $fNumInt64_$c- */ = function(_J9/* s2dXr */, _Ja/* s2dXs */){
  return new F(function(){return hs_minusInt64/* EXTERNAL */(E(_J9/* s2dXr */), E(_Ja/* s2dXs */));});
},
_Jb/* $w$cabs */ = function(_Jc/* s2dWW */){
  var _Jd/* s2dWY */ = hs_geInt64/* EXTERNAL */(_Jc/* s2dWW */, new Long/* EXTERNAL */(0, 0));
  if(!_Jd/* s2dWY */){
    var _Je/* s2dX3 */ = hs_negateInt64/* EXTERNAL */(_Jc/* s2dWW */);
    return E(_Je/* s2dX3 */);
  }else{
    return E(_Jc/* s2dWW */);
  }
},
_Jf/* $fNumInt64_$cabs */ = function(_Jg/* s2dX6 */){
  return new F(function(){return _Jb/* GHC.Int.$w$cabs */(E(_Jg/* s2dX6 */));});
},
_Jh/* $fNumInt64_$cnegate */ = function(_Ji/* s2dXa */){
  return new F(function(){return hs_negateInt64/* EXTERNAL */(E(_Ji/* s2dXa */));});
},
_Jj/* $w$csignum */ = function(_Jk/* s2dWH */){
  var _Jl/* s2dWJ */ = hs_gtInt64/* EXTERNAL */(_Jk/* s2dWH */, new Long/* EXTERNAL */(0, 0));
  if(!_Jl/* s2dWJ */){
    var _Jm/* s2dWO */ = hs_eqInt64/* EXTERNAL */(_Jk/* s2dWH */, new Long/* EXTERNAL */(0, 0));
    if(!_Jm/* s2dWO */){
      return new F(function(){return new Long/* EXTERNAL */(4294967295, -1);});
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return new F(function(){return new Long/* EXTERNAL */(1, 0);});
  }
},
_Jn/* $fNumInt64_$csignum */ = function(_Jo/* s2dWS */){
  return new F(function(){return _Jj/* GHC.Int.$w$csignum */(E(_Jo/* s2dWS */));});
},
_Jp/* $fNumInt64 */ = {_:0,a:_J5/* GHC.Int.$fNumInt64_$c+ */,b:_J8/* GHC.Int.$fNumInt64_$c- */,c:_J2/* GHC.Int.$fNumInt64_$c* */,d:_Jh/* GHC.Int.$fNumInt64_$cnegate */,e:_Jf/* GHC.Int.$fNumInt64_$cabs */,f:_Jn/* GHC.Int.$fNumInt64_$csignum */,g:_J0/* GHC.Int.$cfromInteger3 */},
_Jq/* lvl */ = new T1(0,0),
_Jr/* orInteger */ = function(_Js/* s1KS */, _Jt/* s1KT */){
  while(1){
    var _Ju/* s1KU */ = E(_Js/* s1KS */);
    if(!_Ju/* s1KU */._){
      var _Jv/* s1KV */ = _Ju/* s1KU */.a,
      _Jw/* s1KW */ = E(_Jt/* s1KT */);
      if(!_Jw/* s1KW */._){
        return new T1(0,(_Jv/* s1KV */>>>0|_Jw/* s1KW */.a>>>0)>>>0&4294967295);
      }else{
        _Js/* s1KS */ = new T1(1,I_fromInt/* EXTERNAL */(_Jv/* s1KV */));
        _Jt/* s1KT */ = _Jw/* s1KW */;
        continue;
      }
    }else{
      var _Jx/* s1L7 */ = E(_Jt/* s1KT */);
      if(!_Jx/* s1L7 */._){
        _Js/* s1KS */ = _Ju/* s1KU */;
        _Jt/* s1KT */ = new T1(1,I_fromInt/* EXTERNAL */(_Jx/* s1L7 */.a));
        continue;
      }else{
        return new T1(1,I_or/* EXTERNAL */(_Ju/* s1KU */.a, _Jx/* s1L7 */.a));
      }
    }
  }
},
_Jy/* shiftLInteger */ = function(_Jz/* s1Jk */, _JA/* s1Jl */){
  while(1){
    var _JB/* s1Jm */ = E(_Jz/* s1Jk */);
    if(!_JB/* s1Jm */._){
      _Jz/* s1Jk */ = new T1(1,I_fromInt/* EXTERNAL */(_JB/* s1Jm */.a));
      continue;
    }else{
      return new T1(1,I_shiftLeft/* EXTERNAL */(_JB/* s1Jm */.a, _JA/* s1Jl */));
    }
  }
},
_JC/* mkInteger_f */ = function(_JD/* s1S6 */){
  var _JE/* s1S7 */ = E(_JD/* s1S6 */);
  if(!_JE/* s1S7 */._){
    return E(_Jq/* GHC.Integer.Type.lvl */);
  }else{
    return new F(function(){return _Jr/* GHC.Integer.Type.orInteger */(new T1(0,E(_JE/* s1S7 */.a)), B(_Jy/* GHC.Integer.Type.shiftLInteger */(B(_JC/* GHC.Integer.Type.mkInteger_f */(_JE/* s1S7 */.b)), 31)));});
  }
},
_JF/* log2I1 */ = new T1(0,1),
_JG/* lvl2 */ = new T1(0,2147483647),
_JH/* plusInteger */ = function(_JI/* s1Qe */, _JJ/* s1Qf */){
  while(1){
    var _JK/* s1Qg */ = E(_JI/* s1Qe */);
    if(!_JK/* s1Qg */._){
      var _JL/* s1Qh */ = _JK/* s1Qg */.a,
      _JM/* s1Qi */ = E(_JJ/* s1Qf */);
      if(!_JM/* s1Qi */._){
        var _JN/* s1Qj */ = _JM/* s1Qi */.a,
        _JO/* s1Qk */ = addC/* EXTERNAL */(_JL/* s1Qh */, _JN/* s1Qj */);
        if(!E(_JO/* s1Qk */.b)){
          return new T1(0,_JO/* s1Qk */.a);
        }else{
          _JI/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_JL/* s1Qh */));
          _JJ/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_JN/* s1Qj */));
          continue;
        }
      }else{
        _JI/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_JL/* s1Qh */));
        _JJ/* s1Qf */ = _JM/* s1Qi */;
        continue;
      }
    }else{
      var _JP/* s1Qz */ = E(_JJ/* s1Qf */);
      if(!_JP/* s1Qz */._){
        _JI/* s1Qe */ = _JK/* s1Qg */;
        _JJ/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_JP/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_JK/* s1Qg */.a, _JP/* s1Qz */.a));
      }
    }
  }
},
_JQ/* lvl3 */ = new T(function(){
  return B(_JH/* GHC.Integer.Type.plusInteger */(_JG/* GHC.Integer.Type.lvl2 */, _JF/* GHC.Integer.Type.log2I1 */));
}),
_JR/* negateInteger */ = function(_JS/* s1QH */){
  var _JT/* s1QI */ = E(_JS/* s1QH */);
  if(!_JT/* s1QI */._){
    var _JU/* s1QK */ = E(_JT/* s1QI */.a);
    return (_JU/* s1QK */==(-2147483648)) ? E(_JQ/* GHC.Integer.Type.lvl3 */) : new T1(0, -_JU/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_JT/* s1QI */.a));
  }
},
_JV/* mkInteger */ = function(_JW/* s1Sf */, _JX/* s1Sg */){
  if(!E(_JW/* s1Sf */)){
    return new F(function(){return _JR/* GHC.Integer.Type.negateInteger */(B(_JC/* GHC.Integer.Type.mkInteger_f */(_JX/* s1Sg */)));});
  }else{
    return new F(function(){return _JC/* GHC.Integer.Type.mkInteger_f */(_JX/* s1Sg */);});
  }
},
_JY/* sfn3 */ = 2147483647,
_JZ/* sfn4 */ = 2147483647,
_K0/* sfn5 */ = 1,
_K1/* sfn6 */ = new T2(1,_K0/* sfn5 */,_6/* GHC.Types.[] */),
_K2/* sfn7 */ = new T2(1,_JZ/* sfn4 */,_K1/* sfn6 */),
_K3/* sfn8 */ = new T2(1,_JY/* sfn3 */,_K2/* sfn7 */),
_K4/* $fRandomCLLong3 */ = new T(function(){
  return B(_JV/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _K3/* sfn8 */));
}),
_K5/* sfn9 */ = 0,
_K6/* sfna */ = 0,
_K7/* sfnb */ = 2,
_K8/* sfnc */ = new T2(1,_K7/* sfnb */,_6/* GHC.Types.[] */),
_K9/* sfnd */ = new T2(1,_K6/* sfna */,_K8/* sfnc */),
_Ka/* sfne */ = new T2(1,_K5/* sfn9 */,_K9/* sfnd */),
_Kb/* $fRandomCLLong4 */ = new T(function(){
  return B(_JV/* GHC.Integer.Type.mkInteger */(_av/* GHC.Types.False */, _Ka/* sfne */));
}),
_Kc/* $fRandomDouble4 */ = new Long/* EXTERNAL */(2, 0),
_Kd/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_Ke/* $fRandomDouble5 */ = new T(function(){
  return B(err/* EXTERNAL */(_Kd/* System.Random.lvl1 */));
}),
_Kf/* $fRandomDouble6 */ = new Long/* EXTERNAL */(1, 0),
_Kg/* $fBoundedInt64_$cmaxBound */ = new Long/* EXTERNAL */(4294967295, 2147483647),
_Kh/* $fBoundedInt64_$cminBound */ = new Long/* EXTERNAL */(0, -2147483648),
_Ki/* $fBoundedInt64 */ = new T2(0,_Kh/* GHC.Int.$fBoundedInt64_$cminBound */,_Kg/* GHC.Int.$fBoundedInt64_$cmaxBound */),
_Kj/* $fEnumRatio1 */ = new T1(0,1),
_Kk/* $p1Integral */ = function(_Kl/* sveb */){
  return E(E(_Kl/* sveb */).a);
},
_Km/* $p1Real */ = function(_Kn/* svfM */){
  return E(E(_Kn/* svfM */).a);
},
_Ko/* fromInteger */ = function(_Kp/* s6Gq */){
  return E(E(_Kp/* s6Gq */).g);
},
_Kq/* gtInteger */ = function(_Kr/* s1G4 */, _Ks/* s1G5 */){
  var _Kt/* s1G6 */ = E(_Kr/* s1G4 */);
  if(!_Kt/* s1G6 */._){
    var _Ku/* s1G7 */ = _Kt/* s1G6 */.a,
    _Kv/* s1G8 */ = E(_Ks/* s1G5 */);
    return (_Kv/* s1G8 */._==0) ? _Ku/* s1G7 */>_Kv/* s1G8 */.a : I_compareInt/* EXTERNAL */(_Kv/* s1G8 */.a, _Ku/* s1G7 */)<0;
  }else{
    var _Kw/* s1Gf */ = _Kt/* s1G6 */.a,
    _Kx/* s1Gg */ = E(_Ks/* s1G5 */);
    return (_Kx/* s1Gg */._==0) ? I_compareInt/* EXTERNAL */(_Kw/* s1Gf */, _Kx/* s1Gg */.a)>0 : I_compare/* EXTERNAL */(_Kw/* s1Gf */, _Kx/* s1Gg */.a)>0;
  }
},
_Ky/* maxBound */ = function(_Kz/* smmz */){
  return E(E(_Kz/* smmz */).b);
},
_KA/* toInteger */ = function(_KB/* svfB */){
  return E(E(_KB/* svfB */).i);
},
_KC/* integralEnumFrom */ = function(_KD/* svkx */, _KE/* svky */, _KF/* svkz */){
  var _KG/* svkC */ = new T(function(){
    return B(_Ko/* GHC.Num.fromInteger */(new T(function(){
      return B(_Km/* GHC.Real.$p1Real */(new T(function(){
        return B(_Kk/* GHC.Real.$p1Integral */(_KD/* svkx */));
      })));
    })));
  }),
  _KH/* svkE */ = new T(function(){
    return B(_Ky/* GHC.Enum.maxBound */(_KE/* svky */));
  }),
  _KI/* svkF */ = function(_KJ/* svkG */){
    return (!B(_Kq/* GHC.Integer.Type.gtInteger */(_KJ/* svkG */, B(A2(_KA/* GHC.Real.toInteger */,_KD/* svkx */, _KH/* svkE */))))) ? new T2(1,new T(function(){
      return B(A1(_KG/* svkC */,_KJ/* svkG */));
    }),new T(function(){
      return B(_KI/* svkF */(B(_JH/* GHC.Integer.Type.plusInteger */(_KJ/* svkG */, _Kj/* GHC.Real.$fEnumRatio1 */))));
    })) : __Z/* EXTERNAL */;
  };
  return new F(function(){return _KI/* svkF */(B(A2(_KA/* GHC.Real.toInteger */,_KD/* svkx */, _KF/* svkz */)));});
},
_KK/* $fEnumInt64_$cenumFrom */ = function(_KL/* B1 */){
  return new F(function(){return _KC/* GHC.Real.integralEnumFrom */(_KM/* GHC.Int.$fIntegralInt64 */, _Ki/* GHC.Int.$fBoundedInt64 */, _KL/* B1 */);});
},
_KN/* $fEnumInteger1 */ = new T1(0,0),
_KO/* geInteger */ = function(_KP/* s1Fo */, _KQ/* s1Fp */){
  var _KR/* s1Fq */ = E(_KP/* s1Fo */);
  if(!_KR/* s1Fq */._){
    var _KS/* s1Fr */ = _KR/* s1Fq */.a,
    _KT/* s1Fs */ = E(_KQ/* s1Fp */);
    return (_KT/* s1Fs */._==0) ? _KS/* s1Fr */>=_KT/* s1Fs */.a : I_compareInt/* EXTERNAL */(_KT/* s1Fs */.a, _KS/* s1Fr */)<=0;
  }else{
    var _KU/* s1Fz */ = _KR/* s1Fq */.a,
    _KV/* s1FA */ = E(_KQ/* s1Fp */);
    return (_KV/* s1FA */._==0) ? I_compareInt/* EXTERNAL */(_KU/* s1Fz */, _KV/* s1FA */.a)>=0 : I_compare/* EXTERNAL */(_KU/* s1Fz */, _KV/* s1FA */.a)>=0;
  }
},
_KW/* ltInteger */ = function(_KX/* s1FJ */, _KY/* s1FK */){
  var _KZ/* s1FL */ = E(_KX/* s1FJ */);
  if(!_KZ/* s1FL */._){
    var _L0/* s1FM */ = _KZ/* s1FL */.a,
    _L1/* s1FN */ = E(_KY/* s1FK */);
    return (_L1/* s1FN */._==0) ? _L0/* s1FM */<_L1/* s1FN */.a : I_compareInt/* EXTERNAL */(_L1/* s1FN */.a, _L0/* s1FM */)>0;
  }else{
    var _L2/* s1FU */ = _KZ/* s1FL */.a,
    _L3/* s1FV */ = E(_KY/* s1FK */);
    return (_L3/* s1FV */._==0) ? I_compareInt/* EXTERNAL */(_L2/* s1FU */, _L3/* s1FV */.a)<0 : I_compare/* EXTERNAL */(_L2/* s1FU */, _L3/* s1FV */.a)<0;
  }
},
_L4/* up_fb */ = function(_L5/* smnV */, _L6/* smnW */, _L7/* smnX */, _L8/* smnY */, _L9/* smnZ */){
  var _La/* smo0 */ = function(_Lb/* smo1 */){
    if(!B(_Kq/* GHC.Integer.Type.gtInteger */(_Lb/* smo1 */, _L9/* smnZ */))){
      return new F(function(){return A2(_L5/* smnV */,_Lb/* smo1 */, new T(function(){
        return B(_La/* smo0 */(B(_JH/* GHC.Integer.Type.plusInteger */(_Lb/* smo1 */, _L8/* smnY */))));
      }));});
    }else{
      return E(_L6/* smnW */);
    }
  };
  return new F(function(){return _La/* smo0 */(_L7/* smnX */);});
},
_Lc/* enumDeltaToIntegerFB */ = function(_Ld/* smK3 */, _Le/* smK4 */, _Lf/* smK5 */, _Lg/* smK6 */, _Lh/* smK7 */){
  if(!B(_KO/* GHC.Integer.Type.geInteger */(_Lg/* smK6 */, _KN/* GHC.Enum.$fEnumInteger1 */))){
    var _Li/* smK9 */ = function(_Lj/* smKa */){
      if(!B(_KW/* GHC.Integer.Type.ltInteger */(_Lj/* smKa */, _Lh/* smK7 */))){
        return new F(function(){return A2(_Ld/* smK3 */,_Lj/* smKa */, new T(function(){
          return B(_Li/* smK9 */(B(_JH/* GHC.Integer.Type.plusInteger */(_Lj/* smKa */, _Lg/* smK6 */))));
        }));});
      }else{
        return E(_Le/* smK4 */);
      }
    };
    return new F(function(){return _Li/* smK9 */(_Lf/* smK5 */);});
  }else{
    return new F(function(){return _L4/* GHC.Enum.up_fb */(_Ld/* smK3 */, _Le/* smK4 */, _Lf/* smK5 */, _Lg/* smK6 */, _Lh/* smK7 */);});
  }
},
_Lk/* minBound */ = function(_Ll/* smmv */){
  return E(E(_Ll/* smmv */).a);
},
_Lm/* minusInteger */ = function(_Ln/* s1P0 */, _Lo/* s1P1 */){
  while(1){
    var _Lp/* s1P2 */ = E(_Ln/* s1P0 */);
    if(!_Lp/* s1P2 */._){
      var _Lq/* s1P3 */ = _Lp/* s1P2 */.a,
      _Lr/* s1P4 */ = E(_Lo/* s1P1 */);
      if(!_Lr/* s1P4 */._){
        var _Ls/* s1P5 */ = _Lr/* s1P4 */.a,
        _Lt/* s1P6 */ = subC/* EXTERNAL */(_Lq/* s1P3 */, _Ls/* s1P5 */);
        if(!E(_Lt/* s1P6 */.b)){
          return new T1(0,_Lt/* s1P6 */.a);
        }else{
          _Ln/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_Lq/* s1P3 */));
          _Lo/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_Ls/* s1P5 */));
          continue;
        }
      }else{
        _Ln/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_Lq/* s1P3 */));
        _Lo/* s1P1 */ = _Lr/* s1P4 */;
        continue;
      }
    }else{
      var _Lu/* s1Pl */ = E(_Lo/* s1P1 */);
      if(!_Lu/* s1Pl */._){
        _Ln/* s1P0 */ = _Lp/* s1P2 */;
        _Lo/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_Lu/* s1Pl */.a));
        continue;
      }else{
        return new T1(1,I_sub/* EXTERNAL */(_Lp/* s1P2 */.a, _Lu/* s1Pl */.a));
      }
    }
  }
},
_Lv/* integralEnumFromThen */ = function(_Lw/* svk6 */, _Lx/* svk7 */, _Ly/* svk8 */, _Lz/* svk9 */){
  var _LA/* svka */ = B(A2(_KA/* GHC.Real.toInteger */,_Lw/* svk6 */, _Lz/* svk9 */)),
  _LB/* svkb */ = B(A2(_KA/* GHC.Real.toInteger */,_Lw/* svk6 */, _Ly/* svk8 */));
  if(!B(_KO/* GHC.Integer.Type.geInteger */(_LA/* svka */, _LB/* svkb */))){
    var _LC/* svkf */ = new T(function(){
      return B(_Ko/* GHC.Num.fromInteger */(new T(function(){
        return B(_Km/* GHC.Real.$p1Real */(new T(function(){
          return B(_Kk/* GHC.Real.$p1Integral */(_Lw/* svk6 */));
        })));
      })));
    }),
    _LD/* svkj */ = function(_LE/* svkg */, _LF/* svkh */){
      return new T2(1,new T(function(){
        return B(A1(_LC/* svkf */,_LE/* svkg */));
      }),_LF/* svkh */);
    };
    return new F(function(){return _Lc/* GHC.Enum.enumDeltaToIntegerFB */(_LD/* svkj */, _6/* GHC.Types.[] */, _LB/* svkb */, B(_Lm/* GHC.Integer.Type.minusInteger */(_LA/* svka */, _LB/* svkb */)), B(A2(_KA/* GHC.Real.toInteger */,_Lw/* svk6 */, new T(function(){
      return B(_Lk/* GHC.Enum.minBound */(_Lx/* svk7 */));
    }))));});
  }else{
    var _LG/* svkp */ = new T(function(){
      return B(_Ko/* GHC.Num.fromInteger */(new T(function(){
        return B(_Km/* GHC.Real.$p1Real */(new T(function(){
          return B(_Kk/* GHC.Real.$p1Integral */(_Lw/* svk6 */));
        })));
      })));
    }),
    _LH/* svkt */ = function(_LI/* svkq */, _LJ/* svkr */){
      return new T2(1,new T(function(){
        return B(A1(_LG/* svkp */,_LI/* svkq */));
      }),_LJ/* svkr */);
    };
    return new F(function(){return _Lc/* GHC.Enum.enumDeltaToIntegerFB */(_LH/* svkt */, _6/* GHC.Types.[] */, _LB/* svkb */, B(_Lm/* GHC.Integer.Type.minusInteger */(_LA/* svka */, _LB/* svkb */)), B(A2(_KA/* GHC.Real.toInteger */,_Lw/* svk6 */, new T(function(){
      return B(_Ky/* GHC.Enum.maxBound */(_Lx/* svk7 */));
    }))));});
  }
},
_LK/* $fEnumInt64_$cenumFromThen */ = function(_LL/* B2 */, _KL/* B1 */){
  return new F(function(){return _Lv/* GHC.Real.integralEnumFromThen */(_KM/* GHC.Int.$fIntegralInt64 */, _Ki/* GHC.Int.$fBoundedInt64 */, _LL/* B2 */, _KL/* B1 */);});
},
_LM/* integralEnumFromThenTo */ = function(_LN/* svjD */, _LO/* svjE */, _LP/* svjF */, _LQ/* svjG */){
  var _LR/* svjH */ = B(A2(_KA/* GHC.Real.toInteger */,_LN/* svjD */, _LO/* svjE */)),
  _LS/* svjK */ = new T(function(){
    return B(_Ko/* GHC.Num.fromInteger */(new T(function(){
      return B(_Km/* GHC.Real.$p1Real */(new T(function(){
        return B(_Kk/* GHC.Real.$p1Integral */(_LN/* svjD */));
      })));
    })));
  }),
  _LT/* svjO */ = function(_LU/* svjL */, _LV/* svjM */){
    return new T2(1,new T(function(){
      return B(A1(_LS/* svjK */,_LU/* svjL */));
    }),_LV/* svjM */);
  };
  return new F(function(){return _Lc/* GHC.Enum.enumDeltaToIntegerFB */(_LT/* svjO */, _6/* GHC.Types.[] */, _LR/* svjH */, B(_Lm/* GHC.Integer.Type.minusInteger */(B(A2(_KA/* GHC.Real.toInteger */,_LN/* svjD */, _LP/* svjF */)), _LR/* svjH */)), B(A2(_KA/* GHC.Real.toInteger */,_LN/* svjD */, _LQ/* svjG */)));});
},
_LW/* $fEnumInt64_$cenumFromThenTo */ = function(_LX/* B3 */, _LL/* B2 */, _KL/* B1 */){
  return new F(function(){return _LM/* GHC.Real.integralEnumFromThenTo */(_KM/* GHC.Int.$fIntegralInt64 */, _LX/* B3 */, _LL/* B2 */, _KL/* B1 */);});
},
_LY/* integralEnumFromTo */ = function(_LZ/* svjS */, _M0/* svjT */, _M1/* svjU */){
  var _M2/* svjX */ = new T(function(){
    return B(_Ko/* GHC.Num.fromInteger */(new T(function(){
      return B(_Km/* GHC.Real.$p1Real */(new T(function(){
        return B(_Kk/* GHC.Real.$p1Integral */(_LZ/* svjS */));
      })));
    })));
  }),
  _M3/* svjZ */ = function(_M4/* svk0 */){
    return (!B(_Kq/* GHC.Integer.Type.gtInteger */(_M4/* svk0 */, B(A2(_KA/* GHC.Real.toInteger */,_LZ/* svjS */, _M1/* svjU */))))) ? new T2(1,new T(function(){
      return B(A1(_M2/* svjX */,_M4/* svk0 */));
    }),new T(function(){
      return B(_M3/* svjZ */(B(_JH/* GHC.Integer.Type.plusInteger */(_M4/* svk0 */, _Kj/* GHC.Real.$fEnumRatio1 */))));
    })) : __Z/* EXTERNAL */;
  };
  return new F(function(){return _M3/* svjZ */(B(A2(_KA/* GHC.Real.toInteger */,_LZ/* svjS */, _M0/* svjT */)));});
},
_M5/* $fEnumInt64_$cenumFromTo */ = function(_LL/* B2 */, _KL/* B1 */){
  return new F(function(){return _LY/* GHC.Real.integralEnumFromTo */(_KM/* GHC.Int.$fIntegralInt64 */, _LL/* B2 */, _KL/* B1 */);});
},
_M6/* $fEnumInt6 */ = new T(function(){
  return hs_intToInt64/* EXTERNAL */(2147483647);
}),
_M7/* smallInteger */ = function(_M8/* B1 */){
  return new T1(0,_M8/* B1 */);
},
_M9/* int64ToInteger */ = function(_Ma/* s1RA */){
  var _Mb/* s1RC */ = hs_intToInt64/* EXTERNAL */(2147483647),
  _Mc/* s1RG */ = hs_leInt64/* EXTERNAL */(_Ma/* s1RA */, _Mb/* s1RC */);
  if(!_Mc/* s1RG */){
    return new T1(1,I_fromInt64/* EXTERNAL */(_Ma/* s1RA */));
  }else{
    var _Md/* s1RN */ = hs_intToInt64/* EXTERNAL */(-2147483648),
    _Me/* s1RR */ = hs_geInt64/* EXTERNAL */(_Ma/* s1RA */, _Md/* s1RN */);
    if(!_Me/* s1RR */){
      return new T1(1,I_fromInt64/* EXTERNAL */(_Ma/* s1RA */));
    }else{
      var _Mf/* s1RY */ = hs_int64ToInt/* EXTERNAL */(_Ma/* s1RA */);
      return new F(function(){return _M7/* GHC.Integer.Type.smallInteger */(_Mf/* s1RY */);});
    }
  }
},
_Mg/* $fIntegralInt64_$ctoInteger */ = function(_Mh/* s2dYm */){
  return new F(function(){return _M9/* GHC.Integer.Type.int64ToInteger */(E(_Mh/* s2dYm */));});
},
_Mi/* integerToJSString */ = function(_Mj/* s1Iv */){
  while(1){
    var _Mk/* s1Iw */ = E(_Mj/* s1Iv */);
    if(!_Mk/* s1Iw */._){
      _Mj/* s1Iv */ = new T1(1,I_fromInt/* EXTERNAL */(_Mk/* s1Iw */.a));
      continue;
    }else{
      return new F(function(){return I_toString/* EXTERNAL */(_Mk/* s1Iw */.a);});
    }
  }
},
_Ml/* integerToString */ = function(_Mm/* sfbi */, _Mn/* sfbj */){
  return new F(function(){return _2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_Mi/* GHC.Integer.Type.integerToJSString */(_Mm/* sfbi */))), _Mn/* sfbj */);});
},
_Mo/* shows9 */ = new T1(0,0),
_Mp/* $w$cshowsPrec1 */ = function(_Mq/* sfcx */, _Mr/* sfcy */, _Ms/* sfcz */){
  if(_Mq/* sfcx */<=6){
    return new F(function(){return _Ml/* GHC.Show.integerToString */(_Mr/* sfcy */, _Ms/* sfcz */);});
  }else{
    if(!B(_KW/* GHC.Integer.Type.ltInteger */(_Mr/* sfcy */, _Mo/* GHC.Show.shows9 */))){
      return new F(function(){return _Ml/* GHC.Show.integerToString */(_Mr/* sfcy */, _Ms/* sfcz */);});
    }else{
      return new T2(1,_3c/* GHC.Show.shows8 */,new T(function(){
        return B(_2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_Mi/* GHC.Integer.Type.integerToJSString */(_Mr/* sfcy */))), new T2(1,_3b/* GHC.Show.shows7 */,_Ms/* sfcz */)));
      }));
    }
  }
},
_Mt/* $fShowInt64_$cshow */ = function(_Mu/* s2dYy */){
  return new F(function(){return _Mp/* GHC.Show.$w$cshowsPrec1 */(0, B(_Mg/* GHC.Int.$fIntegralInt64_$ctoInteger */(_Mu/* s2dYy */)), _6/* GHC.Types.[] */);});
},
_Mv/* $fShowInt3 */ = function(_Mw/* s2dYA */, _Mx/* s2dYB */){
  return new F(function(){return _Mp/* GHC.Show.$w$cshowsPrec1 */(0, B(_M9/* GHC.Integer.Type.int64ToInteger */(E(_Mw/* s2dYA */))), _Mx/* s2dYB */);});
},
_My/* $fShowInt64_$cshowList */ = function(_Mz/* s2dYF */, _MA/* s2dYG */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_Mv/* GHC.Int.$fShowInt3 */, _Mz/* s2dYF */, _MA/* s2dYG */);});
},
_MB/* $fShowInt64_$cshowsPrec */ = function(_MC/* s2dYp */, _MD/* s2dYq */){
  var _ME/* s2dYr */ = new T(function(){
    return B(_M9/* GHC.Integer.Type.int64ToInteger */(E(_MD/* s2dYq */)));
  });
  return function(_MF/* s2dYu */){
    return new F(function(){return _Mp/* GHC.Show.$w$cshowsPrec1 */(E(_MC/* s2dYp */), _ME/* s2dYr */, _MF/* s2dYu */);});
  };
},
_MG/* $fShowInt64 */ = new T3(0,_MB/* GHC.Int.$fShowInt64_$cshowsPrec */,_Mt/* GHC.Int.$fShowInt64_$cshow */,_My/* GHC.Int.$fShowInt64_$cshowList */),
_MH/* lvl */ = new T2(1,_3b/* GHC.Show.shows7 */,_6/* GHC.Types.[] */),
_MI/* $fShow(,)1 */ = function(_MJ/* sfg4 */, _MK/* sfg5 */, _ML/* sfg6 */){
  return new F(function(){return A1(_MJ/* sfg4 */,new T2(1,_23/* GHC.Show.showList__1 */,new T(function(){
    return B(A1(_MK/* sfg5 */,_ML/* sfg6 */));
  })));});
},
_MM/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_MN/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_MO/* errorEmptyList */ = function(_MP/* s9t7 */){
  return new F(function(){return err/* EXTERNAL */(B(_2/* GHC.Base.++ */(_MN/* GHC.List.prel_list_str */, new T(function(){
    return B(_2/* GHC.Base.++ */(_MP/* s9t7 */, _MM/* GHC.List.lvl */));
  },1))));});
},
_MQ/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("foldr1"));
}),
_MR/* lvl8 */ = new T(function(){
  return B(_MO/* GHC.List.errorEmptyList */(_MQ/* GHC.List.lvl7 */));
}),
_MS/* foldr1 */ = function(_MT/* s9Ah */, _MU/* s9Ai */){
  var _MV/* s9Aj */ = E(_MU/* s9Ai */);
  if(!_MV/* s9Aj */._){
    return E(_MR/* GHC.List.lvl8 */);
  }else{
    var _MW/* s9Ak */ = _MV/* s9Aj */.a,
    _MX/* s9Am */ = E(_MV/* s9Aj */.b);
    if(!_MX/* s9Am */._){
      return E(_MW/* s9Ak */);
    }else{
      return new F(function(){return A2(_MT/* s9Ah */,_MW/* s9Ak */, new T(function(){
        return B(_MS/* GHC.List.foldr1 */(_MT/* s9Ah */, _MX/* s9Am */));
      }));});
    }
  }
},
_MY/* lvl14 */ = function(_MZ/* smEb */){
  return new F(function(){return _3d/* GHC.Show.$wshowSignedInt */(0, -2147483648, _MZ/* smEb */);});
},
_N0/* lvl15 */ = function(_N1/* smEc */){
  return new F(function(){return _3d/* GHC.Show.$wshowSignedInt */(0, 2147483647, _N1/* smEc */);});
},
_N2/* lvl16 */ = new T2(1,_N0/* GHC.Enum.lvl15 */,_6/* GHC.Types.[] */),
_N3/* lvl17 */ = new T2(1,_MY/* GHC.Enum.lvl14 */,_N2/* GHC.Enum.lvl16 */),
_N4/* lvl18 */ = new T(function(){
  return B(_MS/* GHC.List.foldr1 */(_MI/* GHC.Show.$fShow(,)1 */, _N3/* GHC.Enum.lvl17 */));
}),
_N5/* lvl19 */ = new T(function(){
  return B(A1(_N4/* GHC.Enum.lvl18 */,_MH/* GHC.Enum.lvl */));
}),
_N6/* lvl20 */ = new T2(1,_3c/* GHC.Show.shows8 */,_N5/* GHC.Enum.lvl19 */),
_N7/* lvl21 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */(") is outside of Int\'s bounds ", _N6/* GHC.Enum.lvl20 */));
}),
_N8/* show */ = function(_N9/* sfb3 */){
  return E(E(_N9/* sfb3 */).b);
},
_Na/* lvl22 */ = function(_Nb/* smEd */, _Nc/* smEe */, _Nd/* smEf */){
  var _Ne/* smEj */ = new T(function(){
    var _Nf/* smEi */ = new T(function(){
      return B(unAppCStr/* EXTERNAL */("}: value (", new T(function(){
        return B(_2/* GHC.Base.++ */(B(A2(_N8/* GHC.Show.show */,_Nd/* smEf */, _Nc/* smEe */)), _N7/* GHC.Enum.lvl21 */));
      })));
    },1);
    return B(_2/* GHC.Base.++ */(_Nb/* smEd */, _Nf/* smEi */));
  });
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.fromEnum{", _Ne/* smEj */)));});
},
_Ng/* fromEnumError */ = function(_Nh/* smEl */, _Ni/* smEm */, _Nj/* smEn */){
  return new F(function(){return _Na/* GHC.Enum.lvl22 */(_Ni/* smEm */, _Nj/* smEn */, _Nh/* smEl */);});
},
_Nk/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Int64"));
}),
_Nl/* lvl13 */ = function(_Nm/* s2dYH */){
  return new F(function(){return _Ng/* GHC.Enum.fromEnumError */(_MG/* GHC.Int.$fShowInt64 */, _Nk/* GHC.Int.lvl1 */, _Nm/* s2dYH */);});
},
_Nn/* $fEnumInt7 */ = function(_No/* s2dYI */){
  return new F(function(){return _Nl/* GHC.Int.lvl13 */(_No/* s2dYI */);});
},
_Np/* $fEnumInt9 */ = new T(function(){
  return hs_intToInt64/* EXTERNAL */(-2147483648);
}),
_Nq/* $w$cfromEnum */ = function(_Nr/* s2dYK */){
  var _Ns/* s2dYO */ = hs_geInt64/* EXTERNAL */(_Nr/* s2dYK */, E(_Np/* GHC.Int.$fEnumInt9 */));
  if(!_Ns/* s2dYO */){
    return new F(function(){return _Nn/* GHC.Int.$fEnumInt7 */(_Nr/* s2dYK */);});
  }else{
    var _Nt/* s2dYW */ = hs_leInt64/* EXTERNAL */(_Nr/* s2dYK */, E(_M6/* GHC.Int.$fEnumInt6 */));
    if(!_Nt/* s2dYW */){
      return new F(function(){return _Nn/* GHC.Int.$fEnumInt7 */(_Nr/* s2dYK */);});
    }else{
      var _Nu/* s2dZ2 */ = hs_int64ToInt/* EXTERNAL */(_Nr/* s2dYK */);
      return E(_Nu/* s2dZ2 */);
    }
  }
},
_Nv/* $fEnumInt64_$cfromEnum */ = function(_Nw/* s2dZ5 */){
  return new F(function(){return _Nq/* GHC.Int.$w$cfromEnum */(E(_Nw/* s2dZ5 */));});
},
_Nx/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}: tried to take `pred\' of minBound"));
}),
_Ny/* lvl2 */ = function(_Nz/* smrD */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.pred{", new T(function(){
    return B(_2/* GHC.Base.++ */(_Nz/* smrD */, _Nx/* GHC.Enum.lvl1 */));
  }))));});
},
_NA/* predError */ = function(_NB/* B1 */){
  return new F(function(){return _Ny/* GHC.Enum.lvl2 */(_NB/* B1 */);});
},
_NC/* $fEnumInt10 */ = new T(function(){
  return B(_NA/* GHC.Enum.predError */(_Nk/* GHC.Int.lvl1 */));
}),
_ND/* $w$cpred */ = function(_NE/* s2dXS */){
  var _NF/* s2dXU */ = hs_neInt64/* EXTERNAL */(_NE/* s2dXS */, new Long/* EXTERNAL */(0, -2147483648));
  if(!_NF/* s2dXU */){
    return E(_NC/* GHC.Int.$fEnumInt10 */);
  }else{
    var _NG/* s2dY0 */ = hs_minusInt64/* EXTERNAL */(_NE/* s2dXS */, new Long/* EXTERNAL */(1, 0));
    return E(_NG/* s2dY0 */);
  }
},
_NH/* $fEnumInt64_$cpred */ = function(_NI/* s2dY3 */){
  return new F(function(){return _ND/* GHC.Int.$w$cpred */(E(_NI/* s2dY3 */));});
},
_NJ/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}: tried to take `succ\' of maxBound"));
}),
_NK/* lvl4 */ = function(_NL/* smrG */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.succ{", new T(function(){
    return B(_2/* GHC.Base.++ */(_NL/* smrG */, _NJ/* GHC.Enum.lvl3 */));
  }))));});
},
_NM/* succError */ = function(_NB/* B1 */){
  return new F(function(){return _NK/* GHC.Enum.lvl4 */(_NB/* B1 */);});
},
_NN/* $fEnumInt11 */ = new T(function(){
  return B(_NM/* GHC.Enum.succError */(_Nk/* GHC.Int.lvl1 */));
}),
_NO/* $w$csucc */ = function(_NP/* s2dY7 */){
  var _NQ/* s2dY9 */ = hs_neInt64/* EXTERNAL */(_NP/* s2dY7 */, new Long/* EXTERNAL */(4294967295, 2147483647));
  if(!_NQ/* s2dY9 */){
    return E(_NN/* GHC.Int.$fEnumInt11 */);
  }else{
    var _NR/* s2dYf */ = hs_plusInt64/* EXTERNAL */(_NP/* s2dY7 */, new Long/* EXTERNAL */(1, 0));
    return E(_NR/* s2dYf */);
  }
},
_NS/* $fEnumInt64_$csucc */ = function(_NT/* s2dYi */){
  return new F(function(){return _NO/* GHC.Int.$w$csucc */(E(_NT/* s2dYi */));});
},
_NU/* $fEnumInt64_$ctoEnum */ = function(_NV/* s2dXL */){
  return new F(function(){return hs_intToInt64/* EXTERNAL */(E(_NV/* s2dXL */));});
},
_NW/* $fEnumInt64 */ = new T(function(){
  return {_:0,a:_NS/* GHC.Int.$fEnumInt64_$csucc */,b:_NH/* GHC.Int.$fEnumInt64_$cpred */,c:_NU/* GHC.Int.$fEnumInt64_$ctoEnum */,d:_Nv/* GHC.Int.$fEnumInt64_$cfromEnum */,e:_KK/* GHC.Int.$fEnumInt64_$cenumFrom */,f:_LK/* GHC.Int.$fEnumInt64_$cenumFromThen */,g:_M5/* GHC.Int.$fEnumInt64_$cenumFromTo */,h:_LW/* GHC.Int.$fEnumInt64_$cenumFromThenTo */};
}),
_NX/* minusInt64# */ = function(_NY/* sdC */, _NZ/* sdD */){
  var _O0/* sdF */ = hs_minusInt64/* EXTERNAL */(_NY/* sdC */, _NZ/* sdD */);
  return E(_O0/* sdF */);
},
_O1/* quotInt64# */ = function(_O2/* sdk */, _O3/* sdl */){
  var _O4/* sdn */ = hs_quotInt64/* EXTERNAL */(_O2/* sdk */, _O3/* sdl */);
  return E(_O4/* sdn */);
},
_O5/* divInt64# */ = function(_O6/* s2dwk */, _O7/* s2dwl */){
  var _O8/* s2dwn */ = hs_intToInt64/* EXTERNAL */(1),
  _O9/* s2dwp */ = _O8/* s2dwn */,
  _Oa/* s2dwr */ = hs_intToInt64/* EXTERNAL */(0),
  _Ob/* s2dwt */ = _Oa/* s2dwr */,
  _Oc/* s2dwv */ = hs_gtInt64/* EXTERNAL */(_O6/* s2dwk */, _Ob/* s2dwt */),
  _Od/* s2dwy */ = function(_Oe/* s2dwz */){
    var _Of/* s2dwB */ = hs_ltInt64/* EXTERNAL */(_O6/* s2dwk */, _Ob/* s2dwt */);
    if(!_Of/* s2dwB */){
      return new F(function(){return _O1/* GHC.IntWord64.quotInt64# */(_O6/* s2dwk */, _O7/* s2dwl */);});
    }else{
      var _Og/* s2dwG */ = hs_gtInt64/* EXTERNAL */(_O7/* s2dwl */, _Ob/* s2dwt */);
      if(!_Og/* s2dwG */){
        return new F(function(){return _O1/* GHC.IntWord64.quotInt64# */(_O6/* s2dwk */, _O7/* s2dwl */);});
      }else{
        var _Oh/* s2dwL */ = hs_plusInt64/* EXTERNAL */(_O6/* s2dwk */, _O9/* s2dwp */),
        _Oi/* s2dwP */ = hs_quotInt64/* EXTERNAL */(_Oh/* s2dwL */, _O7/* s2dwl */);
        return new F(function(){return _NX/* GHC.IntWord64.minusInt64# */(_Oi/* s2dwP */, _O9/* s2dwp */);});
      }
    }
  };
  if(!_Oc/* s2dwv */){
    return new F(function(){return _Od/* s2dwy */(_/* EXTERNAL */);});
  }else{
    var _Oj/* s2dwU */ = hs_ltInt64/* EXTERNAL */(_O7/* s2dwl */, _Ob/* s2dwt */);
    if(!_Oj/* s2dwU */){
      return new F(function(){return _Od/* s2dwy */(_/* EXTERNAL */);});
    }else{
      var _Ok/* s2dwZ */ = hs_minusInt64/* EXTERNAL */(_O6/* s2dwk */, _O9/* s2dwp */),
      _Ol/* s2dx3 */ = hs_quotInt64/* EXTERNAL */(_Ok/* s2dwZ */, _O7/* s2dwl */);
      return new F(function(){return _NX/* GHC.IntWord64.minusInt64# */(_Ol/* s2dx3 */, _O9/* s2dwp */);});
    }
  }
},
_Om/* $fExceptionArithException_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_On/* $fExceptionArithException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.Exception"));
}),
_Oo/* $fExceptionArithException_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ArithException"));
}),
_Op/* $fExceptionArithException_wild */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_Om/* GHC.Exception.$fExceptionArithException_ww2 */,_On/* GHC.Exception.$fExceptionArithException_ww4 */,_Oo/* GHC.Exception.$fExceptionArithException_ww5 */),
_Oq/* $fExceptionArithException8 */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_Op/* GHC.Exception.$fExceptionArithException_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_Or/* $fExceptionArithException7 */ = function(_Os/* s2S2z */){
  return E(_Oq/* GHC.Exception.$fExceptionArithException8 */);
},
_Ot/* $fExceptionArithException_$cfromException */ = function(_Ou/* s2S35 */){
  var _Ov/* s2S36 */ = E(_Ou/* s2S35 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_Ov/* s2S36 */.a)), _Or/* GHC.Exception.$fExceptionArithException7 */, _Ov/* s2S36 */.b);});
},
_Ow/* $fExceptionArithException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ratio has zero denominator"));
}),
_Ox/* $fExceptionArithException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("denormal"));
}),
_Oy/* $fExceptionArithException3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("divide by zero"));
}),
_Oz/* $fExceptionArithException4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("loss of precision"));
}),
_OA/* $fExceptionArithException5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic underflow"));
}),
_OB/* $fExceptionArithException6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic overflow"));
}),
_OC/* $w$cshowsPrec */ = function(_OD/* s2S3a */, _OE/* s2S3b */){
  switch(E(_OD/* s2S3a */)){
    case 0:
      return new F(function(){return _2/* GHC.Base.++ */(_OB/* GHC.Exception.$fExceptionArithException6 */, _OE/* s2S3b */);});
      break;
    case 1:
      return new F(function(){return _2/* GHC.Base.++ */(_OA/* GHC.Exception.$fExceptionArithException5 */, _OE/* s2S3b */);});
      break;
    case 2:
      return new F(function(){return _2/* GHC.Base.++ */(_Oz/* GHC.Exception.$fExceptionArithException4 */, _OE/* s2S3b */);});
      break;
    case 3:
      return new F(function(){return _2/* GHC.Base.++ */(_Oy/* GHC.Exception.$fExceptionArithException3 */, _OE/* s2S3b */);});
      break;
    case 4:
      return new F(function(){return _2/* GHC.Base.++ */(_Ox/* GHC.Exception.$fExceptionArithException2 */, _OE/* s2S3b */);});
      break;
    default:
      return new F(function(){return _2/* GHC.Base.++ */(_Ow/* GHC.Exception.$fExceptionArithException1 */, _OE/* s2S3b */);});
  }
},
_OF/* $fExceptionArithException_$cshow */ = function(_OG/* s2S3g */){
  return new F(function(){return _OC/* GHC.Exception.$w$cshowsPrec */(_OG/* s2S3g */, _6/* GHC.Types.[] */);});
},
_OH/* $fExceptionArithException_$cshowsPrec */ = function(_OI/* s2S3d */, _OJ/* s2S3e */, _OK/* s2S3f */){
  return new F(function(){return _OC/* GHC.Exception.$w$cshowsPrec */(_OJ/* s2S3e */, _OK/* s2S3f */);});
},
_OL/* $fShowArithException_$cshowList */ = function(_OM/* s2S3h */, _ON/* s2S3i */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_OC/* GHC.Exception.$w$cshowsPrec */, _OM/* s2S3h */, _ON/* s2S3i */);});
},
_OO/* $fShowArithException */ = new T3(0,_OH/* GHC.Exception.$fExceptionArithException_$cshowsPrec */,_OF/* GHC.Exception.$fExceptionArithException_$cshow */,_OL/* GHC.Exception.$fShowArithException_$cshowList */),
_OP/* $fExceptionArithException */ = new T(function(){
  return new T5(0,_Or/* GHC.Exception.$fExceptionArithException7 */,_OO/* GHC.Exception.$fShowArithException */,_OQ/* GHC.Exception.$fExceptionArithException_$ctoException */,_Ot/* GHC.Exception.$fExceptionArithException_$cfromException */,_OF/* GHC.Exception.$fExceptionArithException_$cshow */);
}),
_OQ/* $fExceptionArithException_$ctoException */ = function(_OR/* B1 */){
  return new T2(0,_OP/* GHC.Exception.$fExceptionArithException */,_OR/* B1 */);
},
_OS/* DivideByZero */ = 3,
_OT/* divZeroException */ = new T(function(){
  return B(_OQ/* GHC.Exception.$fExceptionArithException_$ctoException */(_OS/* GHC.Exception.DivideByZero */));
}),
_OU/* divZeroError */ = new T(function(){
  return die/* EXTERNAL */(_OT/* GHC.Exception.divZeroException */);
}),
_OV/* Overflow */ = 0,
_OW/* overflowException */ = new T(function(){
  return B(_OQ/* GHC.Exception.$fExceptionArithException_$ctoException */(_OV/* GHC.Exception.Overflow */));
}),
_OX/* overflowError */ = new T(function(){
  return die/* EXTERNAL */(_OW/* GHC.Exception.overflowException */);
}),
_OY/* $w$cdiv2 */ = function(_OZ/* s2e0N */, _P0/* s2e0O */){
  var _P1/* s2e0Q */ = hs_eqInt64/* EXTERNAL */(_P0/* s2e0O */, new Long/* EXTERNAL */(0, 0));
  if(!_P1/* s2e0Q */){
    var _P2/* s2e0V */ = hs_eqInt64/* EXTERNAL */(_P0/* s2e0O */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_P2/* s2e0V */){
      return new F(function(){return _O5/* GHC.Int.divInt64# */(_OZ/* s2e0N */, _P0/* s2e0O */);});
    }else{
      var _P3/* s2e10 */ = hs_eqInt64/* EXTERNAL */(_OZ/* s2e0N */, new Long/* EXTERNAL */(0, -2147483648));
      if(!_P3/* s2e10 */){
        return new F(function(){return _O5/* GHC.Int.divInt64# */(_OZ/* s2e0N */, _P0/* s2e0O */);});
      }else{
        return E(_OX/* GHC.Real.overflowError */);
      }
    }
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_P4/* $fIntegralInt64_$cdiv */ = function(_P5/* s2e16 */, _P6/* s2e17 */){
  return new F(function(){return _OY/* GHC.Int.$w$cdiv2 */(E(_P5/* s2e16 */), E(_P6/* s2e17 */));});
},
_P7/* $fIntegralInt1 */ = new Long/* EXTERNAL */(0, 0),
_P8/* plusInt64# */ = function(_P9/* sdw */, _Pa/* sdx */){
  var _Pb/* sdz */ = hs_plusInt64/* EXTERNAL */(_P9/* sdw */, _Pa/* sdx */);
  return E(_Pb/* sdz */);
},
_Pc/* modInt64# */ = function(_Pd/* s2dvH */, _Pe/* s2dvI */){
  var _Pf/* s2dvK */ = hs_remInt64/* EXTERNAL */(_Pd/* s2dvH */, _Pe/* s2dvI */),
  _Pg/* s2dvM */ = _Pf/* s2dvK */,
  _Ph/* s2dvO */ = hs_intToInt64/* EXTERNAL */(0),
  _Pi/* s2dvQ */ = _Ph/* s2dvO */,
  _Pj/* s2dvS */ = hs_gtInt64/* EXTERNAL */(_Pd/* s2dvH */, _Pi/* s2dvQ */),
  _Pk/* s2dvV */ = function(_Pl/* s2dvW */){
    var _Pm/* s2dvY */ = hs_neInt64/* EXTERNAL */(_Pg/* s2dvM */, _Pi/* s2dvQ */);
    if(!_Pm/* s2dvY */){
      return E(_Pi/* s2dvQ */);
    }else{
      return new F(function(){return _P8/* GHC.IntWord64.plusInt64# */(_Pg/* s2dvM */, _Pe/* s2dvI */);});
    }
  },
  _Pn/* s2dw2 */ = function(_Po/* s2dw3 */){
    var _Pp/* s2dw5 */ = hs_ltInt64/* EXTERNAL */(_Pd/* s2dvH */, _Pi/* s2dvQ */);
    if(!_Pp/* s2dw5 */){
      return E(_Pg/* s2dvM */);
    }else{
      var _Pq/* s2dwa */ = hs_gtInt64/* EXTERNAL */(_Pe/* s2dvI */, _Pi/* s2dvQ */);
      if(!_Pq/* s2dwa */){
        return E(_Pg/* s2dvM */);
      }else{
        return new F(function(){return _Pk/* s2dvV */(_/* EXTERNAL */);});
      }
    }
  };
  if(!_Pj/* s2dvS */){
    return new F(function(){return _Pn/* s2dw2 */(_/* EXTERNAL */);});
  }else{
    var _Pr/* s2dwg */ = hs_ltInt64/* EXTERNAL */(_Pe/* s2dvI */, _Pi/* s2dvQ */);
    if(!_Pr/* s2dwg */){
      return new F(function(){return _Pn/* s2dw2 */(_/* EXTERNAL */);});
    }else{
      return new F(function(){return _Pk/* s2dvV */(_/* EXTERNAL */);});
    }
  }
},
_Ps/* $w$cdivMod2 */ = function(_Pt/* s2dZ9 */, _Pu/* s2dZa */){
  var _Pv/* s2dZc */ = hs_eqInt64/* EXTERNAL */(_Pu/* s2dZa */, new Long/* EXTERNAL */(0, 0));
  if(!_Pv/* s2dZc */){
    var _Pw/* s2dZh */ = hs_eqInt64/* EXTERNAL */(_Pu/* s2dZa */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Pw/* s2dZh */){
      return new T2(0,new T(function(){
        return B(_O5/* GHC.Int.divInt64# */(_Pt/* s2dZ9 */, _Pu/* s2dZa */));
      }),new T(function(){
        return B(_Pc/* GHC.Int.modInt64# */(_Pt/* s2dZ9 */, _Pu/* s2dZa */));
      }));
    }else{
      var _Px/* s2dZq */ = hs_eqInt64/* EXTERNAL */(_Pt/* s2dZ9 */, new Long/* EXTERNAL */(0, -2147483648));
      return (!_Px/* s2dZq */) ? new T2(0,new T(function(){
        return B(_O5/* GHC.Int.divInt64# */(_Pt/* s2dZ9 */, _Pu/* s2dZa */));
      }),new T(function(){
        return B(_Pc/* GHC.Int.modInt64# */(_Pt/* s2dZ9 */, _Pu/* s2dZa */));
      })) : new T2(0,_OX/* GHC.Real.overflowError */,_P7/* GHC.Int.$fIntegralInt1 */);
    }
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_Py/* $fIntegralInt64_$cdivMod */ = function(_Pz/* s2dZz */, _PA/* s2dZA */){
  var _PB/* s2dZF */ = B(_Ps/* GHC.Int.$w$cdivMod2 */(E(_Pz/* s2dZz */), E(_PA/* s2dZA */)));
  return new T2(0,_PB/* s2dZF */.a,_PB/* s2dZF */.b);
},
_PC/* $w$cmod */ = function(_PD/* s2e0t */, _PE/* s2e0u */){
  var _PF/* s2e0w */ = hs_eqInt64/* EXTERNAL */(_PE/* s2e0u */, new Long/* EXTERNAL */(0, 0));
  if(!_PF/* s2e0w */){
    var _PG/* s2e0B */ = hs_eqInt64/* EXTERNAL */(_PE/* s2e0u */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_PG/* s2e0B */){
      return new F(function(){return _Pc/* GHC.Int.modInt64# */(_PD/* s2e0t */, _PE/* s2e0u */);});
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_PH/* $fIntegralInt64_$cmod */ = function(_PI/* s2e0G */, _PJ/* s2e0H */){
  return new F(function(){return _PC/* GHC.Int.$w$cmod */(E(_PI/* s2e0G */), E(_PJ/* s2e0H */));});
},
_PK/* $w$cquot */ = function(_PL/* s2e1B */, _PM/* s2e1C */){
  var _PN/* s2e1E */ = hs_eqInt64/* EXTERNAL */(_PM/* s2e1C */, new Long/* EXTERNAL */(0, 0));
  if(!_PN/* s2e1E */){
    var _PO/* s2e1J */ = hs_eqInt64/* EXTERNAL */(_PM/* s2e1C */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_PO/* s2e1J */){
      var _PP/* s2e1O */ = hs_quotInt64/* EXTERNAL */(_PL/* s2e1B */, _PM/* s2e1C */);
      return E(_PP/* s2e1O */);
    }else{
      var _PQ/* s2e1S */ = hs_eqInt64/* EXTERNAL */(_PL/* s2e1B */, new Long/* EXTERNAL */(0, -2147483648));
      if(!_PQ/* s2e1S */){
        var _PR/* s2e1X */ = hs_quotInt64/* EXTERNAL */(_PL/* s2e1B */, _PM/* s2e1C */);
        return E(_PR/* s2e1X */);
      }else{
        return E(_OX/* GHC.Real.overflowError */);
      }
    }
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_PS/* $fIntegralInt64_$cquot */ = function(_PT/* s2e22 */, _PU/* s2e23 */){
  return new F(function(){return _PK/* GHC.Int.$w$cquot */(E(_PT/* s2e22 */), E(_PU/* s2e23 */));});
},
_PV/* $w$cquotRem */ = function(_PW/* s2dZI */, _PX/* s2dZJ */){
  var _PY/* s2dZL */ = hs_eqInt64/* EXTERNAL */(_PX/* s2dZJ */, new Long/* EXTERNAL */(0, 0));
  if(!_PY/* s2dZL */){
    var _PZ/* s2dZQ */ = hs_eqInt64/* EXTERNAL */(_PX/* s2dZJ */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_PZ/* s2dZQ */){
      return new T2(0,new T(function(){
        return hs_quotInt64/* EXTERNAL */(_PW/* s2dZI */, _PX/* s2dZJ */);
      }),new T(function(){
        return hs_remInt64/* EXTERNAL */(_PW/* s2dZI */, _PX/* s2dZJ */);
      }));
    }else{
      var _Q0/* s2e05 */ = hs_eqInt64/* EXTERNAL */(_PW/* s2dZI */, new Long/* EXTERNAL */(0, -2147483648));
      return (!_Q0/* s2e05 */) ? new T2(0,new T(function(){
        return hs_quotInt64/* EXTERNAL */(_PW/* s2dZI */, _PX/* s2dZJ */);
      }),new T(function(){
        return hs_remInt64/* EXTERNAL */(_PW/* s2dZI */, _PX/* s2dZJ */);
      })) : new T2(0,_OX/* GHC.Real.overflowError */,_P7/* GHC.Int.$fIntegralInt1 */);
    }
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_Q1/* $fIntegralInt64_$cquotRem */ = function(_Q2/* s2e0k */, _Q3/* s2e0l */){
  var _Q4/* s2e0q */ = B(_PV/* GHC.Int.$w$cquotRem */(E(_Q2/* s2e0k */), E(_Q3/* s2e0l */)));
  return new T2(0,_Q4/* s2e0q */.a,_Q4/* s2e0q */.b);
},
_Q5/* $w$crem */ = function(_Q6/* s2e1d */, _Q7/* s2e1e */){
  var _Q8/* s2e1g */ = hs_eqInt64/* EXTERNAL */(_Q7/* s2e1e */, new Long/* EXTERNAL */(0, 0));
  if(!_Q8/* s2e1g */){
    var _Q9/* s2e1l */ = hs_eqInt64/* EXTERNAL */(_Q7/* s2e1e */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Q9/* s2e1l */){
      var _Qa/* s2e1q */ = hs_remInt64/* EXTERNAL */(_Q6/* s2e1d */, _Q7/* s2e1e */);
      return E(_Qa/* s2e1q */);
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_Qb/* $fIntegralInt64_$crem */ = function(_Qc/* s2e1u */, _Qd/* s2e1v */){
  return new F(function(){return _Q5/* GHC.Int.$w$crem */(E(_Qc/* s2e1u */), E(_Qd/* s2e1v */));});
},
_Qe/* $fBitsInt64_$c/= */ = function(_Qf/* s2dV3 */, _Qg/* s2dV4 */){
  return new F(function(){return hs_neInt64/* EXTERNAL */(E(_Qf/* s2dV3 */), E(_Qg/* s2dV4 */));});
},
_Qh/* $fEqInt64_$c== */ = function(_Qi/* s2dVd */, _Qj/* s2dVe */){
  return new F(function(){return hs_eqInt64/* EXTERNAL */(E(_Qi/* s2dVd */), E(_Qj/* s2dVe */));});
},
_Qk/* $fEqInt64 */ = new T2(0,_Qh/* GHC.Int.$fEqInt64_$c== */,_Qe/* GHC.Int.$fBitsInt64_$c/= */),
_Ql/* $fOrdInt64_$c< */ = function(_Qm/* s2dWd */, _Qn/* s2dWe */){
  return new F(function(){return hs_ltInt64/* EXTERNAL */(E(_Qm/* s2dWd */), E(_Qn/* s2dWe */));});
},
_Qo/* $fOrdInt64_$c<= */ = function(_Qp/* s2dW3 */, _Qq/* s2dW4 */){
  return new F(function(){return hs_leInt64/* EXTERNAL */(E(_Qp/* s2dW3 */), E(_Qq/* s2dW4 */));});
},
_Qr/* $fOrdInt64_$c> */ = function(_Qs/* s2dVT */, _Qt/* s2dVU */){
  return new F(function(){return hs_gtInt64/* EXTERNAL */(E(_Qs/* s2dVT */), E(_Qt/* s2dVU */));});
},
_Qu/* $fOrdInt64_$c>= */ = function(_Qv/* s2dVJ */, _Qw/* s2dVK */){
  return new F(function(){return hs_geInt64/* EXTERNAL */(E(_Qv/* s2dVJ */), E(_Qw/* s2dVK */));});
},
_Qx/* $w$ccompare */ = function(_Qy/* s2dWn */, _Qz/* s2dWo */){
  var _QA/* s2dWq */ = hs_eqInt64/* EXTERNAL */(_Qy/* s2dWn */, _Qz/* s2dWo */);
  if(!_QA/* s2dWq */){
    var _QB/* s2dWv */ = hs_leInt64/* EXTERNAL */(_Qy/* s2dWn */, _Qz/* s2dWo */);
    return (!_QB/* s2dWv */) ? 2 : 0;
  }else{
    return 1;
  }
},
_QC/* $fOrdInt64_$ccompare */ = function(_QD/* s2dWz */, _QE/* s2dWA */){
  return new F(function(){return _Qx/* GHC.Int.$w$ccompare */(E(_QD/* s2dWz */), E(_QE/* s2dWA */));});
},
_QF/* $fOrdInt64_$cmax */ = function(_QG/* s2dVy */, _QH/* s2dVz */){
  var _QI/* s2dVA */ = E(_QG/* s2dVy */),
  _QJ/* s2dVC */ = E(_QH/* s2dVz */),
  _QK/* s2dVF */ = hs_leInt64/* EXTERNAL */(_QI/* s2dVA */, _QJ/* s2dVC */);
  return (!_QK/* s2dVF */) ? E(_QI/* s2dVA */) : E(_QJ/* s2dVC */);
},
_QL/* $fOrdInt64_$cmin */ = function(_QM/* s2dVn */, _QN/* s2dVo */){
  var _QO/* s2dVp */ = E(_QM/* s2dVn */),
  _QP/* s2dVr */ = E(_QN/* s2dVo */),
  _QQ/* s2dVu */ = hs_leInt64/* EXTERNAL */(_QO/* s2dVp */, _QP/* s2dVr */);
  return (!_QQ/* s2dVu */) ? E(_QP/* s2dVr */) : E(_QO/* s2dVp */);
},
_QR/* $fOrdInt64 */ = {_:0,a:_Qk/* GHC.Int.$fEqInt64 */,b:_QC/* GHC.Int.$fOrdInt64_$ccompare */,c:_Ql/* GHC.Int.$fOrdInt64_$c< */,d:_Qo/* GHC.Int.$fOrdInt64_$c<= */,e:_Qr/* GHC.Int.$fOrdInt64_$c> */,f:_Qu/* GHC.Int.$fOrdInt64_$c>= */,g:_QF/* GHC.Int.$fOrdInt64_$cmax */,h:_QL/* GHC.Int.$fOrdInt64_$cmin */},
_QS/* $fRealInt1 */ = new T1(0,1),
_QT/* eqInteger */ = function(_QU/* s1H2 */, _QV/* s1H3 */){
  var _QW/* s1H4 */ = E(_QU/* s1H2 */);
  if(!_QW/* s1H4 */._){
    var _QX/* s1H5 */ = _QW/* s1H4 */.a,
    _QY/* s1H6 */ = E(_QV/* s1H3 */);
    return (_QY/* s1H6 */._==0) ? _QX/* s1H5 */==_QY/* s1H6 */.a : (I_compareInt/* EXTERNAL */(_QY/* s1H6 */.a, _QX/* s1H5 */)==0) ? true : false;
  }else{
    var _QZ/* s1Hc */ = _QW/* s1H4 */.a,
    _R0/* s1Hd */ = E(_QV/* s1H3 */);
    return (_R0/* s1Hd */._==0) ? (I_compareInt/* EXTERNAL */(_QZ/* s1Hc */, _R0/* s1Hd */.a)==0) ? true : false : (I_compare/* EXTERNAL */(_QZ/* s1Hc */, _R0/* s1Hd */.a)==0) ? true : false;
  }
},
_R1/* even1 */ = new T1(0,0),
_R2/* remInteger */ = function(_R3/* s1NY */, _R4/* s1NZ */){
  while(1){
    var _R5/* s1O0 */ = E(_R3/* s1NY */);
    if(!_R5/* s1O0 */._){
      var _R6/* s1O2 */ = E(_R5/* s1O0 */.a);
      if(_R6/* s1O2 */==(-2147483648)){
        _R3/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _R7/* s1O3 */ = E(_R4/* s1NZ */);
        if(!_R7/* s1O3 */._){
          return new T1(0,_R6/* s1O2 */%_R7/* s1O3 */.a);
        }else{
          _R3/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(_R6/* s1O2 */));
          _R4/* s1NZ */ = _R7/* s1O3 */;
          continue;
        }
      }
    }else{
      var _R8/* s1Od */ = _R5/* s1O0 */.a,
      _R9/* s1Oe */ = E(_R4/* s1NZ */);
      return (_R9/* s1Oe */._==0) ? new T1(1,I_rem/* EXTERNAL */(_R8/* s1Od */, I_fromInt/* EXTERNAL */(_R9/* s1Oe */.a))) : new T1(1,I_rem/* EXTERNAL */(_R8/* s1Od */, _R9/* s1Oe */.a));
    }
  }
},
_Ra/* $fIntegralInteger_$crem */ = function(_Rb/* svus */, _Rc/* svut */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_Rc/* svut */, _R1/* GHC.Real.even1 */))){
    return new F(function(){return _R2/* GHC.Integer.Type.remInteger */(_Rb/* svus */, _Rc/* svut */);});
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_Rd/* $fEnumRatio_gcd' */ = function(_Re/* svuv */, _Rf/* svuw */){
  while(1){
    if(!B(_QT/* GHC.Integer.Type.eqInteger */(_Rf/* svuw */, _R1/* GHC.Real.even1 */))){
      var _Rg/*  svuv */ = _Rf/* svuw */,
      _Rh/*  svuw */ = B(_Ra/* GHC.Real.$fIntegralInteger_$crem */(_Re/* svuv */, _Rf/* svuw */));
      _Re/* svuv */ = _Rg/*  svuv */;
      _Rf/* svuw */ = _Rh/*  svuw */;
      continue;
    }else{
      return E(_Re/* svuv */);
    }
  }
},
_Ri/* absInteger */ = function(_Rj/* s1QP */){
  var _Rk/* s1QQ */ = E(_Rj/* s1QP */);
  if(!_Rk/* s1QQ */._){
    var _Rl/* s1QS */ = E(_Rk/* s1QQ */.a);
    return (_Rl/* s1QS */==(-2147483648)) ? E(_JQ/* GHC.Integer.Type.lvl3 */) : (_Rl/* s1QS */<0) ? new T1(0, -_Rl/* s1QS */) : E(_Rk/* s1QQ */);
  }else{
    var _Rm/* s1QW */ = _Rk/* s1QQ */.a;
    return (I_compareInt/* EXTERNAL */(_Rm/* s1QW */, 0)>=0) ? E(_Rk/* s1QQ */) : new T1(1,I_negate/* EXTERNAL */(_Rm/* s1QW */));
  }
},
_Rn/* quotInteger */ = function(_Ro/* s1On */, _Rp/* s1Oo */){
  while(1){
    var _Rq/* s1Op */ = E(_Ro/* s1On */);
    if(!_Rq/* s1Op */._){
      var _Rr/* s1Or */ = E(_Rq/* s1Op */.a);
      if(_Rr/* s1Or */==(-2147483648)){
        _Ro/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _Rs/* s1Os */ = E(_Rp/* s1Oo */);
        if(!_Rs/* s1Os */._){
          return new T1(0,quot/* EXTERNAL */(_Rr/* s1Or */, _Rs/* s1Os */.a));
        }else{
          _Ro/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(_Rr/* s1Or */));
          _Rp/* s1Oo */ = _Rs/* s1Os */;
          continue;
        }
      }
    }else{
      var _Rt/* s1OC */ = _Rq/* s1Op */.a,
      _Ru/* s1OD */ = E(_Rp/* s1Oo */);
      return (_Ru/* s1OD */._==0) ? new T1(0,I_toInt/* EXTERNAL */(I_quot/* EXTERNAL */(_Rt/* s1OC */, I_fromInt/* EXTERNAL */(_Ru/* s1OD */.a)))) : new T1(1,I_quot/* EXTERNAL */(_Rt/* s1OC */, _Ru/* s1OD */.a));
    }
  }
},
_Rv/* RatioZeroDenominator */ = 5,
_Rw/* ratioZeroDenomException */ = new T(function(){
  return B(_OQ/* GHC.Exception.$fExceptionArithException_$ctoException */(_Rv/* GHC.Exception.RatioZeroDenominator */));
}),
_Rx/* ratioZeroDenominatorError */ = new T(function(){
  return die/* EXTERNAL */(_Rw/* GHC.Exception.ratioZeroDenomException */);
}),
_Ry/* $w$sreduce */ = function(_Rz/* svvD */, _RA/* svvE */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_RA/* svvE */, _R1/* GHC.Real.even1 */))){
    var _RB/* svvG */ = B(_Rd/* GHC.Real.$fEnumRatio_gcd' */(B(_Ri/* GHC.Integer.Type.absInteger */(_Rz/* svvD */)), B(_Ri/* GHC.Integer.Type.absInteger */(_RA/* svvE */))));
    return (!B(_QT/* GHC.Integer.Type.eqInteger */(_RB/* svvG */, _R1/* GHC.Real.even1 */))) ? new T2(0,B(_Rn/* GHC.Integer.Type.quotInteger */(_Rz/* svvD */, _RB/* svvG */)),B(_Rn/* GHC.Integer.Type.quotInteger */(_RA/* svvE */, _RB/* svvG */))) : E(_OU/* GHC.Real.divZeroError */);
  }else{
    return E(_Rx/* GHC.Real.ratioZeroDenominatorError */);
  }
},
_RC/* timesInteger */ = function(_RD/* s1PN */, _RE/* s1PO */){
  while(1){
    var _RF/* s1PP */ = E(_RD/* s1PN */);
    if(!_RF/* s1PP */._){
      var _RG/* s1PQ */ = _RF/* s1PP */.a,
      _RH/* s1PR */ = E(_RE/* s1PO */);
      if(!_RH/* s1PR */._){
        var _RI/* s1PS */ = _RH/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_RG/* s1PQ */, _RI/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_RG/* s1PQ */, _RI/* s1PS */)|0);
        }else{
          _RD/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_RG/* s1PQ */));
          _RE/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_RI/* s1PS */));
          continue;
        }
      }else{
        _RD/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_RG/* s1PQ */));
        _RE/* s1PO */ = _RH/* s1PR */;
        continue;
      }
    }else{
      var _RJ/* s1Q6 */ = E(_RE/* s1PO */);
      if(!_RJ/* s1Q6 */._){
        _RD/* s1PN */ = _RF/* s1PP */;
        _RE/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_RJ/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_RF/* s1PP */.a, _RJ/* s1Q6 */.a));
      }
    }
  }
},
_RK/* $fRealInt64_$ctoRational */ = function(_RL/* s2e6O */){
  var _RM/* s2e6T */ = B(_Ry/* GHC.Real.$w$sreduce */(B(_RC/* GHC.Integer.Type.timesInteger */(B(_M9/* GHC.Integer.Type.int64ToInteger */(E(_RL/* s2e6O */))), _QS/* GHC.Int.$fRealInt1 */)), _QS/* GHC.Int.$fRealInt1 */));
  return new T2(0,E(_RM/* s2e6T */.a),E(_RM/* s2e6T */.b));
},
_RN/* $fRealInt64 */ = new T3(0,_Jp/* GHC.Int.$fNumInt64 */,_QR/* GHC.Int.$fOrdInt64 */,_RK/* GHC.Int.$fRealInt64_$ctoRational */),
_KM/* $fIntegralInt64 */ = new T(function(){
  return {_:0,a:_RN/* GHC.Int.$fRealInt64 */,b:_NW/* GHC.Int.$fEnumInt64 */,c:_PS/* GHC.Int.$fIntegralInt64_$cquot */,d:_Qb/* GHC.Int.$fIntegralInt64_$crem */,e:_P4/* GHC.Int.$fIntegralInt64_$cdiv */,f:_PH/* GHC.Int.$fIntegralInt64_$cmod */,g:_Q1/* GHC.Int.$fIntegralInt64_$cquotRem */,h:_Py/* GHC.Int.$fIntegralInt64_$cdivMod */,i:_Mg/* GHC.Int.$fIntegralInt64_$ctoInteger */};
}),
_RO/* $p1Ord */ = function(_RP/* scBR */){
  return E(E(_RP/* scBR */).a);
},
_RQ/* $p2Real */ = function(_RR/* svfR */){
  return E(E(_RR/* svfR */).b);
},
_RS/* == */ = function(_RT/* scBJ */){
  return E(E(_RT/* scBJ */).a);
},
_RU/* even2 */ = new T1(0,2),
_RV/* rem */ = function(_RW/* sveI */){
  return E(E(_RW/* sveI */).d);
},
_RX/* even */ = function(_RY/* svre */, _RZ/* svrf */){
  var _S0/* svrg */ = B(_Kk/* GHC.Real.$p1Integral */(_RY/* svre */)),
  _S1/* svrh */ = new T(function(){
    return B(_Km/* GHC.Real.$p1Real */(_S0/* svrg */));
  }),
  _S2/* svrl */ = new T(function(){
    return B(A3(_RV/* GHC.Real.rem */,_RY/* svre */, _RZ/* svrf */, new T(function(){
      return B(A2(_Ko/* GHC.Num.fromInteger */,_S1/* svrh */, _RU/* GHC.Real.even2 */));
    })));
  });
  return new F(function(){return A3(_RS/* GHC.Classes.== */,B(_RO/* GHC.Classes.$p1Ord */(B(_RQ/* GHC.Real.$p2Real */(_S0/* svrg */)))), _S2/* svrl */, new T(function(){
    return B(A2(_Ko/* GHC.Num.fromInteger */,_S1/* svrh */, _R1/* GHC.Real.even1 */));
  }));});
},
_S3/* $wg1 */ = function(_S4/*  sfnl */, _S5/*  sfnm */, _S6/*  sfnn */){
  while(1){
    var _S7/*  $wg1 */ = B((function(_S8/* sfnl */, _S9/* sfnm */, _Sa/* sfnn */){
      if(!B(_RX/* GHC.Real.even */(_KM/* GHC.Int.$fIntegralInt64 */, _S9/* sfnm */))){
        var _Sb/* sfnr */ = hs_eqInt64/* EXTERNAL */(_S9/* sfnm */, new Long/* EXTERNAL */(1, 0));
        if(!_Sb/* sfnr */){
          var _Sc/* sfnw */ = hs_minusInt64/* EXTERNAL */(_S9/* sfnm */, new Long/* EXTERNAL */(1, 0));
          _S4/*  sfnl */ = new T(function(){
            return B(_J2/* GHC.Int.$fNumInt64_$c* */(_S8/* sfnl */, _S8/* sfnl */));
          });
          _S5/*  sfnm */ = B(_PK/* GHC.Int.$w$cquot */(_Sc/* sfnw */, new Long/* EXTERNAL */(2, 0)));
          _S6/*  sfnn */ = new T(function(){
            return B(_J2/* GHC.Int.$fNumInt64_$c* */(_S8/* sfnl */, _Sa/* sfnn */));
          },1);
          return __continue/* EXTERNAL */;
        }else{
          var _Sd/* sfnH */ = hs_timesInt64/* EXTERNAL */(E(_S8/* sfnl */), E(_Sa/* sfnn */));
          return E(_Sd/* sfnH */);
        }
      }else{
        var _Se/*   sfnm */ = B(_PK/* GHC.Int.$w$cquot */(_S9/* sfnm */, new Long/* EXTERNAL */(2, 0))),
        _Sf/*   sfnn */ = _Sa/* sfnn */;
        _S4/*  sfnl */ = new T(function(){
          return B(_J2/* GHC.Int.$fNumInt64_$c* */(_S8/* sfnl */, _S8/* sfnl */));
        });
        _S5/*  sfnm */ = _Se/*   sfnm */;
        _S6/*  sfnn */ = _Sf/*   sfnn */;
        return __continue/* EXTERNAL */;
      }
    })(_S4/*  sfnl */, _S5/*  sfnm */, _S6/*  sfnn */));
    if(_S7/*  $wg1 */!=__continue/* EXTERNAL */){
      return _S7/*  $wg1 */;
    }
  }
},
_Sg/* $wf1 */ = function(_Sh/*  sfnM */, _Si/*  sfnN */){
  while(1){
    var _Sj/*  $wf1 */ = B((function(_Sk/* sfnM */, _Sl/* sfnN */){
      if(!B(_RX/* GHC.Real.even */(_KM/* GHC.Int.$fIntegralInt64 */, _Sl/* sfnN */))){
        var _Sm/* sfnR */ = hs_eqInt64/* EXTERNAL */(_Sl/* sfnN */, new Long/* EXTERNAL */(1, 0));
        if(!_Sm/* sfnR */){
          var _Sn/* sfnW */ = hs_minusInt64/* EXTERNAL */(_Sl/* sfnN */, new Long/* EXTERNAL */(1, 0));
          return new F(function(){return _S3/* System.Random.$wg1 */(new T(function(){
            return B(_J2/* GHC.Int.$fNumInt64_$c* */(_Sk/* sfnM */, _Sk/* sfnM */));
          }), B(_PK/* GHC.Int.$w$cquot */(_Sn/* sfnW */, new Long/* EXTERNAL */(2, 0))), _Sk/* sfnM */);});
        }else{
          return E(_Sk/* sfnM */);
        }
      }else{
        var _So/*   sfnN */ = B(_PK/* GHC.Int.$w$cquot */(_Sl/* sfnN */, new Long/* EXTERNAL */(2, 0)));
        _Sh/*  sfnM */ = new T(function(){
          return B(_J2/* GHC.Int.$fNumInt64_$c* */(_Sk/* sfnM */, _Sk/* sfnM */));
        });
        _Si/*  sfnN */ = _So/*   sfnN */;
        return __continue/* EXTERNAL */;
      }
    })(_Sh/*  sfnM */, _Si/*  sfnN */));
    if(_Sj/*  $wf1 */!=__continue/* EXTERNAL */){
      return _Sj/*  $wf1 */;
    }
  }
},
_Sp/* $w$s^ */ = function(_Sq/* sfoq */, _Sr/* sfor */){
  var _Ss/* sfot */ = hs_ltInt64/* EXTERNAL */(_Sr/* sfor */, new Long/* EXTERNAL */(0, 0));
  if(!_Ss/* sfot */){
    var _St/* sfoy */ = hs_eqInt64/* EXTERNAL */(_Sr/* sfor */, new Long/* EXTERNAL */(0, 0));
    if(!_St/* sfoy */){
      return new F(function(){return _Sg/* System.Random.$wf1 */(_Sq/* sfoq */, _Sr/* sfor */);});
    }else{
      return E(_Kf/* System.Random.$fRandomDouble6 */);
    }
  }else{
    return E(_Ke/* System.Random.$fRandomDouble5 */);
  }
},
_Su/* $fRandomDouble_twoto53 */ = new T(function(){
  return B(_Sp/* System.Random.$w$s^ */(_Kc/* System.Random.$fRandomDouble4 */, new Long/* EXTERNAL */(53, 0)));
}),
_Sv/* doubleFromInteger */ = function(_Sw/* s1M0 */){
  var _Sx/* s1M1 */ = E(_Sw/* s1M0 */);
  if(!_Sx/* s1M1 */._){
    return _Sx/* s1M1 */.a;
  }else{
    return new F(function(){return I_toNumber/* EXTERNAL */(_Sx/* s1M1 */.a);});
  }
},
_Sy/* $fRandomDouble3 */ = new T(function(){
  return B(_Sv/* GHC.Integer.Type.doubleFromInteger */(B(_M9/* GHC.Integer.Type.int64ToInteger */(E(_Su/* System.Random.$fRandomDouble_twoto53 */)))));
}),
_Sz/* $fRandomDouble7 */ = new T(function(){
  return hs_minusInt64/* EXTERNAL */(E(_Su/* System.Random.$fRandomDouble_twoto53 */), new Long/* EXTERNAL */(1, 0));
}),
_SA/* $w$c.&. */ = function(_SB/* s2e5n */, _SC/* s2e5o */){
  var _SD/* s2e5q */ = hs_int64ToWord64/* EXTERNAL */(_SC/* s2e5o */),
  _SE/* s2e5u */ = hs_int64ToWord64/* EXTERNAL */(_SB/* s2e5n */),
  _SF/* s2e5y */ = hs_and64/* EXTERNAL */(_SE/* s2e5u */, _SD/* s2e5q */),
  _SG/* s2e5C */ = hs_word64ToInt64/* EXTERNAL */(_SF/* s2e5y */);
  return E(_SG/* s2e5C */);
},
_SH/* $fRandomBool3 */ = new T1(0,1),
_SI/* $WStdGen */ = function(_SJ/* sfmR */, _SK/* sfmS */){
  return new T2(0,E(_SJ/* sfmR */),E(_SK/* sfmS */));
},
_SL/* $w$cnext */ = function(_SM/* sfqJ */, _SN/* sfqK */){
  var _SO/* sfqL */ = quot/* EXTERNAL */(_SN/* sfqK */, 52774),
  _SP/* sfqM */ = (imul/* EXTERNAL */(40692, _SN/* sfqK */-(imul/* EXTERNAL */(_SO/* sfqL */, 52774)|0)|0)|0)-(imul/* EXTERNAL */(_SO/* sfqL */, 3791)|0)|0,
  _SQ/* sfqR */ = new T(function(){
    if(_SP/* sfqM */>=0){
      return _SP/* sfqM */;
    }else{
      return _SP/* sfqM */+2147483399|0;
    }
  }),
  _SR/* sfqV */ = quot/* EXTERNAL */(_SM/* sfqJ */, 53668),
  _SS/* sfqW */ = (imul/* EXTERNAL */(40014, _SM/* sfqJ */-(imul/* EXTERNAL */(_SR/* sfqV */, 53668)|0)|0)|0)-(imul/* EXTERNAL */(_SR/* sfqV */, 12211)|0)|0,
  _ST/* sfr1 */ = new T(function(){
    if(_SS/* sfqW */>=0){
      return _SS/* sfqW */;
    }else{
      return _SS/* sfqW */+2147483563|0;
    }
  });
  return new T2(0,new T(function(){
    var _SU/* sfr9 */ = E(_ST/* sfr1 */)-E(_SQ/* sfqR */)|0;
    if(_SU/* sfr9 */>=1){
      return _SU/* sfr9 */;
    }else{
      return _SU/* sfr9 */+2147483562|0;
    }
  }),new T(function(){
    return B(_SI/* System.Random.$WStdGen */(_ST/* sfr1 */, _SQ/* sfqR */));
  }));
},
_SV/* b */ = new T1(0,2147483562),
_SW/* getStdRandom4 */ = new T1(0,0),
_SX/* lvl5 */ = new T1(0,1000),
_SY/* modInt# */ = function(_SZ/* scEd */, _T0/* scEe */){
  var _T1/* scEf */ = _SZ/* scEd */%_T0/* scEe */;
  if(_SZ/* scEd */<=0){
    if(_SZ/* scEd */>=0){
      return E(_T1/* scEf */);
    }else{
      if(_T0/* scEe */<=0){
        return E(_T1/* scEf */);
      }else{
        var _T2/* scEm */ = E(_T1/* scEf */);
        return (_T2/* scEm */==0) ? 0 : _T2/* scEm */+_T0/* scEe */|0;
      }
    }
  }else{
    if(_T0/* scEe */>=0){
      if(_SZ/* scEd */>=0){
        return E(_T1/* scEf */);
      }else{
        if(_T0/* scEe */<=0){
          return E(_T1/* scEf */);
        }else{
          var _T3/* scEt */ = E(_T1/* scEf */);
          return (_T3/* scEt */==0) ? 0 : _T3/* scEt */+_T0/* scEe */|0;
        }
      }
    }else{
      var _T4/* scEu */ = E(_T1/* scEf */);
      return (_T4/* scEu */==0) ? 0 : _T4/* scEu */+_T0/* scEe */|0;
    }
  }
},
_T5/* modInteger */ = function(_T6/* s1Na */, _T7/* s1Nb */){
  while(1){
    var _T8/* s1Nc */ = E(_T6/* s1Na */);
    if(!_T8/* s1Nc */._){
      var _T9/* s1Ne */ = E(_T8/* s1Nc */.a);
      if(_T9/* s1Ne */==(-2147483648)){
        _T6/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _Ta/* s1Nf */ = E(_T7/* s1Nb */);
        if(!_Ta/* s1Nf */._){
          return new T1(0,B(_SY/* GHC.Classes.modInt# */(_T9/* s1Ne */, _Ta/* s1Nf */.a)));
        }else{
          _T6/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(_T9/* s1Ne */));
          _T7/* s1Nb */ = _Ta/* s1Nf */;
          continue;
        }
      }
    }else{
      var _Tb/* s1Np */ = _T8/* s1Nc */.a,
      _Tc/* s1Nq */ = E(_T7/* s1Nb */);
      return (_Tc/* s1Nq */._==0) ? new T1(1,I_mod/* EXTERNAL */(_Tb/* s1Np */, I_fromInt/* EXTERNAL */(_Tc/* s1Nq */.a))) : new T1(1,I_mod/* EXTERNAL */(_Tb/* s1Np */, _Tc/* s1Nq */.a));
    }
  }
},
_Td/* $w$srandomIvalInteger */ = function(_Te/*  sfs7 */, _Tf/*  sfs8 */, _Tg/*  sfs9 */, _Th/*  sfsa */){
  while(1){
    var _Ti/*  $w$srandomIvalInteger */ = B((function(_Tj/* sfs7 */, _Tk/* sfs8 */, _Tl/* sfs9 */, _Tm/* sfsa */){
      if(!B(_Kq/* GHC.Integer.Type.gtInteger */(_Tk/* sfs8 */, _Tl/* sfs9 */))){
        var _Tn/* sfsc */ = B(_JH/* GHC.Integer.Type.plusInteger */(B(_Lm/* GHC.Integer.Type.minusInteger */(_Tl/* sfs9 */, _Tk/* sfs8 */)), _SH/* System.Random.$fRandomBool3 */)),
        _To/* sfsf */ = function(_Tp/* sfsg */, _Tq/* sfsh */, _Tr/* sfsi */){
          while(1){
            if(!B(_KO/* GHC.Integer.Type.geInteger */(_Tp/* sfsg */, B(_RC/* GHC.Integer.Type.timesInteger */(_Tn/* sfsc */, _SX/* System.Random.lvl5 */))))){
              var _Ts/* sfsk */ = E(_Tr/* sfsi */),
              _Tt/* sfsn */ = B(_SL/* System.Random.$w$cnext */(_Ts/* sfsk */.a, _Ts/* sfsk */.b)),
              _Tu/*  sfsg */ = B(_RC/* GHC.Integer.Type.timesInteger */(_Tp/* sfsg */, _SV/* System.Random.b */)),
              _Tv/*  sfsh */ = B(_JH/* GHC.Integer.Type.plusInteger */(B(_RC/* GHC.Integer.Type.timesInteger */(_Tq/* sfsh */, _SV/* System.Random.b */)), B(_Lm/* GHC.Integer.Type.minusInteger */(B(_M7/* GHC.Integer.Type.smallInteger */(E(_Tt/* sfsn */.a))), _SH/* System.Random.$fRandomBool3 */))));
              _Tp/* sfsg */ = _Tu/*  sfsg */;
              _Tq/* sfsh */ = _Tv/*  sfsh */;
              _Tr/* sfsi */ = _Tt/* sfsn */.b;
              continue;
            }else{
              return new T2(0,_Tq/* sfsh */,_Tr/* sfsi */);
            }
          }
        },
        _Tw/* sfsx */ = B(_To/* sfsf */(_SH/* System.Random.$fRandomBool3 */, _SW/* System.Random.getStdRandom4 */, _Tm/* sfsa */)),
        _Tx/* sfsE */ = new T(function(){
          return B(A2(_Ko/* GHC.Num.fromInteger */,_Tj/* sfs7 */, new T(function(){
            if(!B(_QT/* GHC.Integer.Type.eqInteger */(_Tn/* sfsc */, _SW/* System.Random.getStdRandom4 */))){
              return B(_JH/* GHC.Integer.Type.plusInteger */(_Tk/* sfs8 */, B(_T5/* GHC.Integer.Type.modInteger */(_Tw/* sfsx */.a, _Tn/* sfsc */))));
            }else{
              return E(_OU/* GHC.Real.divZeroError */);
            }
          })));
        });
        return new T2(0,_Tx/* sfsE */,_Tw/* sfsx */.b);
      }else{
        var _Ty/*   sfs7 */ = _Tj/* sfs7 */,
        _Tz/*   sfs8 */ = _Tl/* sfs9 */,
        _TA/*   sfs9 */ = _Tk/* sfs8 */,
        _TB/*   sfsa */ = _Tm/* sfsa */;
        _Te/*  sfs7 */ = _Ty/*   sfs7 */;
        _Tf/*  sfs8 */ = _Tz/*   sfs8 */;
        _Tg/*  sfs9 */ = _TA/*   sfs9 */;
        _Th/*  sfsa */ = _TB/*   sfsa */;
        return __continue/* EXTERNAL */;
      }
    })(_Te/*  sfs7 */, _Tf/*  sfs8 */, _Tg/*  sfs9 */, _Th/*  sfsa */));
    if(_Ti/*  $w$srandomIvalInteger */!=__continue/* EXTERNAL */){
      return _Ti/*  $w$srandomIvalInteger */;
    }
  }
},
_TC/* $w$s$crandom */ = function(_TD/* sfSt */){
  var _TE/* sfSu */ = B(_Td/* System.Random.$w$srandomIvalInteger */(_Jp/* GHC.Int.$fNumInt64 */, _Kb/* System.Random.$fRandomCLLong4 */, _K4/* System.Random.$fRandomCLLong3 */, _TD/* sfSt */));
  return new T2(0,new T(function(){
    return B(_Sv/* GHC.Integer.Type.doubleFromInteger */(B(_M9/* GHC.Integer.Type.int64ToInteger */(B(_SA/* GHC.Int.$w$c.&. */(E(_Sz/* System.Random.$fRandomDouble7 */), E(_TE/* sfSu */.a)))))))/E(_Sy/* System.Random.$fRandomDouble3 */);
  }),_TE/* sfSu */.b);
},
_TF/* $w$srandomRFloating2 */ = function(_TG/*  sfSX */, _TH/*  sfSY */, _TI/*  sfSZ */){
  while(1){
    var _TJ/*  $w$srandomRFloating2 */ = B((function(_TK/* sfSX */, _TL/* sfSY */, _TM/* sfSZ */){
      if(_TK/* sfSX */<=_TL/* sfSY */){
        var _TN/* sfT2 */ = new T(function(){
          var _TO/* sfT3 */ = B(_TC/* System.Random.$w$s$crandom */(_TM/* sfSZ */));
          return new T2(0,_TO/* sfT3 */.a,_TO/* sfT3 */.b);
        });
        return new T2(0,new T(function(){
          var _TP/* sfT9 */ = E(E(_TN/* sfT2 */).a);
          return 0.5*_TK/* sfSX */+_TP/* sfT9 */*(0.5*_TL/* sfSY */-0.5*_TK/* sfSX */)+0.5*_TK/* sfSX */+_TP/* sfT9 */*(0.5*_TL/* sfSY */-0.5*_TK/* sfSX */);
        }),new T(function(){
          return E(E(_TN/* sfT2 */).b);
        }));
      }else{
        var _TQ/*   sfSX */ = _TL/* sfSY */,
        _TR/*   sfSY */ = _TK/* sfSX */,
        _TS/*   sfSZ */ = _TM/* sfSZ */;
        _TG/*  sfSX */ = _TQ/*   sfSX */;
        _TH/*  sfSY */ = _TR/*   sfSY */;
        _TI/*  sfSZ */ = _TS/*   sfSZ */;
        return __continue/* EXTERNAL */;
      }
    })(_TG/*  sfSX */, _TH/*  sfSY */, _TI/*  sfSZ */));
    if(_TJ/*  $w$srandomRFloating2 */!=__continue/* EXTERNAL */){
      return _TJ/*  $w$srandomRFloating2 */;
    }
  }
},
_TT/* s6SwZ */ = 1420103680,
_TU/* s6Sx0 */ = 465,
_TV/* s6Sx1 */ = new T2(1,_TU/* s6Sx0 */,_6/* GHC.Types.[] */),
_TW/* s6Sx2 */ = new T2(1,_TT/* s6SwZ */,_TV/* s6Sx1 */),
_TX/* $fHasResolutionE5 */ = new T(function(){
  return B(_JV/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _TW/* s6Sx2 */));
}),
_TY/* $fBitsInt4 */ = 0,
_TZ/* $w$cdivMod1 */ = function(_U0/* s2dPw */, _U1/* s2dPx */){
  var _U2/* s2dPy */ = E(_U1/* s2dPx */);
  if(!_U2/* s2dPy */){
    return E(_OU/* GHC.Real.divZeroError */);
  }else{
    var _U3/* s2dPz */ = function(_U4/* s2dPA */){
      if(_U0/* s2dPw */<=0){
        if(_U0/* s2dPw */>=0){
          var _U5/* s2dPF */ = quotRemI/* EXTERNAL */(_U0/* s2dPw */, _U2/* s2dPy */);
          return new T2(0,_U5/* s2dPF */.a,_U5/* s2dPF */.b);
        }else{
          if(_U2/* s2dPy */<=0){
            var _U6/* s2dPM */ = quotRemI/* EXTERNAL */(_U0/* s2dPw */, _U2/* s2dPy */);
            return new T2(0,_U6/* s2dPM */.a,_U6/* s2dPM */.b);
          }else{
            var _U7/* s2dPS */ = quotRemI/* EXTERNAL */(_U0/* s2dPw */+1|0, _U2/* s2dPy */);
            return new T2(0,_U7/* s2dPS */.a-1|0,(_U7/* s2dPS */.b+_U2/* s2dPy */|0)-1|0);
          }
        }
      }else{
        if(_U2/* s2dPy */>=0){
          if(_U0/* s2dPw */>=0){
            var _U8/* s2dQ4 */ = quotRemI/* EXTERNAL */(_U0/* s2dPw */, _U2/* s2dPy */);
            return new T2(0,_U8/* s2dQ4 */.a,_U8/* s2dQ4 */.b);
          }else{
            if(_U2/* s2dPy */<=0){
              var _U9/* s2dQb */ = quotRemI/* EXTERNAL */(_U0/* s2dPw */, _U2/* s2dPy */);
              return new T2(0,_U9/* s2dQb */.a,_U9/* s2dQb */.b);
            }else{
              var _Ua/* s2dQh */ = quotRemI/* EXTERNAL */(_U0/* s2dPw */+1|0, _U2/* s2dPy */);
              return new T2(0,_Ua/* s2dQh */.a-1|0,(_Ua/* s2dQh */.b+_U2/* s2dPy */|0)-1|0);
            }
          }
        }else{
          var _Ub/* s2dQq */ = quotRemI/* EXTERNAL */(_U0/* s2dPw */-1|0, _U2/* s2dPy */);
          return new T2(0,_Ub/* s2dQq */.a-1|0,(_Ub/* s2dQq */.b+_U2/* s2dPy */|0)+1|0);
        }
      }
    };
    if(E(_U2/* s2dPy */)==(-1)){
      if(E(_U0/* s2dPw */)==(-2147483648)){
        return new T2(0,_OX/* GHC.Real.overflowError */,_TY/* GHC.Int.$fBitsInt4 */);
      }else{
        return new F(function(){return _U3/* s2dPz */(_/* EXTERNAL */);});
      }
    }else{
      return new F(function(){return _U3/* s2dPz */(_/* EXTERNAL */);});
    }
  }
},
_Uc/* lvl1 */ = new T1(0,-1),
_Ud/* signumInteger */ = function(_Ue/* s1OO */){
  var _Uf/* s1OP */ = E(_Ue/* s1OO */);
  if(!_Uf/* s1OP */._){
    var _Ug/* s1OQ */ = _Uf/* s1OP */.a;
    return (_Ug/* s1OQ */>=0) ? (E(_Ug/* s1OQ */)==0) ? E(_Jq/* GHC.Integer.Type.lvl */) : E(_JF/* GHC.Integer.Type.log2I1 */) : E(_Uc/* GHC.Integer.Type.lvl1 */);
  }else{
    var _Uh/* s1OW */ = I_compareInt/* EXTERNAL */(_Uf/* s1OP */.a, 0);
    return (_Uh/* s1OW */<=0) ? (E(_Uh/* s1OW */)==0) ? E(_Jq/* GHC.Integer.Type.lvl */) : E(_Uc/* GHC.Integer.Type.lvl1 */) : E(_JF/* GHC.Integer.Type.log2I1 */);
  }
},
_Ui/* $w$s$c/ */ = function(_Uj/* svwb */, _Uk/* svwc */, _Ul/* svwd */, _Um/* svwe */){
  var _Un/* svwf */ = B(_RC/* GHC.Integer.Type.timesInteger */(_Uk/* svwc */, _Ul/* svwd */));
  return new F(function(){return _Ry/* GHC.Real.$w$sreduce */(B(_RC/* GHC.Integer.Type.timesInteger */(B(_RC/* GHC.Integer.Type.timesInteger */(_Uj/* svwb */, _Um/* svwe */)), B(_Ud/* GHC.Integer.Type.signumInteger */(_Un/* svwf */)))), B(_Ri/* GHC.Integer.Type.absInteger */(_Un/* svwf */)));});
},
_Uo/* $fHasResolutionE12_$cresolution */ = function(_Up/* s6Sx3 */){
  return E(_TX/* Data.Fixed.$fHasResolutionE5 */);
},
_Uq/* $fEnumInteger2 */ = new T1(0,1),
_Ur/* $wenumDeltaInteger */ = function(_Us/* smJm */, _Ut/* smJn */){
  var _Uu/* smJo */ = E(_Us/* smJm */);
  return new T2(0,_Uu/* smJo */,new T(function(){
    var _Uv/* smJq */ = B(_Ur/* GHC.Enum.$wenumDeltaInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_Uu/* smJo */, _Ut/* smJn */)), _Ut/* smJn */));
    return new T2(1,_Uv/* smJq */.a,_Uv/* smJq */.b);
  }));
},
_Uw/* $fEnumInteger_$cenumFrom */ = function(_Ux/* smJF */){
  var _Uy/* smJG */ = B(_Ur/* GHC.Enum.$wenumDeltaInteger */(_Ux/* smJF */, _Uq/* GHC.Enum.$fEnumInteger2 */));
  return new T2(1,_Uy/* smJG */.a,_Uy/* smJG */.b);
},
_Uz/* $fEnumInteger_$cenumFromThen */ = function(_UA/* smJJ */, _UB/* smJK */){
  var _UC/* smJM */ = B(_Ur/* GHC.Enum.$wenumDeltaInteger */(_UA/* smJJ */, new T(function(){
    return B(_Lm/* GHC.Integer.Type.minusInteger */(_UB/* smJK */, _UA/* smJJ */));
  })));
  return new T2(1,_UC/* smJM */.a,_UC/* smJM */.b);
},
_UD/* enumDeltaToInteger */ = function(_UE/* smJP */, _UF/* smJQ */, _UG/* smJR */){
  if(!B(_KO/* GHC.Integer.Type.geInteger */(_UF/* smJQ */, _KN/* GHC.Enum.$fEnumInteger1 */))){
    var _UH/* smJT */ = function(_UI/* smJU */){
      return (!B(_KW/* GHC.Integer.Type.ltInteger */(_UI/* smJU */, _UG/* smJR */))) ? new T2(1,_UI/* smJU */,new T(function(){
        return B(_UH/* smJT */(B(_JH/* GHC.Integer.Type.plusInteger */(_UI/* smJU */, _UF/* smJQ */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _UH/* smJT */(_UE/* smJP */);});
  }else{
    var _UJ/* smJY */ = function(_UK/* smJZ */){
      return (!B(_Kq/* GHC.Integer.Type.gtInteger */(_UK/* smJZ */, _UG/* smJR */))) ? new T2(1,_UK/* smJZ */,new T(function(){
        return B(_UJ/* smJY */(B(_JH/* GHC.Integer.Type.plusInteger */(_UK/* smJZ */, _UF/* smJQ */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _UJ/* smJY */(_UE/* smJP */);});
  }
},
_UL/* $fEnumInteger_$cenumFromThenTo */ = function(_UM/* smKg */, _UN/* smKh */, _UO/* smKi */){
  return new F(function(){return _UD/* GHC.Enum.enumDeltaToInteger */(_UM/* smKg */, B(_Lm/* GHC.Integer.Type.minusInteger */(_UN/* smKh */, _UM/* smKg */)), _UO/* smKi */);});
},
_UP/* $fEnumInteger_$cenumFromTo */ = function(_UQ/* smKe */, _UR/* smKf */){
  return new F(function(){return _UD/* GHC.Enum.enumDeltaToInteger */(_UQ/* smKe */, _Uq/* GHC.Enum.$fEnumInteger2 */, _UR/* smKf */);});
},
_US/* integerToInt */ = function(_UT/* s1Rv */){
  var _UU/* s1Rw */ = E(_UT/* s1Rv */);
  if(!_UU/* s1Rw */._){
    return E(_UU/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_UU/* s1Rw */.a);});
  }
},
_UV/* $fEnumInteger_$cfromEnum */ = function(_UW/* smJf */){
  return new F(function(){return _US/* GHC.Integer.Type.integerToInt */(_UW/* smJf */);});
},
_UX/* $fEnumInteger_$cpred */ = function(_UY/* smJl */){
  return new F(function(){return _Lm/* GHC.Integer.Type.minusInteger */(_UY/* smJl */, _Uq/* GHC.Enum.$fEnumInteger2 */);});
},
_UZ/* $fEnumInteger_$csucc */ = function(_V0/* smJk */){
  return new F(function(){return _JH/* GHC.Integer.Type.plusInteger */(_V0/* smJk */, _Uq/* GHC.Enum.$fEnumInteger2 */);});
},
_V1/* $fEnumInteger_$ctoEnum */ = function(_V2/* smJh */){
  return new F(function(){return _M7/* GHC.Integer.Type.smallInteger */(E(_V2/* smJh */));});
},
_V3/* $fEnumInteger */ = {_:0,a:_UZ/* GHC.Enum.$fEnumInteger_$csucc */,b:_UX/* GHC.Enum.$fEnumInteger_$cpred */,c:_V1/* GHC.Enum.$fEnumInteger_$ctoEnum */,d:_UV/* GHC.Enum.$fEnumInteger_$cfromEnum */,e:_Uw/* GHC.Enum.$fEnumInteger_$cenumFrom */,f:_Uz/* GHC.Enum.$fEnumInteger_$cenumFromThen */,g:_UP/* GHC.Enum.$fEnumInteger_$cenumFromTo */,h:_UL/* GHC.Enum.$fEnumInteger_$cenumFromThenTo */},
_V4/* divInt# */ = function(_V5/* scDT */, _V6/* scDU */){
  if(_V5/* scDT */<=0){
    if(_V5/* scDT */>=0){
      return new F(function(){return quot/* EXTERNAL */(_V5/* scDT */, _V6/* scDU */);});
    }else{
      if(_V6/* scDU */<=0){
        return new F(function(){return quot/* EXTERNAL */(_V5/* scDT */, _V6/* scDU */);});
      }else{
        return quot/* EXTERNAL */(_V5/* scDT */+1|0, _V6/* scDU */)-1|0;
      }
    }
  }else{
    if(_V6/* scDU */>=0){
      if(_V5/* scDT */>=0){
        return new F(function(){return quot/* EXTERNAL */(_V5/* scDT */, _V6/* scDU */);});
      }else{
        if(_V6/* scDU */<=0){
          return new F(function(){return quot/* EXTERNAL */(_V5/* scDT */, _V6/* scDU */);});
        }else{
          return quot/* EXTERNAL */(_V5/* scDT */+1|0, _V6/* scDU */)-1|0;
        }
      }
    }else{
      return quot/* EXTERNAL */(_V5/* scDT */-1|0, _V6/* scDU */)-1|0;
    }
  }
},
_V7/* divInteger */ = function(_V8/* s1Nz */, _V9/* s1NA */){
  while(1){
    var _Va/* s1NB */ = E(_V8/* s1Nz */);
    if(!_Va/* s1NB */._){
      var _Vb/* s1ND */ = E(_Va/* s1NB */.a);
      if(_Vb/* s1ND */==(-2147483648)){
        _V8/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _Vc/* s1NE */ = E(_V9/* s1NA */);
        if(!_Vc/* s1NE */._){
          return new T1(0,B(_V4/* GHC.Classes.divInt# */(_Vb/* s1ND */, _Vc/* s1NE */.a)));
        }else{
          _V8/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(_Vb/* s1ND */));
          _V9/* s1NA */ = _Vc/* s1NE */;
          continue;
        }
      }
    }else{
      var _Vd/* s1NO */ = _Va/* s1NB */.a,
      _Ve/* s1NP */ = E(_V9/* s1NA */);
      return (_Ve/* s1NP */._==0) ? new T1(1,I_div/* EXTERNAL */(_Vd/* s1NO */, I_fromInt/* EXTERNAL */(_Ve/* s1NP */.a))) : new T1(1,I_div/* EXTERNAL */(_Vd/* s1NO */, _Ve/* s1NP */.a));
    }
  }
},
_Vf/* $fIntegralInteger_$cdiv */ = function(_Vg/* svup */, _Vh/* svuq */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_Vh/* svuq */, _R1/* GHC.Real.even1 */))){
    return new F(function(){return _V7/* GHC.Integer.Type.divInteger */(_Vg/* svup */, _Vh/* svuq */);});
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_Vi/* divModInteger */ = function(_Vj/* s1MF */, _Vk/* s1MG */){
  while(1){
    var _Vl/* s1MH */ = E(_Vj/* s1MF */);
    if(!_Vl/* s1MH */._){
      var _Vm/* s1MJ */ = E(_Vl/* s1MH */.a);
      if(_Vm/* s1MJ */==(-2147483648)){
        _Vj/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _Vn/* s1MK */ = E(_Vk/* s1MG */);
        if(!_Vn/* s1MK */._){
          var _Vo/* s1ML */ = _Vn/* s1MK */.a;
          return new T2(0,new T1(0,B(_V4/* GHC.Classes.divInt# */(_Vm/* s1MJ */, _Vo/* s1ML */))),new T1(0,B(_SY/* GHC.Classes.modInt# */(_Vm/* s1MJ */, _Vo/* s1ML */))));
        }else{
          _Vj/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(_Vm/* s1MJ */));
          _Vk/* s1MG */ = _Vn/* s1MK */;
          continue;
        }
      }
    }else{
      var _Vp/* s1MY */ = E(_Vk/* s1MG */);
      if(!_Vp/* s1MY */._){
        _Vj/* s1MF */ = _Vl/* s1MH */;
        _Vk/* s1MG */ = new T1(1,I_fromInt/* EXTERNAL */(_Vp/* s1MY */.a));
        continue;
      }else{
        var _Vq/* s1N5 */ = I_divMod/* EXTERNAL */(_Vl/* s1MH */.a, _Vp/* s1MY */.a);
        return new T2(0,new T1(1,_Vq/* s1N5 */.a),new T1(1,_Vq/* s1N5 */.b));
      }
    }
  }
},
_Vr/* $fIntegralInteger_$cdivMod */ = function(_Vs/* svua */, _Vt/* svub */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_Vt/* svub */, _R1/* GHC.Real.even1 */))){
    var _Vu/* svud */ = B(_Vi/* GHC.Integer.Type.divModInteger */(_Vs/* svua */, _Vt/* svub */));
    return new T2(0,_Vu/* svud */.a,_Vu/* svud */.b);
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_Vv/* $fIntegralInteger_$cmod */ = function(_Vw/* svum */, _Vx/* svun */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_Vx/* svun */, _R1/* GHC.Real.even1 */))){
    return new F(function(){return _T5/* GHC.Integer.Type.modInteger */(_Vw/* svum */, _Vx/* svun */);});
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_Vy/* $fIntegralInteger_$cquot */ = function(_Vz/* svvA */, _VA/* svvB */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_VA/* svvB */, _R1/* GHC.Real.even1 */))){
    return new F(function(){return _Rn/* GHC.Integer.Type.quotInteger */(_Vz/* svvA */, _VA/* svvB */);});
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_VB/* quotRemInteger */ = function(_VC/* s1Ma */, _VD/* s1Mb */){
  while(1){
    var _VE/* s1Mc */ = E(_VC/* s1Ma */);
    if(!_VE/* s1Mc */._){
      var _VF/* s1Me */ = E(_VE/* s1Mc */.a);
      if(_VF/* s1Me */==(-2147483648)){
        _VC/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _VG/* s1Mf */ = E(_VD/* s1Mb */);
        if(!_VG/* s1Mf */._){
          var _VH/* s1Mg */ = _VG/* s1Mf */.a;
          return new T2(0,new T1(0,quot/* EXTERNAL */(_VF/* s1Me */, _VH/* s1Mg */)),new T1(0,_VF/* s1Me */%_VH/* s1Mg */));
        }else{
          _VC/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(_VF/* s1Me */));
          _VD/* s1Mb */ = _VG/* s1Mf */;
          continue;
        }
      }
    }else{
      var _VI/* s1Mt */ = E(_VD/* s1Mb */);
      if(!_VI/* s1Mt */._){
        _VC/* s1Ma */ = _VE/* s1Mc */;
        _VD/* s1Mb */ = new T1(1,I_fromInt/* EXTERNAL */(_VI/* s1Mt */.a));
        continue;
      }else{
        var _VJ/* s1MA */ = I_quotRem/* EXTERNAL */(_VE/* s1Mc */.a, _VI/* s1Mt */.a);
        return new T2(0,new T1(1,_VJ/* s1MA */.a),new T1(1,_VJ/* s1MA */.b));
      }
    }
  }
},
_VK/* $fIntegralInteger_$cquotRem */ = function(_VL/* svug */, _VM/* svuh */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_VM/* svuh */, _R1/* GHC.Real.even1 */))){
    var _VN/* svuj */ = B(_VB/* GHC.Integer.Type.quotRemInteger */(_VL/* svug */, _VM/* svuh */));
    return new T2(0,_VN/* svuj */.a,_VN/* svuj */.b);
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_VO/* $fIntegralInteger_$ctoInteger */ = function(_VP/* svu9 */){
  return E(_VP/* svu9 */);
},
_VQ/* $fNumInteger_$cfromInteger */ = function(_VR/* s6HU */){
  return E(_VR/* s6HU */);
},
_VS/* $fNumInteger */ = {_:0,a:_JH/* GHC.Integer.Type.plusInteger */,b:_Lm/* GHC.Integer.Type.minusInteger */,c:_RC/* GHC.Integer.Type.timesInteger */,d:_JR/* GHC.Integer.Type.negateInteger */,e:_Ri/* GHC.Integer.Type.absInteger */,f:_Ud/* GHC.Integer.Type.signumInteger */,g:_VQ/* GHC.Num.$fNumInteger_$cfromInteger */},
_VT/* neqInteger */ = function(_VU/* s1GK */, _VV/* s1GL */){
  var _VW/* s1GM */ = E(_VU/* s1GK */);
  if(!_VW/* s1GM */._){
    var _VX/* s1GN */ = _VW/* s1GM */.a,
    _VY/* s1GO */ = E(_VV/* s1GL */);
    return (_VY/* s1GO */._==0) ? _VX/* s1GN */!=_VY/* s1GO */.a : (I_compareInt/* EXTERNAL */(_VY/* s1GO */.a, _VX/* s1GN */)==0) ? false : true;
  }else{
    var _VZ/* s1GU */ = _VW/* s1GM */.a,
    _W0/* s1GV */ = E(_VV/* s1GL */);
    return (_W0/* s1GV */._==0) ? (I_compareInt/* EXTERNAL */(_VZ/* s1GU */, _W0/* s1GV */.a)==0) ? false : true : (I_compare/* EXTERNAL */(_VZ/* s1GU */, _W0/* s1GV */.a)==0) ? false : true;
  }
},
_W1/* $fEqInteger */ = new T2(0,_QT/* GHC.Integer.Type.eqInteger */,_VT/* GHC.Integer.Type.neqInteger */),
_W2/* leInteger */ = function(_W3/* s1Gp */, _W4/* s1Gq */){
  var _W5/* s1Gr */ = E(_W3/* s1Gp */);
  if(!_W5/* s1Gr */._){
    var _W6/* s1Gs */ = _W5/* s1Gr */.a,
    _W7/* s1Gt */ = E(_W4/* s1Gq */);
    return (_W7/* s1Gt */._==0) ? _W6/* s1Gs */<=_W7/* s1Gt */.a : I_compareInt/* EXTERNAL */(_W7/* s1Gt */.a, _W6/* s1Gs */)>=0;
  }else{
    var _W8/* s1GA */ = _W5/* s1Gr */.a,
    _W9/* s1GB */ = E(_W4/* s1Gq */);
    return (_W9/* s1GB */._==0) ? I_compareInt/* EXTERNAL */(_W8/* s1GA */, _W9/* s1GB */.a)<=0 : I_compare/* EXTERNAL */(_W8/* s1GA */, _W9/* s1GB */.a)<=0;
  }
},
_Wa/* $fOrdInteger_$cmax */ = function(_Wb/* s1HU */, _Wc/* s1HV */){
  return (!B(_W2/* GHC.Integer.Type.leInteger */(_Wb/* s1HU */, _Wc/* s1HV */))) ? E(_Wb/* s1HU */) : E(_Wc/* s1HV */);
},
_Wd/* $fOrdInteger_$cmin */ = function(_We/* s1HR */, _Wf/* s1HS */){
  return (!B(_W2/* GHC.Integer.Type.leInteger */(_We/* s1HR */, _Wf/* s1HS */))) ? E(_Wf/* s1HS */) : E(_We/* s1HR */);
},
_Wg/* compareInteger */ = function(_Wh/* s1Hk */, _Wi/* s1Hl */){
  var _Wj/* s1Hm */ = E(_Wh/* s1Hk */);
  if(!_Wj/* s1Hm */._){
    var _Wk/* s1Hn */ = _Wj/* s1Hm */.a,
    _Wl/* s1Ho */ = E(_Wi/* s1Hl */);
    if(!_Wl/* s1Ho */._){
      var _Wm/* s1Hp */ = _Wl/* s1Ho */.a;
      return (_Wk/* s1Hn */!=_Wm/* s1Hp */) ? (_Wk/* s1Hn */>_Wm/* s1Hp */) ? 2 : 0 : 1;
    }else{
      var _Wn/* s1Hw */ = I_compareInt/* EXTERNAL */(_Wl/* s1Ho */.a, _Wk/* s1Hn */);
      return (_Wn/* s1Hw */<=0) ? (_Wn/* s1Hw */>=0) ? 1 : 2 : 0;
    }
  }else{
    var _Wo/* s1HB */ = _Wj/* s1Hm */.a,
    _Wp/* s1HC */ = E(_Wi/* s1Hl */);
    if(!_Wp/* s1HC */._){
      var _Wq/* s1HF */ = I_compareInt/* EXTERNAL */(_Wo/* s1HB */, _Wp/* s1HC */.a);
      return (_Wq/* s1HF */>=0) ? (_Wq/* s1HF */<=0) ? 1 : 2 : 0;
    }else{
      var _Wr/* s1HM */ = I_compare/* EXTERNAL */(_Wo/* s1HB */, _Wp/* s1HC */.a);
      return (_Wr/* s1HM */>=0) ? (_Wr/* s1HM */<=0) ? 1 : 2 : 0;
    }
  }
},
_Ws/* $fOrdInteger */ = {_:0,a:_W1/* GHC.Integer.Type.$fEqInteger */,b:_Wg/* GHC.Integer.Type.compareInteger */,c:_KW/* GHC.Integer.Type.ltInteger */,d:_W2/* GHC.Integer.Type.leInteger */,e:_Kq/* GHC.Integer.Type.gtInteger */,f:_KO/* GHC.Integer.Type.geInteger */,g:_Wa/* GHC.Integer.Type.$fOrdInteger_$cmax */,h:_Wd/* GHC.Integer.Type.$fOrdInteger_$cmin */},
_Wt/* $fRealInteger_$s$cfromInteger */ = function(_Wu/* svmz */){
  return new T2(0,E(_Wu/* svmz */),E(_Kj/* GHC.Real.$fEnumRatio1 */));
},
_Wv/* $fRealInteger */ = new T3(0,_VS/* GHC.Num.$fNumInteger */,_Ws/* GHC.Integer.Type.$fOrdInteger */,_Wt/* GHC.Real.$fRealInteger_$s$cfromInteger */),
_Ww/* $fIntegralInteger */ = {_:0,a:_Wv/* GHC.Real.$fRealInteger */,b:_V3/* GHC.Enum.$fEnumInteger */,c:_Vy/* GHC.Real.$fIntegralInteger_$cquot */,d:_Ra/* GHC.Real.$fIntegralInteger_$crem */,e:_Vf/* GHC.Real.$fIntegralInteger_$cdiv */,f:_Vv/* GHC.Real.$fIntegralInteger_$cmod */,g:_VK/* GHC.Real.$fIntegralInteger_$cquotRem */,h:_Vr/* GHC.Real.$fIntegralInteger_$cdivMod */,i:_VO/* GHC.Real.$fIntegralInteger_$ctoInteger */},
_Wx/* $fFractionalFixed1 */ = new T1(0,0),
_Wy/* $fNumFixed5 */ = function(_Wz/* s6SxT */, _WA/* s6SxU */, _WB/* s6SxV */){
  var _WC/* s6SxW */ = B(A1(_Wz/* s6SxT */,_WA/* s6SxU */));
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_WC/* s6SxW */, _Wx/* Data.Fixed.$fFractionalFixed1 */))){
    return new F(function(){return _V7/* GHC.Integer.Type.divInteger */(B(_RC/* GHC.Integer.Type.timesInteger */(_WA/* s6SxU */, _WB/* s6SxV */)), _WC/* s6SxW */);});
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_WD/* $w$s$cproperFraction */ = function(_WE/* svn0 */, _WF/* svn1 */, _WG/* svn2 */){
  var _WH/* svn3 */ = new T(function(){
    if(!B(_QT/* GHC.Integer.Type.eqInteger */(_WG/* svn2 */, _R1/* GHC.Real.even1 */))){
      var _WI/* svn5 */ = B(_VB/* GHC.Integer.Type.quotRemInteger */(_WF/* svn1 */, _WG/* svn2 */));
      return new T2(0,_WI/* svn5 */.a,_WI/* svn5 */.b);
    }else{
      return E(_OU/* GHC.Real.divZeroError */);
    }
  }),
  _WJ/* svne */ = new T(function(){
    return B(A2(_Ko/* GHC.Num.fromInteger */,B(_Km/* GHC.Real.$p1Real */(B(_Kk/* GHC.Real.$p1Integral */(_WE/* svn0 */)))), new T(function(){
      return E(E(_WH/* svn3 */).a);
    })));
  });
  return new T2(0,_WJ/* svne */,new T(function(){
    return new T2(0,E(E(_WH/* svn3 */).b),E(_WG/* svn2 */));
  }));
},
_WK/* - */ = function(_WL/* s6FH */){
  return E(E(_WL/* s6FH */).b);
},
_WM/* $w$s$cfloor */ = function(_WN/* svJO */, _WO/* svJP */, _WP/* svJQ */){
  var _WQ/* svJR */ = B(_WD/* GHC.Real.$w$s$cproperFraction */(_WN/* svJO */, _WO/* svJP */, _WP/* svJQ */)),
  _WR/* svJS */ = _WQ/* svJR */.a,
  _WS/* svJU */ = E(_WQ/* svJR */.b);
  if(!B(_KW/* GHC.Integer.Type.ltInteger */(B(_RC/* GHC.Integer.Type.timesInteger */(_WS/* svJU */.a, _Kj/* GHC.Real.$fEnumRatio1 */)), B(_RC/* GHC.Integer.Type.timesInteger */(_R1/* GHC.Real.even1 */, _WS/* svJU */.b))))){
    return E(_WR/* svJS */);
  }else{
    var _WT/* svK1 */ = B(_Km/* GHC.Real.$p1Real */(B(_Kk/* GHC.Real.$p1Integral */(_WN/* svJO */))));
    return new F(function(){return A3(_WK/* GHC.Num.- */,_WT/* svK1 */, _WR/* svJS */, new T(function(){
      return B(A2(_Ko/* GHC.Num.fromInteger */,_WT/* svK1 */, _Kj/* GHC.Real.$fEnumRatio1 */));
    }));});
  }
},
_WU/* slaT */ = 479723520,
_WV/* slaU */ = 40233135,
_WW/* slaV */ = new T2(1,_WV/* slaU */,_6/* GHC.Types.[] */),
_WX/* slaW */ = new T2(1,_WU/* slaT */,_WW/* slaV */),
_WY/* posixDayLength1 */ = new T(function(){
  return B(_JV/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _WX/* slaW */));
}),
_WZ/* posixSecondsToUTCTime1 */ = new T1(0,40587),
_X0/* $wposixSecondsToUTCTime */ = function(_X1/* slaX */){
  var _X2/* slaY */ = new T(function(){
    var _X3/* slaZ */ = B(_Ui/* GHC.Real.$w$s$c/ */(_X1/* slaX */, _Kj/* GHC.Real.$fEnumRatio1 */, _TX/* Data.Fixed.$fHasResolutionE5 */, _Kj/* GHC.Real.$fEnumRatio1 */)),
    _X4/* slb2 */ = B(_Ui/* GHC.Real.$w$s$c/ */(_WY/* Data.Time.Clock.POSIX.posixDayLength1 */, _Kj/* GHC.Real.$fEnumRatio1 */, _TX/* Data.Fixed.$fHasResolutionE5 */, _Kj/* GHC.Real.$fEnumRatio1 */)),
    _X5/* slb5 */ = B(_Ui/* GHC.Real.$w$s$c/ */(_X3/* slaZ */.a, _X3/* slaZ */.b, _X4/* slb2 */.a, _X4/* slb2 */.b));
    return B(_WM/* GHC.Real.$w$s$cfloor */(_Ww/* GHC.Real.$fIntegralInteger */, _X5/* slb5 */.a, _X5/* slb5 */.b));
  });
  return new T2(0,new T(function(){
    return B(_JH/* GHC.Integer.Type.plusInteger */(_WZ/* Data.Time.Clock.POSIX.posixSecondsToUTCTime1 */, _X2/* slaY */));
  }),new T(function(){
    return B(_Lm/* GHC.Integer.Type.minusInteger */(_X1/* slaX */, B(_Wy/* Data.Fixed.$fNumFixed5 */(_Uo/* Data.Fixed.$fHasResolutionE12_$cresolution */, B(_RC/* GHC.Integer.Type.timesInteger */(_X2/* slaY */, _TX/* Data.Fixed.$fHasResolutionE5 */)), _WY/* Data.Time.Clock.POSIX.posixDayLength1 */))));
  }));
},
_X6/* getCPUTime2 */ = new T1(0,0),
_X7/* $wa1 */ = function(_X8/* s3vS */, _/* EXTERNAL */){
  var _X9/* s3vX */ = __get/* EXTERNAL */(_X8/* s3vS */, 0),
  _Xa/* s3w3 */ = __get/* EXTERNAL */(_X8/* s3vS */, 1),
  _Xb/* s3w7 */ = Number/* EXTERNAL */(_X9/* s3vX */),
  _Xc/* s3wb */ = jsTrunc/* EXTERNAL */(_Xb/* s3w7 */),
  _Xd/* s3wf */ = Number/* EXTERNAL */(_Xa/* s3w3 */),
  _Xe/* s3wj */ = jsTrunc/* EXTERNAL */(_Xd/* s3wf */);
  return new T2(0,_Xc/* s3wb */,_Xe/* s3wj */);
},
_Xf/* getCTimeval_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");
}),
_Xg/* slbq */ = 660865024,
_Xh/* slbr */ = 465661287,
_Xi/* slbs */ = new T2(1,_Xh/* slbr */,_6/* GHC.Types.[] */),
_Xj/* slbt */ = new T2(1,_Xg/* slbq */,_Xi/* slbs */),
_Xk/* getPOSIXTime2 */ = new T(function(){
  return B(_JV/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _Xj/* slbt */));
}),
_Xl/* getPOSIXTime1 */ = function(_/* EXTERNAL */){
  var _Xm/* slby */ = __app0/* EXTERNAL */(E(_Xf/* Data.Time.Clock.CTimeval.getCTimeval_f1 */)),
  _Xn/* slbB */ = B(_X7/* Data.Time.Clock.CTimeval.$wa1 */(_Xm/* slby */, _/* EXTERNAL */));
  return new T(function(){
    var _Xo/* slbE */ = E(_Xn/* slbB */);
    if(!B(_QT/* GHC.Integer.Type.eqInteger */(_Xk/* Data.Time.Clock.POSIX.getPOSIXTime2 */, _Wx/* Data.Fixed.$fFractionalFixed1 */))){
      return B(_JH/* GHC.Integer.Type.plusInteger */(B(_RC/* GHC.Integer.Type.timesInteger */(B(_M7/* GHC.Integer.Type.smallInteger */(E(_Xo/* slbE */.a))), _TX/* Data.Fixed.$fHasResolutionE5 */)), B(_V7/* GHC.Integer.Type.divInteger */(B(_RC/* GHC.Integer.Type.timesInteger */(B(_RC/* GHC.Integer.Type.timesInteger */(B(_M7/* GHC.Integer.Type.smallInteger */(E(_Xo/* slbE */.b))), _TX/* Data.Fixed.$fHasResolutionE5 */)), _TX/* Data.Fixed.$fHasResolutionE5 */)), _Xk/* Data.Time.Clock.POSIX.getPOSIXTime2 */))));
    }else{
      return E(_OU/* GHC.Real.divZeroError */);
    }
  });
},
_Xp/* getStdRandom3 */ = new T1(0,12345),
_Xq/* getStdRandom2 */ = function(_/* EXTERNAL */){
  var _Xr/* sfpA */ = B(_Xl/* Data.Time.Clock.POSIX.getPOSIXTime1 */(0)),
  _Xs/* sfpG */ = B(_Ui/* GHC.Real.$w$s$c/ */(B(_X0/* Data.Time.Clock.POSIX.$wposixSecondsToUTCTime */(_Xr/* sfpA */)).b, _Kj/* GHC.Real.$fEnumRatio1 */, _TX/* Data.Fixed.$fHasResolutionE5 */, _Kj/* GHC.Real.$fEnumRatio1 */)),
  _Xt/* sfpI */ = _Xs/* sfpG */.b;
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_Xt/* sfpI */, _SW/* System.Random.getStdRandom4 */))){
    var _Xu/* sfpK */ = B(_VB/* GHC.Integer.Type.quotRemInteger */(_Xs/* sfpG */.a, _Xt/* sfpI */));
    return new F(function(){return nMV/* EXTERNAL */(new T(function(){
      var _Xv/* sfpV */ = B(_TZ/* GHC.Int.$w$cdivMod1 */((B(_US/* GHC.Integer.Type.integerToInt */(B(_JH/* GHC.Integer.Type.plusInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(B(_RC/* GHC.Integer.Type.timesInteger */(_Xu/* sfpK */.a, _Xp/* System.Random.getStdRandom3 */)), _Xu/* sfpK */.b)), _X6/* System.CPUTime.getCPUTime2 */)), _SW/* System.Random.getStdRandom4 */))))>>>0&2147483647)>>>0&4294967295, 2147483562));
      return new T2(0,E(_Xv/* sfpV */.b)+1|0,B(_SY/* GHC.Classes.modInt# */(E(_Xv/* sfpV */.a), 2147483398))+1|0);
    }));});
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_Xw/* theStdGen */ = new T(function(){
  return B(_44/* GHC.IO.unsafeDupablePerformIO */(_Xq/* System.Random.getStdRandom2 */));
}),
_Xx/* $fRandomDouble8 */ = function(_Xy/* sfTt */, _/* EXTERNAL */){
  var _Xz/* sfTM */ = mMV/* EXTERNAL */(E(_Xw/* System.Random.theStdGen */), function(_XA/* sfTx */){
    var _XB/* sfTy */ = E(_Xy/* sfTt */),
    _XC/* sfTF */ = B(_TF/* System.Random.$w$srandomRFloating2 */(E(_XB/* sfTy */.a), E(_XB/* sfTy */.b), _XA/* sfTx */));
    return new T2(0,E(_XC/* sfTF */.b),_XC/* sfTF */.a);
  }),
  _XD/* sfTQ */ = E(_Xz/* sfTM */);
  return _Xz/* sfTM */;
},
_XE/* speedMot19 */ = 1,
_XF/* speedMot18 */ = new T2(0,_IR/* Motion.Speed.speedMot14 */,_XE/* Motion.Speed.speedMot19 */),
_XG/* speedMot17 */ = function(_/* EXTERNAL */){
  return new F(function(){return _Xx/* System.Random.$fRandomDouble8 */(_XF/* Motion.Speed.speedMot18 */, _/* EXTERNAL */);});
},
_XH/* speedMot16 */ = new T1(1,_XG/* Motion.Speed.speedMot17 */),
_XI/* speedMot15 */ = new T(function(){
  return B(_pg/* Control.Monad.Skeleton.bone */(_XH/* Motion.Speed.speedMot16 */));
}),
_XJ/* speedMot3 */ = 60,
_XK/* speedMot2 */ = new T1(0,_XJ/* Motion.Speed.speedMot3 */),
_XL/* speedMot22 */ = 100,
_XM/* speedMot21 */ = new T1(0,_XL/* Motion.Speed.speedMot22 */),
_XN/* speedMot20 */ = new T2(0,_XM/* Motion.Speed.speedMot21 */,_XM/* Motion.Speed.speedMot21 */),
_XO/* speedMot5 */ = -30,
_XP/* speedMot4 */ = new T1(0,_XO/* Motion.Speed.speedMot5 */),
_XQ/* speedMot8 */ = new T(function(){
  return  -0;
}),
_XR/* speedMot7 */ = new T1(0,_XQ/* Motion.Speed.speedMot8 */),
_XS/* speedMot6 */ = new T2(0,_XR/* Motion.Speed.speedMot7 */,_XR/* Motion.Speed.speedMot7 */),
_XT/* $fFloatingDouble_$cpi */ = 3.141592653589793,
_XU/* $s$fFloatingValue_$cpi */ = new T1(0,_XT/* GHC.Float.$fFloatingDouble_$cpi */),
_XV/* speedMot11 */ = 6,
_XW/* speedMot10 */ = new T1(0,_XV/* Motion.Speed.speedMot11 */),
_XX/* speedMot9 */ = new T(function(){
  return B(_uj/* Core.Ease.opLift */(_in/* GHC.Float.divideDouble */, _XU/* Motion.Speed.$s$fFloatingValue_$cpi */, _XW/* Motion.Speed.speedMot10 */));
}),
_XY/* speedMot */ = function(_XZ/* saf6 */){
  var _Y0/* saf7 */ = new T(function(){
    var _Y1/* safZ */ = new T(function(){
      var _Y2/* saf8 */ = E(_XI/* Motion.Speed.speedMot15 */),
      _Y3/* saf9 */ = _Y2/* saf8 */.a,
      _Y4/* safa */ = _Y2/* saf8 */.b,
      _Y5/* safW */ = function(_Y6/* safb */){
        var _Y7/* safc */ = new T(function(){
          var _Y8/* saff */ = Math.log/* EXTERNAL */(E(_Y6/* safb */));
          return Math.sqrt/* EXTERNAL */( -(_Y8/* saff */+_Y8/* saff */));
        }),
        _Y9/* safT */ = function(_Ya/* safj */){
          var _Yb/* safk */ = new T(function(){
            var _Yc/* safl */ = E(_Y7/* safc */),
            _Yd/* safn */ = E(_Ya/* safj */);
            return _Yc/* safl */*Math.sin/* EXTERNAL */(6.283185307179586*_Yd/* safn */)+_Yc/* safl */*Math.sin/* EXTERNAL */(6.283185307179586*_Yd/* safn */);
          }),
          _Ye/* safQ */ = function(_Yf/* safx */){
            var _Yg/* safO */ = new T(function(){
              var _Yh/* safM */ = new T(function(){
                var _Yi/* safK */ = new T(function(){
                  var _Yj/* safJ */ = new T(function(){
                    var _Yk/* safE */ = new T(function(){
                      return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, _XP/* Motion.Speed.speedMot4 */, new T1(0,new T(function(){
                        return 4/(1-E(_Yf/* safx */));
                      }))));
                    }),
                    _Yl/* safF */ = B(_Gl/* Core.Shape.Internal.$wcenterRect */(new T1(0,_Yb/* safk */), _Yk/* safE */, _XK/* Motion.Speed.speedMot2 */, _XK/* Motion.Speed.speedMot2 */));
                    return new T3(0,_Yl/* safF */.a,_Yl/* safF */.b,_Yl/* safF */.c);
                  });
                  return B(_ro/* Core.Render.Internal.fill1 */(_XZ/* saf6 */, _Yj/* safJ */));
                });
                return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,_XS/* Motion.Speed.speedMot6 */,_Yi/* safK */,_7/* GHC.Tuple.() */)));
              });
              return B(_pg/* Control.Monad.Skeleton.bone */(new T3(6,_XX/* Motion.Speed.speedMot9 */,_Yh/* safM */,_7/* GHC.Tuple.() */)));
            });
            return new F(function(){return _pg/* Control.Monad.Skeleton.bone */(new T3(5,_IT/* Motion.Speed.speedMot12 */,_Yg/* safO */,_7/* GHC.Tuple.() */));});
          };
          return new T2(0,E(_Y3/* saf9 */),E(new T2(2,_Y4/* safa */,new T1(1,_Ye/* safQ */))));
        };
        return new T2(0,E(_Y3/* saf9 */),E(new T2(2,_Y4/* safa */,new T1(1,_Y9/* safT */))));
      };
      return new T2(0,E(_Y3/* saf9 */),E(new T2(2,_Y4/* safa */,new T1(1,_Y5/* safW */))));
    });
    return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,_XN/* Motion.Speed.speedMot20 */,_Y1/* safZ */,_7/* GHC.Tuple.() */)));
  });
  return function(_Ym/* sag2 */, _Yn/* sag3 */){
    return new F(function(){return A1(_Yn/* sag3 */,new T2(0,new T2(0,_Y0/* saf7 */,_IO/* Motion.Speed.speedMot1 */),_Ym/* sag2 */));});
  };
},
_Yo/* lvl36 */ = new T(function(){
  return B(_AB/* Motion.Main.$wconsView */(_IM/* Motion.Main.lvl34 */, _XY/* Motion.Speed.speedMot */, _IN/* Motion.Main.lvl35 */));
}),
_Yp/* $fNumInt_$c* */ = function(_Yq/* s6GP */, _Yr/* s6GQ */){
  return imul/* EXTERNAL */(E(_Yq/* s6GP */), E(_Yr/* s6GQ */))|0;
},
_Ys/* $fNumInt_$c+ */ = function(_Yt/* s6H3 */, _Yu/* s6H4 */){
  return E(_Yt/* s6H3 */)+E(_Yu/* s6H4 */)|0;
},
_Yv/* $fNumInt_$c- */ = function(_Yw/* s6GW */, _Yx/* s6GX */){
  return E(_Yw/* s6GW */)-E(_Yx/* s6GX */)|0;
},
_Yy/* $fNumInt_$cabs */ = function(_Yz/* s6Hg */){
  var _YA/* s6Hh */ = E(_Yz/* s6Hg */);
  return (_YA/* s6Hh */<0) ?  -_YA/* s6Hh */ : E(_YA/* s6Hh */);
},
_YB/* $fNumInt_$cfromInteger */ = function(_YC/* s6GJ */){
  return new F(function(){return _US/* GHC.Integer.Type.integerToInt */(_YC/* s6GJ */);});
},
_YD/* $fNumInt_$cnegate */ = function(_YE/* s6GL */){
  return  -E(_YE/* s6GL */);
},
_YF/* $fNumInt1 */ = -1,
_YG/* $fNumInt2 */ = 0,
_YH/* $fNumInt3 */ = 1,
_YI/* $fNumInt_$csignum */ = function(_YJ/* s6Ha */){
  var _YK/* s6Hb */ = E(_YJ/* s6Ha */);
  return (_YK/* s6Hb */>=0) ? (E(_YK/* s6Hb */)==0) ? E(_YG/* GHC.Num.$fNumInt2 */) : E(_YH/* GHC.Num.$fNumInt3 */) : E(_YF/* GHC.Num.$fNumInt1 */);
},
_YL/* $fNumInt */ = {_:0,a:_Ys/* GHC.Num.$fNumInt_$c+ */,b:_Yv/* GHC.Num.$fNumInt_$c- */,c:_Yp/* GHC.Num.$fNumInt_$c* */,d:_YD/* GHC.Num.$fNumInt_$cnegate */,e:_Yy/* GHC.Num.$fNumInt_$cabs */,f:_YI/* GHC.Num.$fNumInt_$csignum */,g:_YB/* GHC.Num.$fNumInt_$cfromInteger */},
_YM/* $fRandomBool2 */ = function(_YN/* sftN */){
  var _YO/* sftO */ = B(_Td/* System.Random.$w$srandomIvalInteger */(_YL/* GHC.Num.$fNumInt */, _SW/* System.Random.getStdRandom4 */, _SH/* System.Random.$fRandomBool3 */, _YN/* sftN */));
  return new T2(0,E(_YO/* sftO */.b),new T(function(){
    if(!E(_YO/* sftO */.a)){
      return false;
    }else{
      return true;
    }
  }));
},
_YP/* $sreplicateM2 */ = function(_YQ/* s7Zd */, _YR/* s7Ze */){
  var _YS/* s7Zf */ = E(_YQ/* s7Zd */);
  if(!_YS/* s7Zf */._){
    return function(_YT/* s7Zh */){
      return new F(function(){return A1(_YT/* s7Zh */,new T2(0,_6/* GHC.Types.[] */,_YR/* s7Ze */));});
    };
  }else{
    var _YU/* s7Zw */ = function(_YV/* s7Zl */){
      var _YW/* s7Zm */ = new T(function(){
        return B(A1(_YS/* s7Zf */.a,_YV/* s7Zl */));
      }),
      _YX/* s7Zv */ = function(_YY/* s7Zn */){
        var _YZ/* s7Zu */ = function(_Z0/* s7Zo */){
          var _Z1/* s7Zt */ = new T(function(){
            var _Z2/* s7Zp */ = E(_Z0/* s7Zo */);
            return new T2(0,function(_Z3/* B1 */){
              return new T2(1,_Z2/* s7Zp */.a,_Z3/* B1 */);
            },_Z2/* s7Zp */.b);
          });
          return new F(function(){return A1(_YY/* s7Zn */,_Z1/* s7Zt */);});
        };
        return new F(function(){return A1(_YW/* s7Zm */,_YZ/* s7Zu */);});
      };
      return E(_YX/* s7Zv */);
    };
    return new F(function(){return _55/* Core.World.Internal.$fApplicativeWorld3 */(_YU/* s7Zw */, function(_Z3/* B1 */){
      return new F(function(){return _YP/* Motion.Change.$sreplicateM2 */(_YS/* s7Zf */.b, _Z3/* B1 */);});
    }, _YR/* s7Ze */);});
  }
},
_Z4/* $swhen1 */ = new T(function(){
  return B(_oH/* Control.Monad.Skeleton.$w$cpure */(_/* EXTERNAL */, _7/* GHC.Tuple.() */));
}),
_Z5/* a11 */ = 50,
_Z6/* a */ = new T1(0,_/* EXTERNAL */),
_Z7/* a1 */ = new T1(0,_7/* GHC.Tuple.() */),
_Z8/* a2 */ = new T2(0,E(_Z7/* Motion.Change.a1 */),E(_Z6/* Motion.Change.a */)),
_Z9/* lvl */ = new T4(0,_aw/* GHC.Types.True */,_aw/* GHC.Types.True */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_Za/* lvl1 */ = new T2(0,_aw/* GHC.Types.True */,_Z9/* Motion.Change.lvl */),
_Zb/* lvl2 */ = new T2(0,_Za/* Motion.Change.lvl1 */,_6/* GHC.Types.[] */),
_Zc/* lvl3 */ = function(_Zd/* s7Zy */, _Ze/* s7Zz */){
  var _Zf/* s7ZI */ = function(_/* EXTERNAL */){
    var _Zg/* s7ZB */ = nMV/* EXTERNAL */(_Zb/* Motion.Change.lvl2 */);
    return new T(function(){
      return B(A1(_Ze/* s7Zz */,new T2(0,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_Zg/* s7ZB */),_Zd/* s7Zy */)));
    });
  };
  return new T1(0,_Zf/* s7ZI */);
},
_Zh/* lvl4 */ = new T2(1,_Zc/* Motion.Change.lvl3 */,_6/* GHC.Types.[] */),
_Zi/* $wxs */ = function(_Zj/* s7ZJ */){
  var _Zk/* s7ZK */ = E(_Zj/* s7ZJ */);
  return (_Zk/* s7ZK */==1) ? E(_Zh/* Motion.Change.lvl4 */) : new T2(1,_Zc/* Motion.Change.lvl3 */,new T(function(){
    return B(_Zi/* Motion.Change.$wxs */(_Zk/* s7ZK */-1|0));
  }));
},
_Zl/* a8 */ = new T(function(){
  return B(_Zi/* Motion.Change.$wxs */(9));
}),
_Zm/* dur */ = 10,
_Zn/* e */ = function(_Zo/* s7ZN */, _Zp/* s7ZO */){
  return 1-B(A1(_Zo/* s7ZN */,new T(function(){
    return Math.pow/* EXTERNAL */(2,  -((1-(1-E(_Zp/* s7ZO */)))*10));
  })));
},
_Zq/* $fRealDouble1 */ = new T1(0,1),
_Zr/* encodeDoubleInteger */ = function(_Zs/* s1LC */, _Zt/* s1LD */){
  var _Zu/* s1LE */ = E(_Zs/* s1LC */);
  return (_Zu/* s1LE */._==0) ? _Zu/* s1LE */.a*Math.pow/* EXTERNAL */(2, _Zt/* s1LD */) : I_toNumber/* EXTERNAL */(_Zu/* s1LE */.a)*Math.pow/* EXTERNAL */(2, _Zt/* s1LD */);
},
_Zv/* rationalToDouble5 */ = new T1(0,0),
_Zw/* $w$j1 */ = function(_Zx/* s18QG */, _Zy/* s18QH */, _Zz/* s18QI */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_Zz/* s18QI */, _Zv/* GHC.Float.rationalToDouble5 */))){
    var _ZA/* s18QK */ = B(_VB/* GHC.Integer.Type.quotRemInteger */(_Zy/* s18QH */, _Zz/* s18QI */)),
    _ZB/* s18QL */ = _ZA/* s18QK */.a;
    switch(B(_Wg/* GHC.Integer.Type.compareInteger */(B(_Jy/* GHC.Integer.Type.shiftLInteger */(_ZA/* s18QK */.b, 1)), _Zz/* s18QI */))){
      case 0:
        return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(_ZB/* s18QL */, _Zx/* s18QG */);});
        break;
      case 1:
        if(!(B(_US/* GHC.Integer.Type.integerToInt */(_ZB/* s18QL */))&1)){
          return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(_ZB/* s18QL */, _Zx/* s18QG */);});
        }else{
          return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_ZB/* s18QL */, _Zq/* GHC.Float.$fRealDouble1 */)), _Zx/* s18QG */);});
        }
        break;
      default:
        return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_ZB/* s18QL */, _Zq/* GHC.Float.$fRealDouble1 */)), _Zx/* s18QG */);});
    }
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_ZC/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_ZD/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_ZE/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_ZF/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_ZC/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_ZD/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_ZE/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_ZG/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_ZF/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_ZH/* $fExceptionPatternMatchFail1 */ = function(_ZI/* s4nDQ */){
  return E(_ZG/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_ZJ/* $fExceptionPatternMatchFail_$cfromException */ = function(_ZK/* s4nE1 */){
  var _ZL/* s4nE2 */ = E(_ZK/* s4nE1 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_ZL/* s4nE2 */.a)), _ZH/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _ZL/* s4nE2 */.b);});
},
_ZM/* $fExceptionPatternMatchFail_$cshow */ = function(_ZN/* s4nDT */){
  return E(E(_ZN/* s4nDT */).a);
},
_ZO/* $fExceptionPatternMatchFail_$ctoException */ = function(_ZP/* B1 */){
  return new T2(0,_ZQ/* Control.Exception.Base.$fExceptionPatternMatchFail */,_ZP/* B1 */);
},
_ZR/* $fShowPatternMatchFail1 */ = function(_ZS/* s4nzz */, _ZT/* s4nzA */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_ZS/* s4nzz */).a, _ZT/* s4nzA */);});
},
_ZU/* $fShowPatternMatchFail_$cshowList */ = function(_ZV/* s4nDR */, _ZW/* s4nDS */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_ZR/* Control.Exception.Base.$fShowPatternMatchFail1 */, _ZV/* s4nDR */, _ZW/* s4nDS */);});
},
_ZX/* $fShowPatternMatchFail_$cshowsPrec */ = function(_ZY/* s4nDW */, _ZZ/* s4nDX */, _100/* s4nDY */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_ZZ/* s4nDX */).a, _100/* s4nDY */);});
},
_101/* $fShowPatternMatchFail */ = new T3(0,_ZX/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_ZM/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_ZU/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_ZQ/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_ZH/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_101/* Control.Exception.Base.$fShowPatternMatchFail */,_ZO/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_ZJ/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_ZM/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_102/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_103/* lvl */ = function(_104/* s2S2g */, _105/* s2S2h */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_105/* s2S2h */, _104/* s2S2g */));
  }));});
},
_106/* throw1 */ = function(_107/* B2 */, _OR/* B1 */){
  return new F(function(){return _103/* GHC.Exception.lvl */(_107/* B2 */, _OR/* B1 */);});
},
_108/* $wspan */ = function(_109/* s9wA */, _10a/* s9wB */){
  var _10b/* s9wC */ = E(_10a/* s9wB */);
  if(!_10b/* s9wC */._){
    return new T2(0,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */);
  }else{
    var _10c/* s9wD */ = _10b/* s9wC */.a;
    if(!B(A1(_109/* s9wA */,_10c/* s9wD */))){
      return new T2(0,_6/* GHC.Types.[] */,_10b/* s9wC */);
    }else{
      var _10d/* s9wG */ = new T(function(){
        var _10e/* s9wH */ = B(_108/* GHC.List.$wspan */(_109/* s9wA */, _10b/* s9wC */.b));
        return new T2(0,_10e/* s9wH */.a,_10e/* s9wH */.b);
      });
      return new T2(0,new T2(1,_10c/* s9wD */,new T(function(){
        return E(E(_10d/* s9wG */).a);
      })),new T(function(){
        return E(E(_10d/* s9wG */).b);
      }));
    }
  }
},
_10f/* untangle1 */ = 32,
_10g/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_10h/* untangle3 */ = function(_10i/* s3JKg */){
  return (E(_10i/* s3JKg */)==124) ? false : true;
},
_10j/* untangle */ = function(_10k/* s3JL9 */, _10l/* s3JLa */){
  var _10m/* s3JLc */ = B(_108/* GHC.List.$wspan */(_10h/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_10k/* s3JL9 */)))),
  _10n/* s3JLd */ = _10m/* s3JLc */.a,
  _10o/* s3JLf */ = function(_10p/* s3JLg */, _10q/* s3JLh */){
    var _10r/* s3JLk */ = new T(function(){
      var _10s/* s3JLj */ = new T(function(){
        return B(_2/* GHC.Base.++ */(_10l/* s3JLa */, new T(function(){
          return B(_2/* GHC.Base.++ */(_10q/* s3JLh */, _10g/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _10s/* s3JLj */));
    },1);
    return new F(function(){return _2/* GHC.Base.++ */(_10p/* s3JLg */, _10r/* s3JLk */);});
  },
  _10t/* s3JLl */ = E(_10m/* s3JLc */.b);
  if(!_10t/* s3JLl */._){
    return new F(function(){return _10o/* s3JLf */(_10n/* s3JLd */, _6/* GHC.Types.[] */);});
  }else{
    if(E(_10t/* s3JLl */.a)==124){
      return new F(function(){return _10o/* s3JLf */(_10n/* s3JLd */, new T2(1,_10f/* GHC.IO.Exception.untangle1 */,_10t/* s3JLl */.b));});
    }else{
      return new F(function(){return _10o/* s3JLf */(_10n/* s3JLd */, _6/* GHC.Types.[] */);});
    }
  }
},
_10u/* patError */ = function(_10v/* s4nFx */){
  return new F(function(){return _106/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_10j/* GHC.IO.Exception.untangle */(_10v/* s4nFx */, _102/* Control.Exception.Base.lvl3 */));
  })), _ZQ/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_10w/* log2I */ = function(_10x/* s1Ju */){
  var _10y/* s1Jv */ = function(_10z/* s1Jw */, _10A/* s1Jx */){
    while(1){
      if(!B(_KW/* GHC.Integer.Type.ltInteger */(_10z/* s1Jw */, _10x/* s1Ju */))){
        if(!B(_Kq/* GHC.Integer.Type.gtInteger */(_10z/* s1Jw */, _10x/* s1Ju */))){
          if(!B(_QT/* GHC.Integer.Type.eqInteger */(_10z/* s1Jw */, _10x/* s1Ju */))){
            return new F(function(){return _10u/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});
          }else{
            return E(_10A/* s1Jx */);
          }
        }else{
          return _10A/* s1Jx */-1|0;
        }
      }else{
        var _10B/*  s1Jw */ = B(_Jy/* GHC.Integer.Type.shiftLInteger */(_10z/* s1Jw */, 1)),
        _10C/*  s1Jx */ = _10A/* s1Jx */+1|0;
        _10z/* s1Jw */ = _10B/*  s1Jw */;
        _10A/* s1Jx */ = _10C/*  s1Jx */;
        continue;
      }
    }
  };
  return new F(function(){return _10y/* s1Jv */(_JF/* GHC.Integer.Type.log2I1 */, 0);});
},
_10D/* integerLog2# */ = function(_10E/* s1JD */){
  var _10F/* s1JE */ = E(_10E/* s1JD */);
  if(!_10F/* s1JE */._){
    var _10G/* s1JG */ = _10F/* s1JE */.a>>>0;
    if(!_10G/* s1JG */){
      return -1;
    }else{
      var _10H/* s1JH */ = function(_10I/* s1JI */, _10J/* s1JJ */){
        while(1){
          if(_10I/* s1JI */>=_10G/* s1JG */){
            if(_10I/* s1JI */<=_10G/* s1JG */){
              if(_10I/* s1JI */!=_10G/* s1JG */){
                return new F(function(){return _10u/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_10J/* s1JJ */);
              }
            }else{
              return _10J/* s1JJ */-1|0;
            }
          }else{
            var _10K/*  s1JI */ = imul/* EXTERNAL */(_10I/* s1JI */, 2)>>>0,
            _10L/*  s1JJ */ = _10J/* s1JJ */+1|0;
            _10I/* s1JI */ = _10K/*  s1JI */;
            _10J/* s1JJ */ = _10L/*  s1JJ */;
            continue;
          }
        }
      };
      return new F(function(){return _10H/* s1JH */(1, 0);});
    }
  }else{
    return new F(function(){return _10w/* GHC.Integer.Type.log2I */(_10F/* s1JE */);});
  }
},
_10M/* integerLog2IsPowerOf2# */ = function(_10N/* s1JT */){
  var _10O/* s1JU */ = E(_10N/* s1JT */);
  if(!_10O/* s1JU */._){
    var _10P/* s1JW */ = _10O/* s1JU */.a>>>0;
    if(!_10P/* s1JW */){
      return new T2(0,-1,0);
    }else{
      var _10Q/* s1JX */ = function(_10R/* s1JY */, _10S/* s1JZ */){
        while(1){
          if(_10R/* s1JY */>=_10P/* s1JW */){
            if(_10R/* s1JY */<=_10P/* s1JW */){
              if(_10R/* s1JY */!=_10P/* s1JW */){
                return new F(function(){return _10u/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_10S/* s1JZ */);
              }
            }else{
              return _10S/* s1JZ */-1|0;
            }
          }else{
            var _10T/*  s1JY */ = imul/* EXTERNAL */(_10R/* s1JY */, 2)>>>0,
            _10U/*  s1JZ */ = _10S/* s1JZ */+1|0;
            _10R/* s1JY */ = _10T/*  s1JY */;
            _10S/* s1JZ */ = _10U/*  s1JZ */;
            continue;
          }
        }
      };
      return new T2(0,B(_10Q/* s1JX */(1, 0)),(_10P/* s1JW */&_10P/* s1JW */-1>>>0)>>>0&4294967295);
    }
  }else{
    var _10V/* s1Kc */ = _10O/* s1JU */.a;
    return new T2(0,B(_10D/* GHC.Integer.Type.integerLog2# */(_10O/* s1JU */)),I_compareInt/* EXTERNAL */(I_and/* EXTERNAL */(_10V/* s1Kc */, I_sub/* EXTERNAL */(_10V/* s1Kc */, I_fromInt/* EXTERNAL */(1))), 0));
  }
},
_10W/* andInteger */ = function(_10X/* s1Lf */, _10Y/* s1Lg */){
  while(1){
    var _10Z/* s1Lh */ = E(_10X/* s1Lf */);
    if(!_10Z/* s1Lh */._){
      var _110/* s1Li */ = _10Z/* s1Lh */.a,
      _111/* s1Lj */ = E(_10Y/* s1Lg */);
      if(!_111/* s1Lj */._){
        return new T1(0,(_110/* s1Li */>>>0&_111/* s1Lj */.a>>>0)>>>0&4294967295);
      }else{
        _10X/* s1Lf */ = new T1(1,I_fromInt/* EXTERNAL */(_110/* s1Li */));
        _10Y/* s1Lg */ = _111/* s1Lj */;
        continue;
      }
    }else{
      var _112/* s1Lu */ = E(_10Y/* s1Lg */);
      if(!_112/* s1Lu */._){
        _10X/* s1Lf */ = _10Z/* s1Lh */;
        _10Y/* s1Lg */ = new T1(1,I_fromInt/* EXTERNAL */(_112/* s1Lu */.a));
        continue;
      }else{
        return new T1(1,I_and/* EXTERNAL */(_10Z/* s1Lh */.a, _112/* s1Lu */.a));
      }
    }
  }
},
_113/* roundingMode#1 */ = new T1(0,2),
_114/* roundingMode# */ = function(_115/* s1Pt */, _116/* s1Pu */){
  var _117/* s1Pv */ = E(_115/* s1Pt */);
  if(!_117/* s1Pv */._){
    var _118/* s1Px */ = (_117/* s1Pv */.a>>>0&(2<<_116/* s1Pu */>>>0)-1>>>0)>>>0,
    _119/* s1PB */ = 1<<_116/* s1Pu */>>>0;
    return (_119/* s1PB */<=_118/* s1Px */) ? (_119/* s1PB */>=_118/* s1Px */) ? 1 : 2 : 0;
  }else{
    var _11a/* s1PH */ = B(_10W/* GHC.Integer.Type.andInteger */(_117/* s1Pv */, B(_Lm/* GHC.Integer.Type.minusInteger */(B(_Jy/* GHC.Integer.Type.shiftLInteger */(_113/* GHC.Integer.Type.roundingMode#1 */, _116/* s1Pu */)), _JF/* GHC.Integer.Type.log2I1 */)))),
    _11b/* s1PK */ = B(_Jy/* GHC.Integer.Type.shiftLInteger */(_JF/* GHC.Integer.Type.log2I1 */, _116/* s1Pu */));
    return (!B(_Kq/* GHC.Integer.Type.gtInteger */(_11b/* s1PK */, _11a/* s1PH */))) ? (!B(_KW/* GHC.Integer.Type.ltInteger */(_11b/* s1PK */, _11a/* s1PH */))) ? 1 : 2 : 0;
  }
},
_11c/* shiftRInteger */ = function(_11d/* s1Ja */, _11e/* s1Jb */){
  while(1){
    var _11f/* s1Jc */ = E(_11d/* s1Ja */);
    if(!_11f/* s1Jc */._){
      _11d/* s1Ja */ = new T1(1,I_fromInt/* EXTERNAL */(_11f/* s1Jc */.a));
      continue;
    }else{
      return new T1(1,I_shiftRight/* EXTERNAL */(_11f/* s1Jc */.a, _11e/* s1Jb */));
    }
  }
},
_11g/* $w$sfromRat'' */ = function(_11h/* s18QU */, _11i/* s18QV */, _11j/* s18QW */, _11k/* s18QX */){
  var _11l/* s18QY */ = B(_10M/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_11k/* s18QX */)),
  _11m/* s18QZ */ = _11l/* s18QY */.a;
  if(!E(_11l/* s18QY */.b)){
    var _11n/* s18Rp */ = B(_10D/* GHC.Integer.Type.integerLog2# */(_11j/* s18QW */));
    if(_11n/* s18Rp */<((_11m/* s18QZ */+_11h/* s18QU */|0)-1|0)){
      var _11o/* s18Ru */ = _11m/* s18QZ */+(_11h/* s18QU */-_11i/* s18QV */|0)|0;
      if(_11o/* s18Ru */>0){
        if(_11o/* s18Ru */>_11n/* s18Rp */){
          if(_11o/* s18Ru */<=(_11n/* s18Rp */+1|0)){
            if(!E(B(_10M/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_11j/* s18QW */)).b)){
              return 0;
            }else{
              return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(_Zq/* GHC.Float.$fRealDouble1 */, _11h/* s18QU */-_11i/* s18QV */|0);});
            }
          }else{
            return 0;
          }
        }else{
          var _11p/* s18RI */ = B(_11c/* GHC.Integer.Type.shiftRInteger */(_11j/* s18QW */, _11o/* s18Ru */));
          switch(B(_114/* GHC.Integer.Type.roundingMode# */(_11j/* s18QW */, _11o/* s18Ru */-1|0))){
            case 0:
              return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(_11p/* s18RI */, _11h/* s18QU */-_11i/* s18QV */|0);});
              break;
            case 1:
              if(!(B(_US/* GHC.Integer.Type.integerToInt */(_11p/* s18RI */))&1)){
                return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(_11p/* s18RI */, _11h/* s18QU */-_11i/* s18QV */|0);});
              }else{
                return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_11p/* s18RI */, _Zq/* GHC.Float.$fRealDouble1 */)), _11h/* s18QU */-_11i/* s18QV */|0);});
              }
              break;
            default:
              return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_11p/* s18RI */, _Zq/* GHC.Float.$fRealDouble1 */)), _11h/* s18QU */-_11i/* s18QV */|0);});
          }
        }
      }else{
        return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(_11j/* s18QW */, (_11h/* s18QU */-_11i/* s18QV */|0)-_11o/* s18Ru */|0);});
      }
    }else{
      if(_11n/* s18Rp */>=_11i/* s18QV */){
        var _11q/* s18RX */ = B(_11c/* GHC.Integer.Type.shiftRInteger */(_11j/* s18QW */, (_11n/* s18Rp */+1|0)-_11i/* s18QV */|0));
        switch(B(_114/* GHC.Integer.Type.roundingMode# */(_11j/* s18QW */, _11n/* s18Rp */-_11i/* s18QV */|0))){
          case 0:
            return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(_11q/* s18RX */, ((_11n/* s18Rp */-_11m/* s18QZ */|0)+1|0)-_11i/* s18QV */|0);});
            break;
          case 2:
            return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_11q/* s18RX */, _Zq/* GHC.Float.$fRealDouble1 */)), ((_11n/* s18Rp */-_11m/* s18QZ */|0)+1|0)-_11i/* s18QV */|0);});
            break;
          default:
            if(!(B(_US/* GHC.Integer.Type.integerToInt */(_11q/* s18RX */))&1)){
              return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(_11q/* s18RX */, ((_11n/* s18Rp */-_11m/* s18QZ */|0)+1|0)-_11i/* s18QV */|0);});
            }else{
              return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_11q/* s18RX */, _Zq/* GHC.Float.$fRealDouble1 */)), ((_11n/* s18Rp */-_11m/* s18QZ */|0)+1|0)-_11i/* s18QV */|0);});
            }
        }
      }else{
        return new F(function(){return _Zr/* GHC.Integer.Type.encodeDoubleInteger */(_11j/* s18QW */,  -_11m/* s18QZ */);});
      }
    }
  }else{
    var _11r/* s18R3 */ = B(_10D/* GHC.Integer.Type.integerLog2# */(_11j/* s18QW */))-_11m/* s18QZ */|0,
    _11s/* s18R4 */ = function(_11t/* s18R5 */){
      var _11u/* s18R6 */ = function(_11v/* s18R7 */, _11w/* s18R8 */){
        if(!B(_W2/* GHC.Integer.Type.leInteger */(B(_Jy/* GHC.Integer.Type.shiftLInteger */(_11w/* s18R8 */, _11i/* s18QV */)), _11v/* s18R7 */))){
          return new F(function(){return _Zw/* GHC.Float.$w$j1 */(_11t/* s18R5 */-_11i/* s18QV */|0, _11v/* s18R7 */, _11w/* s18R8 */);});
        }else{
          return new F(function(){return _Zw/* GHC.Float.$w$j1 */((_11t/* s18R5 */-_11i/* s18QV */|0)+1|0, _11v/* s18R7 */, B(_Jy/* GHC.Integer.Type.shiftLInteger */(_11w/* s18R8 */, 1)));});
        }
      };
      if(_11t/* s18R5 */>=_11i/* s18QV */){
        if(_11t/* s18R5 */!=_11i/* s18QV */){
          return new F(function(){return _11u/* s18R6 */(_11j/* s18QW */, new T(function(){
            return B(_Jy/* GHC.Integer.Type.shiftLInteger */(_11k/* s18QX */, _11t/* s18R5 */-_11i/* s18QV */|0));
          }));});
        }else{
          return new F(function(){return _11u/* s18R6 */(_11j/* s18QW */, _11k/* s18QX */);});
        }
      }else{
        return new F(function(){return _11u/* s18R6 */(new T(function(){
          return B(_Jy/* GHC.Integer.Type.shiftLInteger */(_11j/* s18QW */, _11i/* s18QV */-_11t/* s18R5 */|0));
        }), _11k/* s18QX */);});
      }
    };
    if(_11h/* s18QU */>_11r/* s18R3 */){
      return new F(function(){return _11s/* s18R4 */(_11h/* s18QU */);});
    }else{
      return new F(function(){return _11s/* s18R4 */(_11r/* s18R3 */);});
    }
  }
},
_11x/* rationalToDouble1 */ = new T(function(){
  return 0/0;
}),
_11y/* rationalToDouble2 */ = new T(function(){
  return -1/0;
}),
_11z/* rationalToDouble3 */ = new T(function(){
  return 1/0;
}),
_11A/* rationalToDouble4 */ = 0,
_11B/* rationalToDouble */ = function(_11C/* s197E */, _11D/* s197F */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_11D/* s197F */, _Zv/* GHC.Float.rationalToDouble5 */))){
    if(!B(_QT/* GHC.Integer.Type.eqInteger */(_11C/* s197E */, _Zv/* GHC.Float.rationalToDouble5 */))){
      if(!B(_KW/* GHC.Integer.Type.ltInteger */(_11C/* s197E */, _Zv/* GHC.Float.rationalToDouble5 */))){
        return new F(function(){return _11g/* GHC.Float.$w$sfromRat'' */(-1021, 53, _11C/* s197E */, _11D/* s197F */);});
      }else{
        return  -B(_11g/* GHC.Float.$w$sfromRat'' */(-1021, 53, B(_JR/* GHC.Integer.Type.negateInteger */(_11C/* s197E */)), _11D/* s197F */));
      }
    }else{
      return E(_11A/* GHC.Float.rationalToDouble4 */);
    }
  }else{
    return (!B(_QT/* GHC.Integer.Type.eqInteger */(_11C/* s197E */, _Zv/* GHC.Float.rationalToDouble5 */))) ? (!B(_KW/* GHC.Integer.Type.ltInteger */(_11C/* s197E */, _Zv/* GHC.Float.rationalToDouble5 */))) ? E(_11z/* GHC.Float.rationalToDouble3 */) : E(_11y/* GHC.Float.rationalToDouble2 */) : E(_11x/* GHC.Float.rationalToDouble1 */);
  }
},
_11E/* $fFractionalDouble_$cfromRational */ = function(_11F/* s197P */){
  var _11G/* s197Q */ = E(_11F/* s197P */);
  return new F(function(){return _11B/* GHC.Float.rationalToDouble */(_11G/* s197Q */.a, _11G/* s197Q */.b);});
},
_11H/* $fFractionalDouble_$crecip */ = function(_11I/* s191m */){
  return 1/E(_11I/* s191m */);
},
_11J/* $fNumDouble_$cabs */ = function(_11K/* s190N */){
  var _11L/* s190O */ = E(_11K/* s190N */),
  _11M/* s190Q */ = E(_11L/* s190O */);
  return (_11M/* s190Q */==0) ? E(_11A/* GHC.Float.rationalToDouble4 */) : (_11M/* s190Q */<=0) ?  -_11M/* s190Q */ : E(_11L/* s190O */);
},
_11N/* $fNumDouble_$cfromInteger */ = function(_11O/* s190E */){
  return new F(function(){return _Sv/* GHC.Integer.Type.doubleFromInteger */(_11O/* s190E */);});
},
_11P/* $fNumDouble1 */ = 1,
_11Q/* $fNumDouble2 */ = -1,
_11R/* $fNumDouble_$csignum */ = function(_11S/* s190G */){
  var _11T/* s190H */ = E(_11S/* s190G */);
  return (_11T/* s190H */<=0) ? (_11T/* s190H */>=0) ? E(_11T/* s190H */) : E(_11Q/* GHC.Float.$fNumDouble2 */) : E(_11P/* GHC.Float.$fNumDouble1 */);
},
_11U/* minusDouble */ = function(_11V/* s18yR */, _11W/* s18yS */){
  return E(_11V/* s18yR */)-E(_11W/* s18yS */);
},
_11X/* $fNumDouble */ = {_:0,a:_BU/* GHC.Float.plusDouble */,b:_11U/* GHC.Float.minusDouble */,c:_vu/* GHC.Float.timesDouble */,d:_FA/* GHC.Float.negateDouble */,e:_11J/* GHC.Float.$fNumDouble_$cabs */,f:_11R/* GHC.Float.$fNumDouble_$csignum */,g:_11N/* GHC.Float.$fNumDouble_$cfromInteger */},
_11Y/* $fFractionalDouble */ = new T4(0,_11X/* GHC.Float.$fNumDouble */,_in/* GHC.Float.divideDouble */,_11H/* GHC.Float.$fFractionalDouble_$crecip */,_11E/* GHC.Float.$fFractionalDouble_$cfromRational */),
_11Z/* $fEqDouble_$c/= */ = function(_120/* scFX */, _121/* scFY */){
  return (E(_120/* scFX */)!=E(_121/* scFY */)) ? true : false;
},
_122/* $fEqDouble_$c== */ = function(_123/* scFQ */, _124/* scFR */){
  return E(_123/* scFQ */)==E(_124/* scFR */);
},
_125/* $fEqDouble */ = new T2(0,_122/* GHC.Classes.$fEqDouble_$c== */,_11Z/* GHC.Classes.$fEqDouble_$c/= */),
_126/* $fOrdDouble_$c< */ = function(_127/* scIa */, _128/* scIb */){
  return E(_127/* scIa */)<E(_128/* scIb */);
},
_129/* $fOrdDouble_$c<= */ = function(_12a/* scI3 */, _12b/* scI4 */){
  return E(_12a/* scI3 */)<=E(_12b/* scI4 */);
},
_12c/* $fOrdDouble_$c> */ = function(_12d/* scHW */, _12e/* scHX */){
  return E(_12d/* scHW */)>E(_12e/* scHX */);
},
_12f/* $fOrdDouble_$c>= */ = function(_12g/* scHP */, _12h/* scHQ */){
  return E(_12g/* scHP */)>=E(_12h/* scHQ */);
},
_12i/* $fOrdDouble_$ccompare */ = function(_12j/* scIh */, _12k/* scIi */){
  var _12l/* scIj */ = E(_12j/* scIh */),
  _12m/* scIl */ = E(_12k/* scIi */);
  return (_12l/* scIj */>=_12m/* scIl */) ? (_12l/* scIj */!=_12m/* scIl */) ? 2 : 1 : 0;
},
_12n/* $fOrdDouble_$cmax */ = function(_12o/* scIz */, _12p/* scIA */){
  var _12q/* scIB */ = E(_12o/* scIz */),
  _12r/* scID */ = E(_12p/* scIA */);
  return (_12q/* scIB */>_12r/* scID */) ? E(_12q/* scIB */) : E(_12r/* scID */);
},
_12s/* $fOrdDouble_$cmin */ = function(_12t/* scIr */, _12u/* scIs */){
  var _12v/* scIt */ = E(_12t/* scIr */),
  _12w/* scIv */ = E(_12u/* scIs */);
  return (_12v/* scIt */>_12w/* scIv */) ? E(_12w/* scIv */) : E(_12v/* scIt */);
},
_12x/* $fOrdDouble */ = {_:0,a:_125/* GHC.Classes.$fEqDouble */,b:_12i/* GHC.Classes.$fOrdDouble_$ccompare */,c:_126/* GHC.Classes.$fOrdDouble_$c< */,d:_129/* GHC.Classes.$fOrdDouble_$c<= */,e:_12c/* GHC.Classes.$fOrdDouble_$c> */,f:_12f/* GHC.Classes.$fOrdDouble_$c>= */,g:_12n/* GHC.Classes.$fOrdDouble_$cmax */,h:_12s/* GHC.Classes.$fOrdDouble_$cmin */},
_12y/* lvl8 */ = -1,
_12z/* $p1Fractional */ = function(_12A/* svdN */){
  return E(E(_12A/* svdN */).a);
},
_12B/* + */ = function(_12C/* s6Fy */){
  return E(E(_12C/* s6Fy */).a);
},
_12D/* $wnumericEnumFrom */ = function(_12E/* svLB */, _12F/* svLC */){
  var _12G/* svLD */ = E(_12F/* svLC */),
  _12H/* svLK */ = new T(function(){
    var _12I/* svLE */ = B(_12z/* GHC.Real.$p1Fractional */(_12E/* svLB */)),
    _12J/* svLH */ = B(_12D/* GHC.Real.$wnumericEnumFrom */(_12E/* svLB */, B(A3(_12B/* GHC.Num.+ */,_12I/* svLE */, _12G/* svLD */, new T(function(){
      return B(A2(_Ko/* GHC.Num.fromInteger */,_12I/* svLE */, _Kj/* GHC.Real.$fEnumRatio1 */));
    })))));
    return new T2(1,_12J/* svLH */.a,_12J/* svLH */.b);
  });
  return new T2(0,_12G/* svLD */,_12H/* svLK */);
},
_12K/* / */ = function(_12L/* svdT */){
  return E(E(_12L/* svdT */).b);
},
_12M/* <= */ = function(_12N/* scCl */){
  return E(E(_12N/* scCl */).d);
},
_12O/* takeWhile */ = function(_12P/* s9yw */, _12Q/* s9yx */){
  var _12R/* s9yy */ = E(_12Q/* s9yx */);
  if(!_12R/* s9yy */._){
    return __Z/* EXTERNAL */;
  }else{
    var _12S/* s9yz */ = _12R/* s9yy */.a;
    return (!B(A1(_12P/* s9yw */,_12S/* s9yz */))) ? __Z/* EXTERNAL */ : new T2(1,_12S/* s9yz */,new T(function(){
      return B(_12O/* GHC.List.takeWhile */(_12P/* s9yw */, _12R/* s9yy */.b));
    }));
  }
},
_12T/* numericEnumFromTo */ = function(_12U/* svMm */, _12V/* svMn */, _12W/* svMo */, _12X/* svMp */){
  var _12Y/* svMq */ = B(_12D/* GHC.Real.$wnumericEnumFrom */(_12V/* svMn */, _12W/* svMo */)),
  _12Z/* svMt */ = new T(function(){
    var _130/* svMu */ = B(_12z/* GHC.Real.$p1Fractional */(_12V/* svMn */)),
    _131/* svMx */ = new T(function(){
      return B(A3(_12K/* GHC.Real./ */,_12V/* svMn */, new T(function(){
        return B(A2(_Ko/* GHC.Num.fromInteger */,_130/* svMu */, _Kj/* GHC.Real.$fEnumRatio1 */));
      }), new T(function(){
        return B(A2(_Ko/* GHC.Num.fromInteger */,_130/* svMu */, _RU/* GHC.Real.even2 */));
      })));
    });
    return B(A3(_12B/* GHC.Num.+ */,_130/* svMu */, _12X/* svMp */, _131/* svMx */));
  });
  return new F(function(){return _12O/* GHC.List.takeWhile */(function(_132/* svMy */){
    return new F(function(){return A3(_12M/* GHC.Classes.<= */,_12U/* svMm */, _132/* svMy */, _12Z/* svMt */);});
  }, new T2(1,_12Y/* svMq */.a,_12Y/* svMq */.b));});
},
_133/* x */ = 1,
_134/* lvl9 */ = new T(function(){
  return B(_12T/* GHC.Real.numericEnumFromTo */(_12x/* GHC.Classes.$fOrdDouble */, _11Y/* GHC.Float.$fFractionalDouble */, _12y/* Motion.Change.lvl8 */, _133/* Motion.Change.x */));
}),
_135/* go */ = function(_136/* s800 */){
  var _137/* s801 */ = E(_136/* s800 */);
  if(!_137/* s801 */._){
    return __Z/* EXTERNAL */;
  }else{
    var _138/* s804 */ = new T(function(){
      return E(_137/* s801 */.a)*100;
    }),
    _139/* s808 */ = new T(function(){
      return B(_135/* Motion.Change.go */(_137/* s801 */.b));
    }),
    _13a/* s809 */ = function(_13b/* s80a */){
      var _13c/* s80b */ = E(_13b/* s80a */);
      return (_13c/* s80b */._==0) ? E(_139/* s808 */) : new T2(1,new T2(0,_138/* s804 */,new T(function(){
        return E(_13c/* s80b */.a)*100;
      })),new T(function(){
        return B(_13a/* s809 */(_13c/* s80b */.b));
      }));
    };
    return new F(function(){return _13a/* s809 */(_134/* Motion.Change.lvl9 */);});
  }
},
_13d/* lvl10 */ = new T(function(){
  return B(_135/* Motion.Change.go */(_134/* Motion.Change.lvl9 */));
}),
_13e/* lvl11 */ = 1.5,
_13f/* lvl12 */ = new T1(0,0),
_13g/* lvl13 */ = new T2(0,_13f/* Motion.Change.lvl12 */,_6/* GHC.Types.[] */),
_13h/* lvl14 */ = new T4(0,_133/* Motion.Change.x */,_133/* Motion.Change.x */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_13i/* lvl15 */ = new T2(0,_133/* Motion.Change.x */,_13h/* Motion.Change.lvl14 */),
_13j/* lvl16 */ = new T2(0,_13i/* Motion.Change.lvl15 */,_6/* GHC.Types.[] */),
_13k/* a9 */ = 100,
_13l/* lvl5 */ = new T1(0,_13k/* Motion.Change.a9 */),
_13m/* lvl6 */ = new T2(0,_13l/* Motion.Change.lvl5 */,_13l/* Motion.Change.lvl5 */),
_13n/* a10 */ = 3,
_13o/* lvl7 */ = new T1(0,_13n/* Motion.Change.a10 */),
_13p/* valueIO1 */ = function(_13q/* sb3M */, _/* EXTERNAL */){
  var _13r/* sb3O */ = E(_13q/* sb3M */);
  switch(_13r/* sb3O */._){
    case 0:
      return new T1(1,_13r/* sb3O */.a);
    case 1:
      var _13s/* sb3S */ = B(A1(_13r/* sb3O */.a,_/* EXTERNAL */));
      return new T1(1,_13s/* sb3S */);
    case 2:
      var _13t/* sb44 */ = rMV/* EXTERNAL */(E(E(_13r/* sb3O */.a).c)),
      _13u/* sb47 */ = E(_13t/* sb44 */);
      if(!_13u/* sb47 */._){
        var _13v/* sb4b */ = new T(function(){
          return B(A1(_13r/* sb3O */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_13u/* sb47 */.a));
          })));
        });
        return new T1(1,_13v/* sb4b */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
      break;
    default:
      var _13w/* sb4m */ = rMV/* EXTERNAL */(E(E(_13r/* sb3O */.a).c)),
      _13x/* sb4p */ = E(_13w/* sb4m */);
      if(!_13x/* sb4p */._){
        var _13y/* sb4v */ = B(A2(_13r/* sb3O */.b,E(_13x/* sb4p */.a).a, _/* EXTERNAL */));
        return new T1(1,_13y/* sb4v */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
  }
},
_13z/* changeMot1 */ = function(_13A/* s80k */, _13B/* s80l */){
  var _13C/* s80m */ = new T(function(){
    return B(_YP/* Motion.Change.$sreplicateM2 */(_Zl/* Motion.Change.a8 */, _13B/* s80l */));
  }),
  _13D/* s80n */ = function(_13E/* s80o */, _13F/* s80p */){
    var _13G/* s80q */ = E(_13E/* s80o */);
    if(!_13G/* s80q */._){
      return E(_Z8/* Motion.Change.a2 */);
    }else{
      var _13H/* s80t */ = E(_13F/* s80p */);
      if(!_13H/* s80t */._){
        return E(_Z8/* Motion.Change.a2 */);
      }else{
        var _13I/* s80w */ = E(_13H/* s80t */.a),
        _13J/* s80z */ = new T(function(){
          return B(_HY/* Core.Ease.morph */(_13G/* s80q */.a));
        }),
        _13K/* s80C */ = B(_pg/* Control.Monad.Skeleton.bone */(new T1(1,function(_/* EXTERNAL */){
          return new F(function(){return _13p/* Core.Ease.valueIO1 */(_13J/* s80z */, _/* EXTERNAL */);});
        }))),
        _13L/* s80F */ = new T(function(){
          return B(_13D/* s80n */(_13G/* s80q */.b, _13H/* s80t */.b));
        }),
        _13M/* s80G */ = new T(function(){
          return B(_ro/* Core.Render.Internal.fill1 */(_13A/* s80k */, new T(function(){
            var _13N/* s80J */ = B(_Gl/* Core.Shape.Internal.$wcenterRect */(new T1(0,_13I/* s80w */.a), new T1(0,_13I/* s80w */.b), _13l/* Motion.Change.lvl5 */, _13l/* Motion.Change.lvl5 */));
            return new T3(0,_13N/* s80J */.a,_13N/* s80J */.b,_13N/* s80J */.c);
          })));
        });
        return new T2(0,E(_13K/* s80C */.a),E(new T2(2,new T2(2,_13K/* s80C */.b,new T1(1,function(_13O/* s80O */){
          var _13P/* s80P */ = E(_13O/* s80O */);
          return (_13P/* s80P */._==0) ? E(_Z4/* Motion.Change.$swhen1 */) : (!E(_13P/* s80P */.a)) ? E(_Z4/* Motion.Change.$swhen1 */) : E(_13M/* s80G */);
        })),new T1(1,function(_13Q/* s80V */){
          return E(_13L/* s80F */);
        }))));
      }
    }
  },
  _13R/* s82F */ = function(_13S/* s80Z */){
    var _13T/* s82E */ = function(_13U/* s810 */){
      var _13V/* s811 */ = E(_13U/* s810 */),
      _13W/* s812 */ = _13V/* s811 */.a,
      _13X/* s82D */ = function(_/* EXTERNAL */){
        var _13Y/* s815 */ = nMV/* EXTERNAL */(_13j/* Motion.Change.lvl16 */),
        _13Z/* s819 */ = new T3(0,_Zm/* Motion.Change.dur */,_Zn/* Motion.Change.e */,_13Y/* s815 */),
        _140/* s81a */ = new T(function(){
          return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Zm/* Motion.Change.dur */, _Zn/* Motion.Change.e */, _13Y/* s815 */, _133/* Motion.Change.x */, _tT/* Core.Ease.easeTo1 */));
        }),
        _141/* s81b */ = new T(function(){
          return B(_wJ/* Core.Ease.$wforceTo */(_13Y/* s815 */, _13e/* Motion.Change.lvl11 */));
        }),
        _142/* s81c */ = function(_143/* s81h */){
          return new F(function(){return _144/* s81g */(E(_143/* s81h */).b);});
        },
        _145/* s81d */ = function(_146/* s81l */){
          return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_Z5/* Motion.Change.a11 */, E(_146/* s81l */).b, _142/* s81c */);});
        },
        _147/* s81e */ = function(_148/* s81p */){
          return new F(function(){return A2(_140/* s81a */,E(_148/* s81p */).b, _145/* s81d */);});
        },
        _149/* s81f */ = function(_14a/* s81t */){
          return new F(function(){return A2(_141/* s81b */,E(_14a/* s81t */).b, _147/* s81e */);});
        },
        _144/* s81g */ = function(_14b/* s81x */){
          var _14c/* s81y */ = E(_13W/* s812 */);
          if(!_14c/* s81y */._){
            return new F(function(){return A2(_141/* s81b */,_14b/* s81x */, _147/* s81e */);});
          }else{
            var _14d/* s82g */ = function(_/* EXTERNAL */){
              var _14e/* s81C */ = E(_Xw/* System.Random.theStdGen */),
              _14f/* s81E */ = mMV/* EXTERNAL */(_14e/* s81C */, _YM/* System.Random.$fRandomBool2 */);
              return new T(function(){
                var _14g/* s82e */ = function(_14h/* s81M */){
                  var _14i/* s81Q */ = function(_14j/* s81R */, _14k/* s81S */, _14l/* s81T */){
                    var _14m/* s81U */ = E(_14j/* s81R */);
                    if(!_14m/* s81U */._){
                      return new F(function(){return A1(_14l/* s81T */,new T2(0,_7/* GHC.Tuple.() */,_14k/* s81S */));});
                    }else{
                      var _14n/* s82d */ = function(_/* EXTERNAL */){
                        var _14o/* s81Z */ = mMV/* EXTERNAL */(_14e/* s81C */, _YM/* System.Random.$fRandomBool2 */);
                        return new T(function(){
                          return B(A(_wJ/* Core.Ease.$wforceTo */,[E(_14m/* s81U */.a).c, E(_14o/* s81Z */), _14k/* s81S */, function(_14p/* s827 */){
                            return new F(function(){return _14i/* s81Q */(_14m/* s81U */.b, E(_14p/* s827 */).b, _14l/* s81T */);});
                          }]));
                        });
                      };
                      return new T1(0,_14n/* s82d */);
                    }
                  };
                  return new F(function(){return _14i/* s81Q */(_14c/* s81y */.b, E(_14h/* s81M */).b, _149/* s81f */);});
                };
                return B(A(_wJ/* Core.Ease.$wforceTo */,[E(_14c/* s81y */.a).c, E(_14f/* s81E */), _14b/* s81x */, _14g/* s82e */]));
              });
            };
            return new T1(0,_14d/* s82g */);
          }
        },
        _14q/* s82h */ = function(_14r/* s82i */, _14s/* s82j */){
          return new F(function(){return _144/* s81g */(_14r/* s82i */);});
        },
        _14t/* s82B */ = function(_/* EXTERNAL */){
          var _14u/* s82l */ = nMV/* EXTERNAL */(_13g/* Motion.Change.lvl13 */);
          return new T(function(){
            var _14v/* s82x */ = new T(function(){
              var _14w/* s82v */ = new T(function(){
                return B(_pg/* Control.Monad.Skeleton.bone */(new T3(7,new T2(0,new T(function(){
                  return B(_uj/* Core.Ease.opLift */(_in/* GHC.Float.divideDouble */, new T2(2,_13Z/* s819 */,_2E/* GHC.Base.id */), _13o/* Motion.Change.lvl7 */));
                }),new T(function(){
                  return B(_uj/* Core.Ease.opLift */(_in/* GHC.Float.divideDouble */, new T2(2,_13Z/* s819 */,_2E/* GHC.Base.id */), _13o/* Motion.Change.lvl7 */));
                })),new T(function(){
                  return B(_13D/* s80n */(_13W/* s812 */, _13d/* Motion.Change.lvl10 */));
                }),_7/* GHC.Tuple.() */)));
              });
              return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,_13m/* Motion.Change.lvl6 */,_14w/* s82v */,_7/* GHC.Tuple.() */)));
            });
            return B(A1(_13S/* s80Z */,new T2(0,new T2(0,_14v/* s82x */,_14q/* s82h */),_13V/* s811 */.b)));
          });
        };
        return new T1(0,_14t/* s82B */);
      };
      return new T1(0,_13X/* s82D */);
    };
    return new F(function(){return A1(_13C/* s80m */,_13T/* s82E */);});
  };
  return E(_13R/* s82F */);
},
_14x/* lvl37 */ = 0.1,
_14y/* lvl38 */ = new T1(0,_14x/* Motion.Main.lvl37 */),
_14z/* lvl39 */ = new T4(0,_14y/* Motion.Main.lvl38 */,_II/* Motion.Main.lvl30 */,_II/* Motion.Main.lvl30 */,_u4/* Motion.Main.lvl9 */),
_14A/* lvl40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Change"));
}),
_14B/* lvl41 */ = new T(function(){
  return B(_AB/* Motion.Main.$wconsView */(_14z/* Motion.Main.lvl39 */, _13z/* Motion.Change.changeMot1 */, _14A/* Motion.Main.lvl40 */));
}),
_14C/* lvl42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("height"));
}),
_14D/* lvl43 */ = 1,
_14E/* lvl44 */ = new T1(1,_6/* GHC.Types.[] */),
_14F/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.scale(x,y);})");
}),
_14G/* f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,rad){ctx.rotate(rad);})");
}),
_14H/* f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.translate(x,y);})");
}),
_14I/* f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})");
}),
_14J/* render2 */ = function(_14K/*  scbK */, _14L/*  scbL */, _/* EXTERNAL */){
  while(1){
    var _14M/*  render2 */ = B((function(_14N/* scbK */, _14O/* scbL */, _/* EXTERNAL */){
      var _14P/* scbN */ = B(_fo/* Control.Monad.Skeleton.debone */(_14N/* scbK */));
      if(!_14P/* scbN */._){
        return _14P/* scbN */.a;
      }else{
        var _14Q/* scbQ */ = _14P/* scbN */.b,
        _14R/* scbR */ = E(_14P/* scbN */.a);
        switch(_14R/* scbR */._){
          case 0:
            var _14S/* scbU */ = B(A2(_14R/* scbR */.a,_14O/* scbL */, _/* EXTERNAL */)),
            _14T/*   scbL */ = _14O/* scbL */;
            _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14R/* scbR */.b));
            _14L/*  scbL */ = _14T/*   scbL */;
            return __continue/* EXTERNAL */;
          case 1:
            var _14U/* scbZ */ = B(A1(_14R/* scbR */.a,_/* EXTERNAL */)),
            _14T/*   scbL */ = _14O/* scbL */;
            _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14U/* scbZ */));
            _14L/*  scbL */ = _14T/*   scbL */;
            return __continue/* EXTERNAL */;
          case 2:
            var _14T/*   scbL */ = _14O/* scbL */;
            _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14R/* scbR */.b));
            _14L/*  scbL */ = _14T/*   scbL */;
            return __continue/* EXTERNAL */;
          case 3:
            var _14V/* scc9 */ = B(_14J/* Core.Render.Internal.render2 */(_14R/* scbR */.b, _14R/* scbR */.a, _/* EXTERNAL */)),
            _14T/*   scbL */ = _14O/* scbL */;
            _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14R/* scbR */.c));
            _14L/*  scbL */ = _14T/*   scbL */;
            return __continue/* EXTERNAL */;
          case 4:
            var _14W/* scck */ = _14R/* scbR */.h,
            _14X/* sccl */ = function(_14Y/* sccm */, _/* EXTERNAL */){
              var _14Z/* scdq */ = function(_150/* scco */, _/* EXTERNAL */){
                var _151/* scdp */ = function(_152/* sccq */, _/* EXTERNAL */){
                  var _153/* scdo */ = function(_154/* sccs */, _/* EXTERNAL */){
                    var _155/* scdn */ = function(_156/* sccu */, _/* EXTERNAL */){
                      return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_14R/* scbR */.f, function(_157/* sccw */, _/* EXTERNAL */){
                        var _158/* sccy */ = E(_14O/* scbL */),
                        _159/* sccD */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _158/* sccy */),
                        _15a/* scda */ = __apply/* EXTERNAL */(E(_14I/* Core.Render.Internal.f4 */), new T2(1,E(_157/* sccw */),new T2(1,E(_156/* sccu */),new T2(1,E(_154/* sccs */),new T2(1,E(_152/* sccq */),new T2(1,E(_150/* scco */),new T2(1,E(_14Y/* sccm */),new T2(1,_158/* sccy */,_6/* GHC.Types.[] */)))))))),
                        _15b/* scdd */ = B(_14J/* Core.Render.Internal.render2 */(_14R/* scbR */.g, _158/* sccy */, _/* EXTERNAL */)),
                        _15c/* scdj */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), _158/* sccy */);
                        return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
                      }, _/* EXTERNAL */);});
                    };
                    return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_14R/* scbR */.e, _155/* scdn */, _/* EXTERNAL */);});
                  };
                  return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_14R/* scbR */.d, _153/* scdo */, _/* EXTERNAL */);});
                };
                return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_14R/* scbR */.c, _151/* scdp */, _/* EXTERNAL */);});
              };
              return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_14R/* scbR */.b, _14Z/* scdq */, _/* EXTERNAL */);});
            },
            _15d/* scdr */ = E(_14R/* scbR */.a);
            switch(_15d/* scdr */._){
              case 0:
                var _15e/* scdt */ = B(_14X/* sccl */(_15d/* scdr */.a, _/* EXTERNAL */)),
                _14T/*   scbL */ = _14O/* scbL */;
                _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14W/* scck */));
                _14L/*  scbL */ = _14T/*   scbL */;
                return __continue/* EXTERNAL */;
              case 1:
                var _15f/* scdy */ = B(A1(_15d/* scdr */.a,_/* EXTERNAL */)),
                _15g/* scdB */ = B(_14X/* sccl */(_15f/* scdy */, _/* EXTERNAL */)),
                _14T/*   scbL */ = _14O/* scbL */;
                _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14W/* scck */));
                _14L/*  scbL */ = _14T/*   scbL */;
                return __continue/* EXTERNAL */;
              case 2:
                var _15h/* scdN */ = rMV/* EXTERNAL */(E(E(_15d/* scdr */.a).c)),
                _15i/* scdQ */ = E(_15h/* scdN */);
                if(!_15i/* scdQ */._){
                  var _15j/* scdU */ = new T(function(){
                    return B(A1(_15d/* scdr */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_15i/* scdQ */.a));
                    })));
                  },1),
                  _15k/* scdV */ = B(_14X/* sccl */(_15j/* scdU */, _/* EXTERNAL */)),
                  _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14W/* scck */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14W/* scck */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _15l/* sce9 */ = rMV/* EXTERNAL */(E(E(_15d/* scdr */.a).c)),
                _15m/* scec */ = E(_15l/* sce9 */);
                if(!_15m/* scec */._){
                  var _15n/* scei */ = B(A2(_15d/* scdr */.b,E(_15m/* scec */.a).a, _/* EXTERNAL */)),
                  _15o/* scel */ = B(_14X/* sccl */(_15n/* scei */, _/* EXTERNAL */)),
                  _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14W/* scck */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14W/* scck */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 5:
            var _15p/* scet */ = _14R/* scbR */.c,
            _15q/* sceu */ = E(_14R/* scbR */.a),
            _15r/* scex */ = function(_15s/* scey */, _/* EXTERNAL */){
              return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_15q/* sceu */.b, function(_15t/* sceA */, _/* EXTERNAL */){
                var _15u/* sceC */ = E(_14O/* scbL */),
                _15v/* sceH */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _15u/* sceC */),
                _15w/* sceV */ = __app3/* EXTERNAL */(E(_14H/* Core.Render.Internal.f3 */), _15u/* sceC */, E(_15s/* scey */), E(_15t/* sceA */)),
                _15x/* sceY */ = B(_14J/* Core.Render.Internal.render2 */(_14R/* scbR */.b, _15u/* sceC */, _/* EXTERNAL */)),
                _15y/* scf4 */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), _15u/* sceC */);
                return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _15z/* scf8 */ = E(_15q/* sceu */.a);
            switch(_15z/* scf8 */._){
              case 0:
                var _15A/* scfa */ = B(_15r/* scex */(_15z/* scf8 */.a, _/* EXTERNAL */)),
                _14T/*   scbL */ = _14O/* scbL */;
                _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15p/* scet */));
                _14L/*  scbL */ = _14T/*   scbL */;
                return __continue/* EXTERNAL */;
              case 1:
                var _15B/* scff */ = B(A1(_15z/* scf8 */.a,_/* EXTERNAL */)),
                _15C/* scfi */ = B(_15r/* scex */(_15B/* scff */, _/* EXTERNAL */)),
                _14T/*   scbL */ = _14O/* scbL */;
                _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15p/* scet */));
                _14L/*  scbL */ = _14T/*   scbL */;
                return __continue/* EXTERNAL */;
              case 2:
                var _15D/* scfu */ = rMV/* EXTERNAL */(E(E(_15z/* scf8 */.a).c)),
                _15E/* scfx */ = E(_15D/* scfu */);
                if(!_15E/* scfx */._){
                  var _15F/* scfB */ = new T(function(){
                    return B(A1(_15z/* scf8 */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_15E/* scfx */.a));
                    })));
                  },1),
                  _15G/* scfC */ = B(_15r/* scex */(_15F/* scfB */, _/* EXTERNAL */)),
                  _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15p/* scet */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15p/* scet */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _15H/* scfQ */ = rMV/* EXTERNAL */(E(E(_15z/* scf8 */.a).c)),
                _15I/* scfT */ = E(_15H/* scfQ */);
                if(!_15I/* scfT */._){
                  var _15J/* scfZ */ = B(A2(_15z/* scf8 */.b,E(_15I/* scfT */.a).a, _/* EXTERNAL */)),
                  _15K/* scg2 */ = B(_15r/* scex */(_15J/* scfZ */, _/* EXTERNAL */)),
                  _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15p/* scet */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15p/* scet */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 6:
            var _15L/* scga */ = _14R/* scbR */.c,
            _15M/* scgb */ = function(_15N/* scgc */, _/* EXTERNAL */){
              var _15O/* scge */ = E(_14O/* scbL */),
              _15P/* scgj */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _15O/* scge */),
              _15Q/* scgt */ = __app2/* EXTERNAL */(E(_14G/* Core.Render.Internal.f2 */), _15O/* scge */, E(_15N/* scgc */)),
              _15R/* scgw */ = B(_14J/* Core.Render.Internal.render2 */(_14R/* scbR */.b, _15O/* scge */, _/* EXTERNAL */)),
              _15S/* scgC */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), _15O/* scge */);
              return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
            },
            _15T/* scgF */ = E(_14R/* scbR */.a);
            switch(_15T/* scgF */._){
              case 0:
                var _15U/* scgH */ = B(_15M/* scgb */(_15T/* scgF */.a, _/* EXTERNAL */)),
                _14T/*   scbL */ = _14O/* scbL */;
                _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15L/* scga */));
                _14L/*  scbL */ = _14T/*   scbL */;
                return __continue/* EXTERNAL */;
              case 1:
                var _15V/* scgM */ = B(A1(_15T/* scgF */.a,_/* EXTERNAL */)),
                _15W/* scgP */ = B(_15M/* scgb */(_15V/* scgM */, _/* EXTERNAL */)),
                _14T/*   scbL */ = _14O/* scbL */;
                _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15L/* scga */));
                _14L/*  scbL */ = _14T/*   scbL */;
                return __continue/* EXTERNAL */;
              case 2:
                var _15X/* sch1 */ = rMV/* EXTERNAL */(E(E(_15T/* scgF */.a).c)),
                _15Y/* sch4 */ = E(_15X/* sch1 */);
                if(!_15Y/* sch4 */._){
                  var _15Z/* sch8 */ = new T(function(){
                    return B(A1(_15T/* scgF */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_15Y/* sch4 */.a));
                    })));
                  },1),
                  _160/* sch9 */ = B(_15M/* scgb */(_15Z/* sch8 */, _/* EXTERNAL */)),
                  _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15L/* scga */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15L/* scga */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _161/* schn */ = rMV/* EXTERNAL */(E(E(_15T/* scgF */.a).c)),
                _162/* schq */ = E(_161/* schn */);
                if(!_162/* schq */._){
                  var _163/* schw */ = B(A2(_15T/* scgF */.b,E(_162/* schq */.a).a, _/* EXTERNAL */)),
                  _164/* schz */ = B(_15M/* scgb */(_163/* schw */, _/* EXTERNAL */)),
                  _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15L/* scga */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_15L/* scga */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 7:
            var _165/* schH */ = _14R/* scbR */.c,
            _166/* schI */ = E(_14R/* scbR */.a),
            _167/* schL */ = function(_168/* schM */, _/* EXTERNAL */){
              return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_166/* schI */.b, function(_169/* schO */, _/* EXTERNAL */){
                var _16a/* schQ */ = E(_14O/* scbL */),
                _16b/* schV */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _16a/* schQ */),
                _16c/* sci9 */ = __app3/* EXTERNAL */(E(_14F/* Core.Render.Internal.f1 */), _16a/* schQ */, E(_168/* schM */), E(_169/* schO */)),
                _16d/* scic */ = B(_14J/* Core.Render.Internal.render2 */(_14R/* scbR */.b, _16a/* schQ */, _/* EXTERNAL */)),
                _16e/* scii */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), _16a/* schQ */);
                return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _16f/* scim */ = E(_166/* schI */.a);
            switch(_16f/* scim */._){
              case 0:
                var _16g/* scio */ = B(_167/* schL */(_16f/* scim */.a, _/* EXTERNAL */)),
                _14T/*   scbL */ = _14O/* scbL */;
                _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_165/* schH */));
                _14L/*  scbL */ = _14T/*   scbL */;
                return __continue/* EXTERNAL */;
              case 1:
                var _16h/* scit */ = B(A1(_16f/* scim */.a,_/* EXTERNAL */)),
                _16i/* sciw */ = B(_167/* schL */(_16h/* scit */, _/* EXTERNAL */)),
                _14T/*   scbL */ = _14O/* scbL */;
                _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_165/* schH */));
                _14L/*  scbL */ = _14T/*   scbL */;
                return __continue/* EXTERNAL */;
              case 2:
                var _16j/* sciI */ = rMV/* EXTERNAL */(E(E(_16f/* scim */.a).c)),
                _16k/* sciL */ = E(_16j/* sciI */);
                if(!_16k/* sciL */._){
                  var _16l/* sciP */ = new T(function(){
                    return B(A1(_16f/* scim */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_16k/* sciL */.a));
                    })));
                  },1),
                  _16m/* sciQ */ = B(_167/* schL */(_16l/* sciP */, _/* EXTERNAL */)),
                  _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_165/* schH */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_165/* schH */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _16n/* scj4 */ = rMV/* EXTERNAL */(E(E(_16f/* scim */.a).c)),
                _16o/* scj7 */ = E(_16n/* scj4 */);
                if(!_16o/* scj7 */._){
                  var _16p/* scjd */ = B(A2(_16f/* scim */.b,E(_16o/* scj7 */.a).a, _/* EXTERNAL */)),
                  _16q/* scjg */ = B(_167/* schL */(_16p/* scjd */, _/* EXTERNAL */)),
                  _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_165/* schH */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _14T/*   scbL */ = _14O/* scbL */;
                  _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_165/* schH */));
                  _14L/*  scbL */ = _14T/*   scbL */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          default:
            var _16r/* scjp */ = B(_14J/* Core.Render.Internal.render2 */(_14R/* scbR */.a, _14O/* scbL */, _/* EXTERNAL */)),
            _14T/*   scbL */ = _14O/* scbL */;
            _14K/*  scbK */ = B(A1(_14Q/* scbQ */,_14R/* scbR */.c));
            _14L/*  scbL */ = _14T/*   scbL */;
            return __continue/* EXTERNAL */;
        }
      }
    })(_14K/*  scbK */, _14L/*  scbL */, _/* EXTERNAL */));
    if(_14M/*  render2 */!=__continue/* EXTERNAL */){
      return _14M/*  render2 */;
    }
  }
},
_16s/* a12 */ = new T1(0,_/* EXTERNAL */),
_16t/* a13 */ = new T1(0,_6/* GHC.Types.[] */),
_16u/* a14 */ = new T2(0,E(_16t/* Motion.Main.a13 */),E(_16s/* Motion.Main.a12 */)),
_16v/* pad */ = 40,
_16w/* lvl1 */ = new T1(0,_16v/* Motion.Main.pad */),
_16x/* rendering1 */ = function(_16y/* sfBX */){
  return E(E(_16y/* sfBX */).b);
},
_16z/* renderContents_go */ = function(_16A/* saIg */, _16B/* saIh */){
  var _16C/* saIi */ = E(_16A/* saIg */);
  if(!_16C/* saIi */._){
    return E(_16u/* Motion.Main.a14 */);
  }else{
    var _16D/* saIl */ = E(_16B/* saIh */);
    if(!_16D/* saIl */._){
      return E(_16u/* Motion.Main.a14 */);
    }else{
      var _16E/* saIy */ = B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_16w/* Motion.Main.lvl1 */,new T1(0,new T(function(){
        return 40+240*E(_16C/* saIi */.a);
      }))),new T(function(){
        return B(_16x/* Core.View.rendering1 */(_16D/* saIl */.a));
      }),_7/* GHC.Tuple.() */))),
      _16F/* saIB */ = new T(function(){
        return B(_16z/* Motion.Main.renderContents_go */(_16C/* saIi */.b, _16D/* saIl */.b));
      }),
      _16G/* saIM */ = function(_16H/* saIC */){
        var _16I/* saID */ = E(_16F/* saIB */);
        return new T2(0,E(_16I/* saID */.a),E(new T2(2,_16I/* saID */.b,new T1(1,function(_16J/* saIG */){
          return new T2(0,E(new T1(0,new T2(1,_16H/* saIC */,_16J/* saIG */))),E(_16s/* Motion.Main.a12 */));
        }))));
      };
      return new T2(0,E(_16E/* saIy */.a),E(new T2(2,_16E/* saIy */.b,new T1(1,_16G/* saIM */))));
    }
  }
},
_16K/* renderContents1 */ = function(_16L/* saIP */){
  return new F(function(){return _p8/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
    return B(_16z/* Motion.Main.renderContents_go */(_HQ/* Core.Util.iforM1 */, _16L/* saIP */));
  }));});
},
_16M/* launch1 */ = function(_16N/* saKb */, _16O/* saKc */){
  var _16P/* saKd */ = function(_16Q/* saKe */, _/* EXTERNAL */){
    var _16R/* saKg */ = E(_16N/* saKb */),
    _16S/* saKm */ = __app1/* EXTERNAL */(E(_ib/* Haste.Graphics.Canvas.buffer_f1 */), _16R/* saKg */.b);
    return new F(function(){return _14J/* Core.Render.Internal.render2 */(B(_16K/* Motion.Main.renderContents1 */(_16Q/* saKe */)), _16R/* saKg */.a, _/* EXTERNAL */);});
  },
  _16T/* saKr */ = new T(function(){
    return B(A1(_Fz/* Motion.Main.lvl28 */,_16O/* saKc */));
  }),
  _16U/* saM8 */ = function(_16V/* saKs */){
    var _16W/* saM7 */ = function(_16X/* saKt */){
      var _16Y/* saKu */ = E(_16X/* saKt */),
      _16Z/* saM6 */ = function(_170/* saKx */){
        var _171/* saKy */ = E(_170/* saKx */),
        _172/* saM5 */ = function(_173/* saKB */){
          var _174/* saKC */ = E(_173/* saKB */),
          _175/* saM4 */ = function(_176/* saKF */){
            var _177/* saKG */ = E(_176/* saKF */),
            _178/* saKM */ = new T2(1,_16Y/* saKu */.a,new T2(1,_171/* saKy */.a,new T2(1,_174/* saKC */.a,new T2(1,_177/* saKG */.a,_6/* GHC.Types.[] */)))),
            _179/* saM3 */ = function(_/* EXTERNAL */){
              var _17a/* saL1 */ = jsShow/* EXTERNAL */(40+B(_eT/* GHC.List.$wlenAcc */(_178/* saKM */, 0))*240),
              _17b/* saLd */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), E(_16N/* saKb */).b, toJSStr/* EXTERNAL */(E(_14C/* Motion.Main.lvl42 */)), toJSStr/* EXTERNAL */(fromJSStr/* EXTERNAL */(_17a/* saL1 */))),
              _17c/* saM1 */ = function(_/* EXTERNAL */){
                var _17d/* saLi */ = nMV/* EXTERNAL */(new T2(0,_178/* saKM */,_6/* GHC.Types.[] */));
                return new T(function(){
                  var _17e/* saLm */ = new T(function(){
                    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _17d/* saLi */, _eY/* Motion.Main.a22 */));
                  }),
                  _17f/* saLo */ = function(_17g/* saLu */){
                    return new F(function(){return _17h/* saLr */(E(_17g/* saLu */).b);});
                  },
                  _17i/* saLp */ = function(_17j/* saLy */){
                    return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_14D/* Motion.Main.lvl43 */, E(_17j/* saLy */).b, _17f/* saLo */);});
                  },
                  _17k/* saLq */ = function(_17l/* saLC */){
                    var _17m/* saLD */ = E(_17l/* saLC */);
                    return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[B(_16K/* Motion.Main.renderContents1 */(_17m/* saLD */.a)), _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _17m/* saLD */.b, _17i/* saLp */]);});
                  },
                  _17h/* saLr */ = function(_17n/* saLH */){
                    return new F(function(){return A2(_17e/* saLm */,_17n/* saLH */, _17k/* saLq */);});
                  },
                  _17o/* saLX */ = function(_17p/* saLI */){
                    var _17q/* saLL */ = E(_17p/* saLI */).b,
                    _17r/* saLW */ = function(_/* EXTERNAL */){
                      var _17s/* saLN */ = nMV/* EXTERNAL */(_14E/* Motion.Main.lvl44 */);
                      return new T1(1,new T2(1,new T(function(){
                        return B(A1(_16V/* saKs */,new T2(0,_7/* GHC.Tuple.() */,_17q/* saLL */)));
                      }),new T2(1,new T(function(){
                        return B(_17h/* saLr */(_17q/* saLL */));
                      }),_6/* GHC.Types.[] */)));
                    };
                    return new T1(0,_17r/* saLW */);
                  };
                  return new T1(0,B(_e8/* Core.Front.Internal.$wa */(_17d/* saLi */, _16P/* saKd */, _177/* saKG */.b, _17o/* saLX */)));
                });
              };
              return new T1(0,_17c/* saM1 */);
            };
            return new T1(0,_179/* saM3 */);
          };
          return new F(function(){return A2(_14B/* Motion.Main.lvl41 */,_174/* saKC */.b, _175/* saM4 */);});
        };
        return new F(function(){return A2(_Yo/* Motion.Main.lvl36 */,_171/* saKy */.b, _172/* saM5 */);});
      };
      return new F(function(){return A2(_IL/* Motion.Main.lvl33 */,_16Y/* saKu */.b, _16Z/* saM6 */);});
    };
    return new F(function(){return A1(_16T/* saKr */,_16W/* saM7 */);});
  };
  return E(_16U/* saM8 */);
},
_17t/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Canvas not found!"));
}),
_17u/* main2 */ = new T(function(){
  return B(err/* EXTERNAL */(_17t/* Main.lvl */));
}),
_17v/* main3 */ = "canvas",
_17w/* start_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(Util.onload)");
}),
_17x/* main1 */ = function(_/* EXTERNAL */){
  var _17y/* skrQ */ = __app1/* EXTERNAL */(E(_17w/* Core.Front.Internal.start_f1 */), E(_48/* Haste.Prim.Any.jsNull */)),
  _17z/* skrT */ = B(A3(_e1/* Haste.DOM.JSString.elemById */,_2G/* Control.Monad.IO.Class.$fMonadIOIO */, _17v/* Main.main3 */, _/* EXTERNAL */)),
  _17A/* skrW */ = E(_17z/* skrT */);
  if(!_17A/* skrW */._){
    return E(_17u/* Main.main2 */);
  }else{
    var _17B/* skrZ */ = E(_17A/* skrW */.a),
    _17C/* sks4 */ = __app1/* EXTERNAL */(E(_1/* Haste.Graphics.Canvas.$fFromAnyCanvas_f2 */), _17B/* skrZ */);
    if(!_17C/* sks4 */){
      return E(_17u/* Main.main2 */);
    }else{
      var _17D/* sksc */ = __app1/* EXTERNAL */(E(_0/* Haste.Graphics.Canvas.$fFromAnyCanvas_f1 */), _17B/* skrZ */),
      _17E/* skse */ = _17D/* sksc */,
      _17F/* sksj */ = new T(function(){
        return new T1(0,B(_d7/* Core.World.Internal.$wa5 */(function(_17G/* B1 */){
          return new F(function(){return _16M/* Motion.Main.launch1 */(new T2(0,_17E/* skse */,_17B/* skrZ */), _17G/* B1 */);});
        }, _2I/* Haste.Concurrent.Monad.forkIO1 */)));
      });
      return new F(function(){return _e/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(_17F/* sksj */, _6/* GHC.Types.[] */, _/* EXTERNAL */);});
    }
  }
},
_17H/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _17x/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_17H, [0]));};window.onload = hasteMain;