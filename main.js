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
_4D/* $fMonadEventWorld2 */ = function(_4E/* sbYf */){
  var _4F/* sbYg */ = E(_4E/* sbYf */);
  return new T0(2);
},
_4G/* $fMonadConcWorld1 */ = function(_4H/* sbYj */, _4I/* sbYk */, _4J/* sbYl */){
  return new T1(1,new T2(1,new T(function(){
    return B(A1(_4J/* sbYl */,new T2(0,_7/* GHC.Tuple.() */,_4I/* sbYk */)));
  }),new T2(1,new T(function(){
    return B(A2(_4H/* sbYj */,_4I/* sbYk */, _4D/* Core.World.Internal.$fMonadEventWorld2 */));
  }),_6/* GHC.Types.[] */)));
},
_4K/* $fApplicativeWorld1 */ = function(_4L/* sbRO */, _4M/* sbRP */, _4N/* sbRQ */){
  var _4O/* sbRR */ = new T(function(){
    return B(A1(_4L/* sbRO */,_4N/* sbRQ */));
  }),
  _4P/* sbS4 */ = function(_4Q/* sbRS */){
    var _4R/* sbS3 */ = function(_4S/* sbRT */){
      var _4T/* sbRU */ = E(_4S/* sbRT */);
      return new F(function(){return A2(_4M/* sbRP */,_4T/* sbRU */.b, function(_4U/* sbRX */){
        return new F(function(){return A1(_4Q/* sbRS */,new T2(0,_4T/* sbRU */.a,E(_4U/* sbRX */).b));});
      });});
    };
    return new F(function(){return A1(_4O/* sbRR */,_4R/* sbS3 */);});
  };
  return E(_4P/* sbS4 */);
},
_4V/* $fApplicativeWorld2 */ = function(_4W/* sbS5 */, _4X/* sbS6 */, _4Y/* sbS7 */){
  var _4Z/* sbS8 */ = new T(function(){
    return B(A1(_4W/* sbS5 */,_4Y/* sbS7 */));
  }),
  _50/* sbSk */ = function(_51/* sbS9 */){
    var _52/* sbSa */ = function(_53/* sbSb */){
      return new F(function(){return A1(_51/* sbS9 */,E(_53/* sbSb */));});
    };
    return new F(function(){return A1(_4Z/* sbS8 */,function(_54/* sbSf */){
      return new F(function(){return A2(_4X/* sbS6 */,E(_54/* sbSf */).b, _52/* sbSa */);});
    });});
  };
  return E(_50/* sbSk */);
},
_55/* $fApplicativeWorld3 */ = function(_56/* sbSl */, _57/* sbSm */, _58/* sbSn */){
  var _59/* sbSo */ = new T(function(){
    return B(A1(_56/* sbSl */,_58/* sbSn */));
  }),
  _5a/* sbSC */ = function(_5b/* sbSp */){
    var _5c/* sbSB */ = function(_5d/* sbSq */){
      var _5e/* sbSr */ = E(_5d/* sbSq */),
      _5f/* sbSA */ = function(_5g/* sbSu */){
        var _5h/* sbSv */ = E(_5g/* sbSu */);
        return new F(function(){return A1(_5b/* sbSp */,new T2(0,new T(function(){
          return B(A1(_5e/* sbSr */.a,_5h/* sbSv */.a));
        }),_5h/* sbSv */.b));});
      };
      return new F(function(){return A2(_57/* sbSm */,_5e/* sbSr */.b, _5f/* sbSA */);});
    };
    return new F(function(){return A1(_59/* sbSo */,_5c/* sbSB */);});
  };
  return E(_5a/* sbSC */);
},
_5i/* $fFunctorWorld1 */ = function(_5j/* sbUs */, _5k/* sbUt */, _5l/* sbUu */){
  var _5m/* sbUv */ = new T(function(){
    return B(A1(_5k/* sbUt */,_5l/* sbUu */));
  }),
  _5n/* sbUD */ = function(_5o/* sbUw */){
    var _5p/* sbUC */ = function(_5q/* sbUx */){
      return new F(function(){return A1(_5o/* sbUw */,new T(function(){
        return new T2(0,_5j/* sbUs */,E(_5q/* sbUx */).b);
      }));});
    };
    return new F(function(){return A1(_5m/* sbUv */,_5p/* sbUC */);});
  };
  return E(_5n/* sbUD */);
},
_5r/* $fFunctorWorld2 */ = function(_5s/* sbUf */, _5t/* sbUg */, _5u/* sbUh */){
  var _5v/* sbUi */ = new T(function(){
    return B(A1(_5t/* sbUg */,_5u/* sbUh */));
  }),
  _5w/* sbUr */ = function(_5x/* sbUj */){
    var _5y/* sbUq */ = function(_5z/* sbUk */){
      var _5A/* sbUp */ = new T(function(){
        var _5B/* sbUl */ = E(_5z/* sbUk */);
        return new T2(0,new T(function(){
          return B(A1(_5s/* sbUf */,_5B/* sbUl */.a));
        }),_5B/* sbUl */.b);
      });
      return new F(function(){return A1(_5x/* sbUj */,_5A/* sbUp */);});
    };
    return new F(function(){return A1(_5v/* sbUi */,_5y/* sbUq */);});
  };
  return E(_5w/* sbUr */);
},
_5C/* $fFunctorWorld */ = new T2(0,_5r/* Core.World.Internal.$fFunctorWorld2 */,_5i/* Core.World.Internal.$fFunctorWorld1 */),
_5D/* $fMonadWorld2 */ = function(_5E/* sbQU */, _5F/* sbQV */, _5G/* sbQW */){
  return new F(function(){return A1(_5G/* sbQW */,new T2(0,_5E/* sbQU */,_5F/* sbQV */));});
},
_5H/* $fApplicativeWorld */ = new T5(0,_5C/* Core.World.Internal.$fFunctorWorld */,_5D/* Core.World.Internal.$fMonadWorld2 */,_55/* Core.World.Internal.$fApplicativeWorld3 */,_4V/* Core.World.Internal.$fApplicativeWorld2 */,_4K/* Core.World.Internal.$fApplicativeWorld1 */),
_5I/* $fMonadWorld1 */ = function(_5J/* sbRM */, _5K/* sbRN */){
  return new F(function(){return err/* EXTERNAL */(_5J/* sbRM */);});
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
_79/* a17 */ = function(_7a/* sbRn */, _7b/* sbRo */, _7c/* sbRp */){
  var _7d/* sbRq */ = new T(function(){
    return B(A1(_7b/* sbRo */,_7c/* sbRp */));
  }),
  _7e/* sbRy */ = function(_7f/* sbRr */){
    var _7g/* sbRx */ = function(_7h/* sbRs */){
      return new F(function(){return A1(_7f/* sbRr */,new T(function(){
        return new T2(0,_7a/* sbRn */,E(_7h/* sbRs */).b);
      }));});
    };
    return new F(function(){return A1(_7d/* sbRq */,_7g/* sbRx */);});
  };
  return E(_7e/* sbRy */);
},
_7i/* a18 */ = function(_7j/* sbRz */, _7k/* sbRA */, _7l/* sbRB */){
  var _7m/* sbRC */ = new T(function(){
    return B(A1(_7k/* sbRA */,_7l/* sbRB */));
  }),
  _7n/* sbRL */ = function(_7o/* sbRD */){
    var _7p/* sbRK */ = function(_7q/* sbRE */){
      var _7r/* sbRJ */ = new T(function(){
        var _7s/* sbRF */ = E(_7q/* sbRE */);
        return new T2(0,new T(function(){
          return B(A1(_7j/* sbRz */,_7s/* sbRF */.a));
        }),_7s/* sbRF */.b);
      });
      return new F(function(){return A1(_7o/* sbRD */,_7r/* sbRJ */);});
    };
    return new F(function(){return A1(_7m/* sbRC */,_7p/* sbRK */);});
  };
  return E(_7n/* sbRL */);
},
_7t/* $fMonadWorld_$s$fFunctorStateT */ = new T2(0,_7i/* Core.World.Internal.a18 */,_79/* Core.World.Internal.a17 */),
_7u/* a22 */ = function(_7v/* sbSD */, _7w/* sbSE */, _7x/* sbSF */){
  var _7y/* sbSG */ = new T(function(){
    return B(A1(_7v/* sbSD */,_7x/* sbSF */));
  }),
  _7z/* sbSU */ = function(_7A/* sbSH */){
    var _7B/* sbST */ = function(_7C/* sbSI */){
      var _7D/* sbSJ */ = E(_7C/* sbSI */),
      _7E/* sbSS */ = function(_7F/* sbSM */){
        var _7G/* sbSN */ = E(_7F/* sbSM */);
        return new F(function(){return A1(_7A/* sbSH */,new T2(0,new T(function(){
          return B(A1(_7D/* sbSJ */.a,_7G/* sbSN */.a));
        }),_7G/* sbSN */.b));});
      };
      return new F(function(){return A2(_7w/* sbSE */,_7D/* sbSJ */.b, _7E/* sbSS */);});
    };
    return new F(function(){return A1(_7y/* sbSG */,_7B/* sbST */);});
  };
  return E(_7z/* sbSU */);
},
_7H/* a23 */ = function(_7I/* sbSV */, _7J/* sbSW */, _7K/* sbSX */){
  var _7L/* sbSY */ = new T(function(){
    return B(A1(_7I/* sbSV */,_7K/* sbSX */));
  }),
  _7M/* sbTa */ = function(_7N/* sbSZ */){
    var _7O/* sbT0 */ = function(_7P/* sbT1 */){
      return new F(function(){return A1(_7N/* sbSZ */,E(_7P/* sbT1 */));});
    };
    return new F(function(){return A1(_7L/* sbSY */,function(_7Q/* sbT5 */){
      return new F(function(){return A2(_7J/* sbSW */,E(_7Q/* sbT5 */).b, _7O/* sbT0 */);});
    });});
  };
  return E(_7M/* sbTa */);
},
_7R/* a24 */ = function(_7S/* sbTb */, _7T/* sbTc */, _7U/* sbTd */){
  var _7V/* sbTe */ = new T(function(){
    return B(A1(_7S/* sbTb */,_7U/* sbTd */));
  }),
  _7W/* sbTr */ = function(_7X/* sbTf */){
    var _7Y/* sbTq */ = function(_7Z/* sbTg */){
      var _80/* sbTh */ = E(_7Z/* sbTg */);
      return new F(function(){return A2(_7T/* sbTc */,_80/* sbTh */.b, function(_81/* sbTk */){
        return new F(function(){return A1(_7X/* sbTf */,new T2(0,_80/* sbTh */.a,E(_81/* sbTk */).b));});
      });});
    };
    return new F(function(){return A1(_7V/* sbTe */,_7Y/* sbTq */);});
  };
  return E(_7W/* sbTr */);
},
_82/* $fMonadWorld_$s$fApplicativeStateT */ = new T5(0,_7t/* Core.World.Internal.$fMonadWorld_$s$fFunctorStateT */,_5D/* Core.World.Internal.$fMonadWorld2 */,_7u/* Core.World.Internal.a22 */,_7H/* Core.World.Internal.a23 */,_7R/* Core.World.Internal.a24 */),
_83/* $fMonadWorld3 */ = function(_84/* B2 */, _85/* B1 */){
  return new F(function(){return _71/* Control.Monad.Trans.State.Strict.$fMonadStateT_$c>> */(_82/* Core.World.Internal.$fMonadWorld_$s$fApplicativeStateT */, _6z/* Haste.Concurrent.Monad.$fMonadCIO */, _84/* B2 */, _85/* B1 */);});
},
_86/* $fMonadWorld5 */ = function(_87/* sbQY */, _88/* sbQZ */, _89/* sbR0 */){
  var _8a/* sbR1 */ = new T(function(){
    return B(A1(_87/* sbQY */,_89/* sbR0 */));
  }),
  _8b/* sbR8 */ = function(_8c/* sbR2 */){
    return new F(function(){return A1(_8a/* sbR1 */,function(_8d/* sbR3 */){
      var _8e/* sbR4 */ = E(_8d/* sbR3 */);
      return new F(function(){return A3(_88/* sbQZ */,_8e/* sbR4 */.a, _8e/* sbR4 */.b, _8c/* sbR2 */);});
    });});
  };
  return E(_8b/* sbR8 */);
},
_8f/* $fMonadWorld */ = new T5(0,_5H/* Core.World.Internal.$fApplicativeWorld */,_86/* Core.World.Internal.$fMonadWorld5 */,_83/* Core.World.Internal.$fMonadWorld3 */,_5D/* Core.World.Internal.$fMonadWorld2 */,_5I/* Core.World.Internal.$fMonadWorld1 */),
_8g/* liftW1 */ = function(_8h/* sbR9 */, _8i/* sbRa */, _8j/* sbRb */){
  return new F(function(){return A1(_8h/* sbR9 */,function(_8k/* sbRc */){
    return new F(function(){return A1(_8j/* sbRb */,new T2(0,_8k/* sbRc */,_8i/* sbRa */));});
  });});
},
_8l/* $fMonadConcWorld */ = new T3(0,_8f/* Core.World.Internal.$fMonadWorld */,_8g/* Core.World.Internal.liftW1 */,_4G/* Core.World.Internal.$fMonadConcWorld1 */),
_8m/* $fMonadEventWorld1 */ = function(_8n/* sbYL */, _8o/* sbYM */, _8p/* sbYN */){
  var _8q/* sbYR */ = function(_8r/* sbYO */, _/* EXTERNAL */){
    return new F(function(){return _e/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(new T(function(){
      return B(A3(_8n/* sbYL */,_8r/* sbYO */, _8o/* sbYM */, _4D/* Core.World.Internal.$fMonadEventWorld2 */));
    }), _6/* GHC.Types.[] */, _/* EXTERNAL */);});
  };
  return new F(function(){return A1(_8p/* sbYN */,new T2(0,_8q/* sbYR */,_8o/* sbYM */));});
},
_8s/* $fMonadIOWorld1 */ = function(_8t/* sbTs */, _8u/* sbTt */, _8v/* sbTu */){
  var _8w/* sbTB */ = function(_/* EXTERNAL */){
    var _8x/* sbTw */ = B(A1(_8t/* sbTs */,_/* EXTERNAL */));
    return new T(function(){
      return B(A1(_8v/* sbTu */,new T2(0,_8x/* sbTw */,_8u/* sbTt */)));
    });
  };
  return new T1(0,_8w/* sbTB */);
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
_9Z/* a36 */ = function(_a0/* sc3l */, _a1/* sc3m */, _a2/* sc3n */){
  return new F(function(){return A1(_a2/* sc3n */,new T2(0,new T2(0,new T(function(){
    return E(E(_a0/* sc3l */).a);
  }),_a0/* sc3l */),_a1/* sc3m */));});
},
_a3/* a37 */ = 16,
_a4/* a38 */ = function(_a5/* sc3w */, _a6/* sc3x */, _a7/* sc3y */){
  var _a8/* sc3z */ = E(_a5/* sc3w */);
  if(!_a8/* sc3z */._){
    return new F(function(){return A1(_a7/* sc3y */,new T2(0,_6/* GHC.Types.[] */,_a6/* sc3x */));});
  }else{
    var _a9/* sc3R */ = function(_aa/* sc3G */){
      var _ab/* sc3H */ = E(_aa/* sc3G */);
      return new F(function(){return _a4/* Core.World.Internal.a38 */(_a8/* sc3z */.b, _ab/* sc3H */.b, function(_ac/* sc3K */){
        var _ad/* sc3L */ = E(_ac/* sc3K */);
        return new F(function(){return A1(_a7/* sc3y */,new T2(0,new T2(1,_ab/* sc3H */.a,_ad/* sc3L */.a),_ad/* sc3L */.b));});
      });});
    };
    return new F(function(){return A2(E(_a8/* sc3z */.a).a,_a6/* sc3x */, _a9/* sc3R */);});
  }
},
_ae/* a39 */ = function(_af/* sc3S */, _ag/* sc3T */, _ah/* sc3U */){
  var _ai/* sc3V */ = E(_af/* sc3S */);
  if(!_ai/* sc3V */._){
    return new F(function(){return A1(_ah/* sc3U */,new T2(0,_6/* GHC.Types.[] */,_ag/* sc3T */));});
  }else{
    var _aj/* sc3Z */ = E(_ai/* sc3V */.a),
    _ak/* sc4e */ = function(_al/* sc42 */){
      var _am/* sc43 */ = E(_al/* sc42 */),
      _an/* sc4d */ = function(_ao/* sc46 */){
        var _ap/* sc47 */ = E(_ao/* sc46 */),
        _aq/* sc48 */ = _ap/* sc47 */.a;
        return new F(function(){return A1(_ah/* sc3U */,new T2(0,new T(function(){
          if(!E(_am/* sc43 */.a)){
            return E(_aq/* sc48 */);
          }else{
            return new T2(1,_aj/* sc3Z */,_aq/* sc48 */);
          }
        }),_ap/* sc47 */.b));});
      };
      return new F(function(){return _ae/* Core.World.Internal.a39 */(_ai/* sc3V */.b, _am/* sc43 */.b, _an/* sc4d */);});
    };
    return new F(function(){return A2(_aj/* sc3Z */.b,_ag/* sc3T */, _ak/* sc4e */);});
  }
},
_ar/* a */ = function(_as/* sbPL */, _at/* sbPM */, _au/* sbPN */){
  return new F(function(){return A1(_au/* sbPN */,new T2(0,new T2(0,new T(function(){
    return E(_as/* sbPL */).b;
  }),_as/* sbPL */),_at/* sbPM */));});
},
_av/* False */ = false,
_aw/* True */ = true,
_ax/* Nil */ = __Z/* EXTERNAL */,
_ay/* $wincr */ = function(_az/* shf5 */, _aA/* shf6 */, _aB/* shf7 */, _aC/* shf8 */){
  var _aD/* shf9 */ = E(_aC/* shf8 */);
  switch(_aD/* shf9 */._){
    case 0:
      return new T3(2,_aA/* shf6 */,_aB/* shf7 */,_ax/* Data.PQueue.Internals.Nil */);
    case 1:
      return new T3(2,_aA/* shf6 */,_aB/* shf7 */,_aD/* shf9 */.a);
    default:
      var _aE/* shfb */ = _aD/* shf9 */.a,
      _aF/* shfc */ = _aD/* shf9 */.b,
      _aG/* shfd */ = _aD/* shf9 */.c;
      return new T1(1,new T(function(){
        if(!B(A2(_az/* shf5 */,_aA/* shf6 */, _aE/* shfb */))){
          return B(_ay/* Data.PQueue.Internals.$wincr */(_az/* shf5 */, _aE/* shfb */, new T3(0,_aA/* shf6 */,_aB/* shf7 */,_aF/* shfc */), _aG/* shfd */));
        }else{
          return B(_ay/* Data.PQueue.Internals.$wincr */(_az/* shf5 */, _aA/* shf6 */, new T3(0,_aE/* shfb */,_aF/* shfc */,_aB/* shf7 */), _aG/* shfd */));
        }
      }));
  }
},
_aH/* extractBin */ = function(_aI/* shgw */, _aJ/* shgx */){
  var _aK/* shgy */ = E(_aJ/* shgx */);
  switch(_aK/* shgy */._){
    case 0:
      return __Z/* EXTERNAL */;
    case 1:
      var _aL/* shgA */ = B(_aH/* Data.PQueue.Internals.extractBin */(_aI/* shgw */, _aK/* shgy */.a));
      if(!_aL/* shgA */._){
        return __Z/* EXTERNAL */;
      }else{
        var _aM/* shgE */ = E(_aL/* shgA */.b);
        return new T3(1,_aL/* shgA */.a,_aM/* shgE */.c,new T3(2,_aM/* shgE */.a,_aM/* shgE */.b,_aL/* shgA */.c));
      }
      break;
    default:
      var _aN/* shgJ */ = _aK/* shgy */.a,
      _aO/* shgK */ = _aK/* shgy */.b,
      _aP/* shgL */ = _aK/* shgy */.c,
      _aQ/* shgM */ = B(_aH/* Data.PQueue.Internals.extractBin */(_aI/* shgw */, _aP/* shgL */));
      if(!_aQ/* shgM */._){
        return new T3(1,_aN/* shgJ */,_aO/* shgK */,new T1(1,_aP/* shgL */));
      }else{
        var _aR/* shgO */ = _aQ/* shgM */.a,
        _aS/* shgQ */ = _aQ/* shgM */.c;
        if(!B(A2(_aI/* shgw */,_aN/* shgJ */, _aR/* shgO */))){
          var _aT/* shgS */ = E(_aQ/* shgM */.b),
          _aU/* shgT */ = _aT/* shgS */.a,
          _aV/* shgU */ = _aT/* shgS */.b;
          return new T3(1,_aR/* shgO */,_aT/* shgS */.c,new T1(1,new T(function(){
            if(!B(A2(_aI/* shgw */,_aN/* shgJ */, _aU/* shgT */))){
              return B(_ay/* Data.PQueue.Internals.$wincr */(_aI/* shgw */, _aU/* shgT */, new T3(0,_aN/* shgJ */,_aO/* shgK */,_aV/* shgU */), _aS/* shgQ */));
            }else{
              return B(_ay/* Data.PQueue.Internals.$wincr */(_aI/* shgw */, _aN/* shgJ */, new T3(0,_aU/* shgT */,_aV/* shgU */,_aO/* shgK */), _aS/* shgQ */));
            }
          })));
        }else{
          return new T3(1,_aN/* shgJ */,_aO/* shgK */,new T1(1,_aP/* shgL */));
        }
      }
  }
},
_aW/* a26 */ = function(_aX/* sbTC */){
  var _aY/* sbTD */ = new T(function(){
    var _aZ/* sbTE */ = E(_aX/* sbTC */),
    _b0/* sbTJ */ = E(_aZ/* sbTE */.c);
    if(!_b0/* sbTJ */._){
      var _b1/* sbTJ#result */ = __Z/* EXTERNAL */;
    }else{
      var _b2/* sbU3 */ = B(_aH/* Data.PQueue.Internals.extractBin */(function(_b3/* sbTN */, _b4/* sbTO */){
        var _b5/* sbTV */ = E(E(_b3/* sbTN */).a),
        _b6/* sbTX */ = E(E(_b4/* sbTO */).a);
        return (_b5/* sbTV */>=_b6/* sbTX */) ? _b5/* sbTV */==_b6/* sbTX */ : true;
      }, _b0/* sbTJ */.c));
      if(!_b2/* sbU3 */._){
        var _b7/* sbU3#result */ = __Z/* EXTERNAL */;
      }else{
        var _b7/* sbU3#result */ = new T3(1,_b0/* sbTJ */.a-1|0,_b2/* sbU3 */.a,E(_b2/* sbU3 */.c));
      }
      var _b1/* sbTJ#result */ = _b7/* sbU3#result */;
    }
    return new T4(0,E(_aZ/* sbTE */.a),_aZ/* sbTE */.b,E(_b1/* sbTJ#result */),E(_aZ/* sbTE */.d));
  });
  return function(_b8/* sbUb */, _b9/* sbUc */){
    return new F(function(){return A1(_b9/* sbUc */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,_aY/* sbTD */),_b8/* sbUb */));});
  };
},
_ba/* a3 */ = function(_bb/* sbQm */, _bc/* sbQn */, _bd/* sbQo */){
  return new F(function(){return A1(_bd/* sbQo */,new T2(0,new T2(0,new T(function(){
    var _be/* sbQu */ = E(E(_bb/* sbQm */).c);
    if(!_be/* sbQu */._){
      return __Z/* EXTERNAL */;
    }else{
      return new T1(1,_be/* sbQu */.b);
    }
  }),_bb/* sbQm */),_bc/* sbQn */));});
},
_bf/* a2 */ = function(_bg/* sbQa */, _bh/* sbQb */, _bi/* sbQc */){
  return new F(function(){return A1(_bi/* sbQc */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
    var _bj/* sbQd */ = E(_bg/* sbQa */);
    return new T4(0,E(_bj/* sbQd */.a),_bj/* sbQd */.b+1|0,E(_bj/* sbQd */.c),E(_bj/* sbQd */.d));
  })),_bh/* sbQb */));});
},
_bk/* a40 */ = function(_bl/* sc4f */, _bm/* sc4g */){
  return new T1(0,B(_bn/* Core.World.Internal.$wa7 */(_bl/* sc4f */)));
},
_bo/* absentError */ = function(_bp/* s4nFP */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Oops!  Entered absent arg ", new T(function(){
    return B(unCStr/* EXTERNAL */(_bp/* s4nFP */));
  }))));});
},
_bq/* eta */ = new T(function(){
  return B(_bo/* Control.Exception.Base.absentError */("w_saPH ((), MVar WorldState) -> Action"));
}),
_br/* eta1 */ = function(_bs/* sc4j */){
  return new F(function(){return _bk/* Core.World.Internal.a40 */(E(_bs/* sc4j */).b, _bq/* Core.World.Internal.eta */);});
},
_bt/* lvl6 */ = function(_bu/* sc4n */){
  var _bv/* sc4q */ = E(_bu/* sc4n */).b;
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bv/* sc4q */, _bf/* Core.World.Internal.a2 */, _bv/* sc4q */, _br/* Core.World.Internal.eta1 */]);});
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
_bC/* lvl7 */ = function(_bD/* sc4r */){
  var _bE/* sc4s */ = E(_bD/* sc4r */),
  _bF/* sc50 */ = function(_bG/* sc4v */, _bH/* sc4w */){
    var _bI/* sc4x */ = function(_bJ/* sc4y */){
      return new F(function(){return A1(_bH/* sc4w */,new T2(0,_aw/* GHC.Types.True */,E(_bJ/* sc4y */).b));});
    },
    _bK/* sc4Z */ = function(_bL/* sc4D */){
      var _bM/* sc4E */ = E(_bL/* sc4D */),
      _bN/* sc4G */ = _bM/* sc4E */.b,
      _bO/* sc4H */ = E(_bM/* sc4E */.a);
      if(!_bO/* sc4H */._){
        return new F(function(){return A1(_bH/* sc4w */,new T2(0,_av/* GHC.Types.False */,_bN/* sc4G */));});
      }else{
        var _bP/* sc4K */ = E(_bO/* sc4H */.a);
        if(E(_bP/* sc4K */.a)<=E(_bE/* sc4s */.a)){
          var _bQ/* sc4T */ = new T(function(){
            return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bN/* sc4G */, _aW/* Core.World.Internal.a26 */, _bN/* sc4G */, _bI/* sc4x */]));
          });
          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_bP/* sc4K */.b, _7/* GHC.Tuple.() */, function(_bR/* sc4U */){
            return E(_bQ/* sc4T */);
          })));
        }else{
          return new F(function(){return A1(_bH/* sc4w */,new T2(0,_av/* GHC.Types.False */,_bN/* sc4G */));});
        }
      }
    };
    return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bG/* sc4v */, _ba/* Core.World.Internal.a3 */, _bG/* sc4v */, _bK/* sc4Z */]);});
  };
  return new F(function(){return A(_bw/* Core.Util.while */,[_8f/* Core.World.Internal.$fMonadWorld */, _bF/* sc50 */, _bE/* sc4s */.b, _bt/* Core.World.Internal.lvl6 */]);});
},
_bS/* lvl8 */ = function(_bT/* sc51 */){
  var _bU/* sc54 */ = E(_bT/* sc51 */).b;
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bU/* sc54 */, _ar/* Core.World.Internal.a */, _bU/* sc54 */, _bC/* Core.World.Internal.lvl7 */]);});
},
_bV/* lvl9 */ = function(_bW/* sc55 */){
  var _bX/* sc56 */ = E(_bW/* sc55 */),
  _bY/* sc58 */ = _bX/* sc56 */.b,
  _bZ/* sc5l */ = function(_c0/* sc59 */, _c1/* sc5a */, _c2/* sc5b */){
    return new F(function(){return A1(_c2/* sc5b */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
      var _c3/* sc5c */ = E(_c0/* sc59 */);
      return new T4(0,E(_bX/* sc56 */.a),_c3/* sc5c */.b,E(_c3/* sc5c */.c),E(_c3/* sc5c */.d));
    })),_c1/* sc5a */));});
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _bY/* sc58 */, _bZ/* sc5l */, _bY/* sc58 */, _bS/* Core.World.Internal.lvl8 */]);});
},
_c4/* lvl10 */ = function(_c5/* sc5m */){
  var _c6/* sc5n */ = E(_c5/* sc5m */),
  _c7/* sc5o */ = _c6/* sc5n */.a;
  return new F(function(){return _a4/* Core.World.Internal.a38 */(_c7/* sc5o */, _c6/* sc5n */.b, function(_c8/* sc5q */){
    return new F(function(){return _ae/* Core.World.Internal.a39 */(_c7/* sc5o */, E(_c8/* sc5q */).b, _bV/* Core.World.Internal.lvl9 */);});
  });});
},
_bn/* $wa7 */ = function(_c9/* sc5v */){
  var _ca/* sc5w */ = new T(function(){
    return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _c9/* sc5v */, _9Z/* Core.World.Internal.a36 */, _c9/* sc5v */, _c4/* Core.World.Internal.lvl10 */]));
  });
  return new F(function(){return _9p/* Haste.Concurrent.$wa */(_a3/* Core.World.Internal.a37 */, function(_cb/* sc5x */){
    return E(_ca/* sc5w */);
  });});
},
_cc/* MouseDown */ = 2,
_cd/* MouseMove */ = 4,
_ce/* MouseUp */ = 3,
_cf/* a1 */ = function(_cg/* sbPW */, _ch/* sbPX */, _ci/* sbPY */){
  return new F(function(){return A1(_ci/* sbPY */,new T2(0,new T2(0,new T(function(){
    return E(E(E(_cg/* sbPW */).d).b);
  }),_cg/* sbPW */),_ch/* sbPX */));});
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
_d4/* oneway2 */ = function(_d5/* sbPH */, _d6/* sbPI */){
  return new F(function(){return A1(_d6/* sbPI */,new T2(0,_7/* GHC.Tuple.() */,_d5/* sbPH */));});
},
_d7/* $wa5 */ = function(_d8/* sc5z */, _d9/* sc5A */){
  return function(_/* EXTERNAL */){
    var _da/* sc5C */ = nMV/* EXTERNAL */(_cs/* Core.World.Internal.lvl14 */),
    _db/* sc5E */ = _da/* sc5C */,
    _dc/* sc5G */ = function(_dd/* sc5H */){
      return new F(function(){return A1(_d9/* sc5A */,E(_dd/* sc5H */).a);});
    },
    _de/* sc5L */ = function(_df/* sc5M */){
      return new F(function(){return A2(_d8/* sc5z */,E(_df/* sc5M */).b, _dc/* sc5G */);});
    },
    _dg/* sc7C */ = function(_/* EXTERNAL */){
      var _dh/* sc5R */ = nMV/* EXTERNAL */(_cm/* Core.World.Internal.lvl11 */),
      _di/* sc5T */ = _dh/* sc5R */,
      _dj/* sc7y */ = new T(function(){
        var _dk/* sc6i */ = function(_dl/* sc6m */){
          return new F(function(){return _dm/* sc6j */(E(_dl/* sc6m */).b);});
        },
        _dm/* sc6j */ = function(_dn/* sc6q */){
          var _do/* sc7v */ = function(_dp/* sc6r */){
            var _dq/* sc7u */ = function(_dr/* sc6s */){
              var _ds/* sc6t */ = E(_dr/* sc6s */),
              _dt/* sc6v */ = _ds/* sc6t */.b,
              _du/* sc6w */ = E(_dp/* sc6r */),
              _dv/* sc6z */ = function(_dw/* sc6A */, _dx/* sc6B */, _dy/* sc6C */){
                var _dz/* sc6D */ = function(_dA/*  sc6E */, _dB/*  sc6F */){
                  while(1){
                    var _dC/*  sc6D */ = B((function(_dD/* sc6E */, _dE/* sc6F */){
                      var _dF/* sc6G */ = E(_dE/* sc6F */);
                      switch(_dF/* sc6G */._){
                        case 0:
                          _dA/*  sc6E */ = new T(function(){
                            return B(_dz/* sc6D */(_dD/* sc6E */, _dF/* sc6G */.d));
                          });
                          _dB/*  sc6F */ = _dF/* sc6G */.c;
                          return __continue/* EXTERNAL */;
                        case 1:
                          var _dG/* sc6O */ = new T(function(){
                            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _dF/* sc6G */.b, _dw/* sc6A */));
                          }),
                          _dH/* sc6Y */ = function(_dI/* sc6P */){
                            var _dJ/* sc6Q */ = new T(function(){
                              return B(A1(_dG/* sc6O */,_dI/* sc6P */));
                            }),
                            _dK/* sc6X */ = function(_dL/* sc6R */){
                              return new F(function(){return A1(_dJ/* sc6Q */,function(_dM/* sc6S */){
                                return new F(function(){return A2(_dD/* sc6E */,E(_dM/* sc6S */).b, _dL/* sc6R */);});
                              });});
                            };
                            return E(_dK/* sc6X */);
                          };
                          return E(_dH/* sc6Y */);
                        default:
                          return E(_dD/* sc6E */);
                      }
                    })(_dA/*  sc6E */, _dB/*  sc6F */));
                    if(_dC/*  sc6D */!=__continue/* EXTERNAL */){
                      return _dC/*  sc6D */;
                    }
                  }
                },
                _dN/* sc6Z */ = E(_ds/* sc6t */.a);
                if(!_dN/* sc6Z */._){
                  var _dO/* sc72 */ = _dN/* sc6Z */.c,
                  _dP/* sc73 */ = _dN/* sc6Z */.d;
                  if(_dN/* sc6Z */.b>=0){
                    return new F(function(){return A(_dz/* sc6D */,[new T(function(){
                      return B(_dz/* sc6D */(_d4/* Core.World.Internal.oneway2 */, _dP/* sc73 */));
                    }), _dO/* sc72 */, _dx/* sc6B */, _dy/* sc6C */]);});
                  }else{
                    return new F(function(){return A(_dz/* sc6D */,[new T(function(){
                      return B(_dz/* sc6D */(_d4/* Core.World.Internal.oneway2 */, _dO/* sc72 */));
                    }), _dP/* sc73 */, _dx/* sc6B */, _dy/* sc6C */]);});
                  }
                }else{
                  return new F(function(){return A(_dz/* sc6D */,[_d4/* Core.World.Internal.oneway2 */, _dN/* sc6Z */, _dx/* sc6B */, _dy/* sc6C */]);});
                }
              };
              switch(E(_du/* sc6w */.a)){
                case 2:
                  return new F(function(){return _dv/* sc6z */(_cl/* Core.World.Internal.lvl1 */, _dt/* sc6v */, _dk/* sc6i */);});
                  break;
                case 3:
                  return new F(function(){return _dv/* sc6z */(_ck/* Core.World.Internal.lvl */, _dt/* sc6v */, _dk/* sc6i */);});
                  break;
                case 4:
                  var _dQ/* sc79 */ = new T(function(){
                    return E(E(_du/* sc6w */.b).a);
                  });
                  return new F(function(){return _dv/* sc6z */(new T1(1,new T2(0,new T(function(){
                    return E(E(_dQ/* sc79 */).a);
                  }),new T(function(){
                    return E(E(_dQ/* sc79 */).b);
                  }))), _dt/* sc6v */, _dk/* sc6i */);});
                  break;
                default:
                  return new F(function(){return _dm/* sc6j */(_dt/* sc6v */);});
              }
            };
            return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _dn/* sc6q */, _cf/* Core.World.Internal.a1 */, _dn/* sc6q */, _dq/* sc7u */]);});
          };
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_di/* sc5T */, _do/* sc7v */)));
        };
        return B(_dm/* sc6j */(_db/* sc5E */));
      }),
      _dR/* sc6g */ = new T(function(){
        var _dS/* sc5V */ = new T(function(){
          return B(_cC/* Haste.Events.Core.onEvent */(_8z/* Core.World.Internal.$fMonadEventWorld */, _4C/* Haste.DOM.Core.$fIsElemElem */, _4z/* Haste.Events.MouseEvents.$fEventMouseEvent */, _cj/* Haste.DOM.Core.document1 */, _cd/* Haste.Events.MouseEvents.MouseMove */, function(_dT/* sc5W */){
            return new F(function(){return _2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _di/* sc5T */, new T2(0,_cd/* Haste.Events.MouseEvents.MouseMove */,_dT/* sc5W */));});
          }));
        }),
        _dU/* sc5Z */ = new T(function(){
          return B(_cC/* Haste.Events.Core.onEvent */(_8z/* Core.World.Internal.$fMonadEventWorld */, _4C/* Haste.DOM.Core.$fIsElemElem */, _4z/* Haste.Events.MouseEvents.$fEventMouseEvent */, _cj/* Haste.DOM.Core.document1 */, _ce/* Haste.Events.MouseEvents.MouseUp */, function(_dV/* sc60 */){
            return new F(function(){return _2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _di/* sc5T */, new T2(0,_ce/* Haste.Events.MouseEvents.MouseUp */,_dV/* sc60 */));});
          }));
        }),
        _dW/* sc63 */ = function(_dX/* sc64 */){
          return new F(function(){return A2(_dU/* sc5Z */,E(_dX/* sc64 */).b, _de/* sc5L */);});
        };
        return B(A(_cC/* Haste.Events.Core.onEvent */,[_8z/* Core.World.Internal.$fMonadEventWorld */, _4C/* Haste.DOM.Core.$fIsElemElem */, _4z/* Haste.Events.MouseEvents.$fEventMouseEvent */, _cj/* Haste.DOM.Core.document1 */, _cc/* Haste.Events.MouseEvents.MouseDown */, function(_dY/* sc68 */){
          return new F(function(){return _2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _di/* sc5T */, new T2(0,_cc/* Haste.Events.MouseEvents.MouseDown */,_dY/* sc68 */));});
        }, _db/* sc5E */, function(_dZ/* sc6b */){
          return new F(function(){return A2(_dS/* sc5V */,E(_dZ/* sc6b */).b, _dW/* sc63 */);});
        }]));
      });
      return new T1(1,new T2(1,_dR/* sc6g */,new T2(1,_dj/* sc7y */,_6/* GHC.Types.[] */)));
    };
    return new T1(1,new T2(1,new T1(0,_dg/* sc7C */),new T2(1,new T(function(){
      return new T1(0,B(_bn/* Core.World.Internal.$wa7 */(_db/* sc5E */)));
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
_e8/* $wa */ = function(_e9/* sfBJ */, _ea/* sfBK */, _eb/* sfBL */, _ec/* sfBM */){
  return function(_/* EXTERNAL */){
    var _ed/* sfBO */ = E(_e9/* sfBJ */),
    _ee/* sfBQ */ = rMV/* EXTERNAL */(_ed/* sfBO */),
    _ef/* sfBT */ = E(_ee/* sfBQ */);
    if(!_ef/* sfBT */._){
      var _eg/* sfBW */ = B(A2(_ea/* sfBK */,_ef/* sfBT */.a, _/* EXTERNAL */)),
      _eh/* sfCI */ = function(_ei/* sfBZ */, _/* EXTERNAL */){
        var _ej/* sfC1 */ = function(_/* EXTERNAL */){
          var _ek/* sfC4 */ = rMV/* EXTERNAL */(_ed/* sfBO */),
          _el/* sfC7 */ = function(_/* EXTERNAL */, _em/* sfC9 */){
            var _en/* sfCa */ = function(_/* EXTERNAL */){
              var _eo/* sfCl */ = __createJSFunc/* EXTERNAL */(2, function(_ep/* sfCc */, _/* EXTERNAL */){
                var _eq/* sfCe */ = B(_er/* sfC2 */(_/* EXTERNAL */, _/* EXTERNAL */));
                return _48/* Haste.Prim.Any.jsNull */;
              }),
              _es/* sfCr */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _eo/* sfCl */);
              return _7/* GHC.Tuple.() */;
            },
            _et/* sfCu */ = E(_em/* sfC9 */);
            if(!_et/* sfCu */._){
              return new F(function(){return _en/* sfCa */(_/* EXTERNAL */);});
            }else{
              var _eu/* sfCw */ = B(A2(_ea/* sfBK */,_et/* sfCu */.a, _/* EXTERNAL */));
              return new F(function(){return _en/* sfCa */(_/* EXTERNAL */);});
            }
          },
          _ev/* sfCz */ = E(_ek/* sfC4 */);
          if(!_ev/* sfCz */._){
            return new F(function(){return _el/* sfC7 */(_/* EXTERNAL */, new T1(1,_ev/* sfCz */.a));});
          }else{
            return new F(function(){return _el/* sfC7 */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
        },
        _er/* sfC2 */ = function(_ew/* sfCE */, _/* EXTERNAL */){
          return new F(function(){return _ej/* sfC1 */(_/* EXTERNAL */);});
        },
        _ex/* sfCF */ = B(_er/* sfC2 */(_/* EXTERNAL */, _/* EXTERNAL */));
        return _48/* Haste.Prim.Any.jsNull */;
      },
      _ey/* sfCM */ = __createJSFunc/* EXTERNAL */(2, E(_eh/* sfCI */)),
      _ez/* sfCS */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _ey/* sfCM */);
      return new T(function(){
        return B(A1(_ec/* sfBM */,new T2(0,_7/* GHC.Tuple.() */,_eb/* sfBL */)));
      });
    }else{
      var _eA/* sfDH */ = function(_eB/* sfCY */, _/* EXTERNAL */){
        var _eC/* sfD0 */ = function(_/* EXTERNAL */){
          var _eD/* sfD3 */ = rMV/* EXTERNAL */(_ed/* sfBO */),
          _eE/* sfD6 */ = function(_/* EXTERNAL */, _eF/* sfD8 */){
            var _eG/* sfD9 */ = function(_/* EXTERNAL */){
              var _eH/* sfDk */ = __createJSFunc/* EXTERNAL */(2, function(_eI/* sfDb */, _/* EXTERNAL */){
                var _eJ/* sfDd */ = B(_eK/* sfD1 */(_/* EXTERNAL */, _/* EXTERNAL */));
                return _48/* Haste.Prim.Any.jsNull */;
              }),
              _eL/* sfDq */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _eH/* sfDk */);
              return _7/* GHC.Tuple.() */;
            },
            _eM/* sfDt */ = E(_eF/* sfD8 */);
            if(!_eM/* sfDt */._){
              return new F(function(){return _eG/* sfD9 */(_/* EXTERNAL */);});
            }else{
              var _eN/* sfDv */ = B(A2(_ea/* sfBK */,_eM/* sfDt */.a, _/* EXTERNAL */));
              return new F(function(){return _eG/* sfD9 */(_/* EXTERNAL */);});
            }
          },
          _eO/* sfDy */ = E(_eD/* sfD3 */);
          if(!_eO/* sfDy */._){
            return new F(function(){return _eE/* sfD6 */(_/* EXTERNAL */, new T1(1,_eO/* sfDy */.a));});
          }else{
            return new F(function(){return _eE/* sfD6 */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
        },
        _eK/* sfD1 */ = function(_eP/* sfDD */, _/* EXTERNAL */){
          return new F(function(){return _eC/* sfD0 */(_/* EXTERNAL */);});
        },
        _eQ/* sfDE */ = B(_eK/* sfD1 */(_/* EXTERNAL */, _/* EXTERNAL */));
        return _48/* Haste.Prim.Any.jsNull */;
      },
      _eR/* sfDL */ = __createJSFunc/* EXTERNAL */(2, E(_eA/* sfDH */)),
      _eS/* sfDR */ = __app1/* EXTERNAL */(E(_e7/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _eR/* sfDL */);
      return new T(function(){
        return B(A1(_ec/* sfBM */,new T2(0,_7/* GHC.Tuple.() */,_eb/* sfBL */)));
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
_eY/* a24 */ = function(_eZ/* s7ED */, _f0/* s7EE */, _f1/* s7EF */){
  return new F(function(){return A1(_f1/* s7EF */,new T2(0,new T2(0,_eZ/* s7ED */,_eZ/* s7ED */),_f0/* s7EE */));});
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
_fD/* valueOf1 */ = function(_fE/* skYb */, _fF/* skYc */, _fG/* skYd */){
  var _fH/* skYe */ = E(_fE/* skYb */);
  switch(_fH/* skYe */._){
    case 0:
      return new F(function(){return _5D/* Core.World.Internal.$fMonadWorld2 */(_fH/* skYe */.a, _fF/* skYc */, _fG/* skYd */);});
      break;
    case 1:
      return new F(function(){return _8s/* Core.World.Internal.$fMonadIOWorld1 */(_fH/* skYe */.a, _fF/* skYc */, _fG/* skYd */);});
      break;
    case 2:
      var _fI/* skYm */ = E(_fH/* skYe */.a).c,
      _fJ/* skYw */ = function(_fK/* skYn */){
        var _fL/* skYo */ = new T(function(){
          var _fM/* skYq */ = new T(function(){
            return B(A1(_fH/* skYe */.b,new T(function(){
              return B(_fB/* Data.Tuple.fst */(_fK/* skYn */));
            })));
          });
          return B(A1(_fG/* skYd */,new T2(0,_fM/* skYq */,_fF/* skYc */)));
        });
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_fI/* skYm */, _fK/* skYn */, function(_fN/* skYs */){
          return E(_fL/* skYo */);
        })));
      };
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_fI/* skYm */, _fJ/* skYw */)));
    default:
      var _fO/* skYE */ = E(_fH/* skYe */.a).c,
      _fP/* skYT */ = function(_fQ/* skYF */){
        var _fR/* skYG */ = function(_/* EXTERNAL */){
          var _fS/* skYJ */ = B(A2(_fH/* skYe */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_fQ/* skYF */));
          }), _/* EXTERNAL */));
          return new T(function(){
            return B(A1(_fG/* skYd */,new T2(0,_fS/* skYJ */,_fF/* skYc */)));
          });
        };
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_fO/* skYE */, _fQ/* skYF */, function(_fT/* skYP */){
          return E(new T1(0,_fR/* skYG */));
        })));
      };
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_fO/* skYE */, _fP/* skYT */)));
  }
},
_fU/* applyTransform_world */ = function(_fV/*  sFlX */, _fW/*  sFlY */, _fX/*  sFlZ */, _fY/*  sFm0 */, _fZ/*  sFm1 */, _g0/*  sFm2 */, _g1/*  sFm3 */){
  while(1){
    var _g2/*  applyTransform_world */ = B((function(_g3/* sFlX */, _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */){
      var _ga/* sFm4 */ = new T(function(){
        return 0*E(_g4/* sFlY */)+0*E(_g5/* sFlZ */)+E(_g6/* sFm0 */);
      }),
      _gb/* sFmf */ = new T(function(){
        return 0*E(_g7/* sFm1 */)+0*E(_g8/* sFm2 */)+E(_g9/* sFm3 */);
      }),
      _gc/* sFmq */ = B(_fo/* Control.Monad.Skeleton.debone */(_g3/* sFlX */));
      if(!_gc/* sFmq */._){
        return function(_gd/* _fa_1 */, _ge/* _fa_2 */){
          return new F(function(){return _5D/* Core.World.Internal.$fMonadWorld2 */(_gc/* sFmq */.a, _gd/* _fa_1 */, _ge/* _fa_2 */);});
        };
      }else{
        var _gf/* sFmt */ = _gc/* sFmq */.b,
        _gg/* sFmu */ = E(_gc/* sFmq */.a);
        switch(_gg/* sFmu */._){
          case 0:
            var _gh/*   sFlY */ = _g4/* sFlY */,
            _gi/*   sFlZ */ = _g5/* sFlZ */,
            _gj/*   sFm0 */ = _g6/* sFm0 */,
            _gk/*   sFm1 */ = _g7/* sFm1 */,
            _gl/*   sFm2 */ = _g8/* sFm2 */,
            _gm/*   sFm3 */ = _g9/* sFm3 */;
            _fV/*  sFlX */ = B(A1(_gf/* sFmt */,_gg/* sFmu */.b));
            _fW/*  sFlY */ = _gh/*   sFlY */;
            _fX/*  sFlZ */ = _gi/*   sFlZ */;
            _fY/*  sFm0 */ = _gj/*   sFm0 */;
            _fZ/*  sFm1 */ = _gk/*   sFm1 */;
            _g0/*  sFm2 */ = _gl/*   sFm2 */;
            _g1/*  sFm3 */ = _gm/*   sFm3 */;
            return __continue/* EXTERNAL */;
          case 1:
            var _gn/* sFmI */ = function(_go/* sFmz */, _gp/* sFmA */){
              var _gq/* sFmH */ = function(_/* EXTERNAL */){
                var _gr/* sFmC */ = B(A1(_gg/* sFmu */.a,_/* EXTERNAL */));
                return new T(function(){
                  return B(A(_fU/* Core.Render.Internal.applyTransform_world */,[B(A1(_gf/* sFmt */,_gr/* sFmC */)), _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */, _go/* sFmz */, _gp/* sFmA */]));
                });
              };
              return new T1(0,_gq/* sFmH */);
            };
            return E(_gn/* sFmI */);
          case 2:
            var _gs/* sFmL */ = new T(function(){
              return B(A(_gg/* sFmu */.a,[_g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */]));
            }),
            _gt/* sFmM */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmt */,_gg/* sFmu */.b)), _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */));
            }),
            _gu/* sFmX */ = function(_gv/* sFmO */){
              var _gw/* sFmP */ = new T(function(){
                return B(A1(_gs/* sFmL */,_gv/* sFmO */));
              }),
              _gx/* sFmW */ = function(_gy/* sFmQ */){
                return new F(function(){return A1(_gw/* sFmP */,function(_gz/* sFmR */){
                  return new F(function(){return A2(_gt/* sFmM */,E(_gz/* sFmR */).b, _gy/* sFmQ */);});
                });});
              };
              return E(_gx/* sFmW */);
            };
            return E(_gu/* sFmX */);
          case 3:
            var _gA/* sFn1 */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(_gg/* sFmu */.b, _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */));
            }),
            _gB/* sFn2 */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmt */,_gg/* sFmu */.c)), _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */));
            }),
            _gC/* sFnd */ = function(_gD/* sFn4 */){
              var _gE/* sFn5 */ = new T(function(){
                return B(A1(_gA/* sFn1 */,_gD/* sFn4 */));
              }),
              _gF/* sFnc */ = function(_gG/* sFn6 */){
                return new F(function(){return A1(_gE/* sFn5 */,function(_gH/* sFn7 */){
                  return new F(function(){return A2(_gB/* sFn2 */,E(_gH/* sFn7 */).b, _gG/* sFn6 */);});
                });});
              };
              return E(_gF/* sFnc */);
            };
            return E(_gC/* sFnd */);
          case 4:
            var _gI/* sFnm */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmt */,_gg/* sFmu */.h)), _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */));
            }),
            _gJ/* sFpf */ = function(_gK/* sFno */, _gL/* sFnp */){
              var _gM/* sFnq */ = function(_gN/* sFnr */){
                return new F(function(){return A2(_gI/* sFnm */,E(_gN/* sFnr */).b, _gL/* sFnp */);});
              },
              _gO/* sFpe */ = function(_gP/* sFnv */){
                var _gQ/* sFnw */ = E(_gP/* sFnv */),
                _gR/* sFnx */ = _gQ/* sFnw */.a,
                _gS/* sFpd */ = function(_gT/* sFnz */){
                  var _gU/* sFnA */ = E(_gT/* sFnz */),
                  _gV/* sFnB */ = _gU/* sFnA */.a,
                  _gW/* sFpc */ = function(_gX/* sFnD */){
                    var _gY/* sFnE */ = E(_gX/* sFnD */),
                    _gZ/* sFnF */ = _gY/* sFnE */.a,
                    _h0/* sFpb */ = function(_h1/* sFnH */){
                      var _h2/* sFnI */ = E(_h1/* sFnH */),
                      _h3/* sFnJ */ = _h2/* sFnI */.a,
                      _h4/* sFnL */ = new T(function(){
                        return E(_gR/* sFnx */)*E(_g7/* sFm1 */)+E(_h3/* sFnJ */)*E(_g8/* sFm2 */);
                      }),
                      _h5/* sFnX */ = new T(function(){
                        return E(_gR/* sFnx */)*E(_g4/* sFlY */)+E(_h3/* sFnJ */)*E(_g5/* sFlZ */);
                      }),
                      _h6/* sFpa */ = function(_h7/* sFo9 */){
                        var _h8/* sFoa */ = E(_h7/* sFo9 */),
                        _h9/* sFob */ = _h8/* sFoa */.a,
                        _ha/* sFod */ = new T(function(){
                          return E(_gV/* sFnB */)*E(_g7/* sFm1 */)+E(_h9/* sFob */)*E(_g8/* sFm2 */);
                        }),
                        _hb/* sFop */ = new T(function(){
                          return E(_gV/* sFnB */)*E(_g4/* sFlY */)+E(_h9/* sFob */)*E(_g5/* sFlZ */);
                        }),
                        _hc/* sFp9 */ = function(_hd/* sFoB */){
                          var _he/* sFoC */ = E(_hd/* sFoB */),
                          _hf/* sFoD */ = _he/* sFoC */.a;
                          return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sFmu */.g, _h5/* sFnX */, _hb/* sFop */, new T(function(){
                            return E(_gZ/* sFnF */)*E(_g4/* sFlY */)+E(_hf/* sFoD */)*E(_g5/* sFlZ */)+E(_g6/* sFm0 */);
                          }), _h4/* sFnL */, _ha/* sFod */, new T(function(){
                            return E(_gZ/* sFnF */)*E(_g7/* sFm1 */)+E(_hf/* sFoD */)*E(_g8/* sFm2 */)+E(_g9/* sFm3 */);
                          }), _he/* sFoC */.b, _gM/* sFnq */]);});
                        };
                        return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmu */.f, _h8/* sFoa */.b, _hc/* sFp9 */);});
                      };
                      return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmu */.e, _h2/* sFnI */.b, _h6/* sFpa */);});
                    };
                    return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmu */.d, _gY/* sFnE */.b, _h0/* sFpb */);});
                  };
                  return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmu */.c, _gU/* sFnA */.b, _gW/* sFpc */);});
                };
                return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmu */.b, _gQ/* sFnw */.b, _gS/* sFpd */);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmu */.a, _gK/* sFno */, _gO/* sFpe */);});
            };
            return E(_gJ/* sFpf */);
          case 5:
            var _hg/* sFpj */ = E(_gg/* sFmu */.a),
            _hh/* sFpm */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmt */,_gg/* sFmu */.c)), _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */));
            }),
            _hi/* sFpo */ = new T(function(){
              return 0*E(_g7/* sFm1 */)+E(_g8/* sFm2 */);
            }),
            _hj/* sFpv */ = new T(function(){
              return E(_g7/* sFm1 */)+0*E(_g8/* sFm2 */);
            }),
            _hk/* sFpC */ = new T(function(){
              return 0*E(_g4/* sFlY */)+E(_g5/* sFlZ */);
            }),
            _hl/* sFpJ */ = new T(function(){
              return E(_g4/* sFlY */)+0*E(_g5/* sFlZ */);
            }),
            _hm/* sFqB */ = function(_hn/* sFpQ */, _ho/* sFpR */){
              var _hp/* sFpS */ = function(_hq/* sFpT */){
                return new F(function(){return A2(_hh/* sFpm */,E(_hq/* sFpT */).b, _ho/* sFpR */);});
              },
              _hr/* sFqA */ = function(_hs/* sFpX */){
                var _ht/* sFpY */ = E(_hs/* sFpX */),
                _hu/* sFpZ */ = _ht/* sFpY */.a,
                _hv/* sFqz */ = function(_hw/* sFq1 */){
                  var _hx/* sFq2 */ = E(_hw/* sFq1 */),
                  _hy/* sFq3 */ = _hx/* sFq2 */.a;
                  return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sFmu */.b, _hl/* sFpJ */, _hk/* sFpC */, new T(function(){
                    return E(_hu/* sFpZ */)*E(_g4/* sFlY */)+E(_hy/* sFq3 */)*E(_g5/* sFlZ */)+E(_g6/* sFm0 */);
                  }), _hj/* sFpv */, _hi/* sFpo */, new T(function(){
                    return E(_hu/* sFpZ */)*E(_g7/* sFm1 */)+E(_hy/* sFq3 */)*E(_g8/* sFm2 */)+E(_g9/* sFm3 */);
                  }), _hx/* sFq2 */.b, _hp/* sFpS */]);});
                };
                return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hg/* sFpj */.b, _ht/* sFpY */.b, _hv/* sFqz */);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hg/* sFpj */.a, _hn/* sFpQ */, _hr/* sFqA */);});
            };
            return E(_hm/* sFqB */);
          case 6:
            var _hz/* sFqF */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmt */,_gg/* sFmu */.c)), _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */));
            }),
            _hA/* sFrR */ = function(_hB/* sFqH */, _hC/* sFqI */){
              var _hD/* sFqJ */ = function(_hE/* sFqK */){
                return new F(function(){return A2(_hz/* sFqF */,E(_hE/* sFqK */).b, _hC/* sFqI */);});
              },
              _hF/* sFrQ */ = function(_hG/* sFqO */){
                var _hH/* sFqP */ = E(_hG/* sFqO */),
                _hI/* sFqQ */ = _hH/* sFqP */.a,
                _hJ/* sFqS */ = new T(function(){
                  return Math.cos/* EXTERNAL */(E(_hI/* sFqQ */));
                }),
                _hK/* sFqW */ = new T(function(){
                  return Math.sin/* EXTERNAL */(E(_hI/* sFqQ */));
                }),
                _hL/* sFr0 */ = new T(function(){
                  return  -E(_hK/* sFqW */);
                });
                return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sFmu */.b, new T(function(){
                  return E(_hJ/* sFqS */)*E(_g4/* sFlY */)+E(_hK/* sFqW */)*E(_g5/* sFlZ */);
                }), new T(function(){
                  return E(_hL/* sFr0 */)*E(_g4/* sFlY */)+E(_hJ/* sFqS */)*E(_g5/* sFlZ */);
                }), _ga/* sFm4 */, new T(function(){
                  return E(_hJ/* sFqS */)*E(_g7/* sFm1 */)+E(_hK/* sFqW */)*E(_g8/* sFm2 */);
                }), new T(function(){
                  return E(_hL/* sFr0 */)*E(_g7/* sFm1 */)+E(_hJ/* sFqS */)*E(_g8/* sFm2 */);
                }), _gb/* sFmf */, _hH/* sFqP */.b, _hD/* sFqJ */]);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_gg/* sFmu */.a, _hB/* sFqH */, _hF/* sFrQ */);});
            };
            return E(_hA/* sFrR */);
          case 7:
            var _hM/* sFrV */ = E(_gg/* sFmu */.a),
            _hN/* sFrY */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmt */,_gg/* sFmu */.c)), _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */));
            }),
            _hO/* sFsV */ = function(_hP/* sFs0 */, _hQ/* sFs1 */){
              var _hR/* sFs2 */ = function(_hS/* sFs3 */){
                return new F(function(){return A2(_hN/* sFrY */,E(_hS/* sFs3 */).b, _hQ/* sFs1 */);});
              },
              _hT/* sFsU */ = function(_hU/* sFs7 */){
                var _hV/* sFs8 */ = E(_hU/* sFs7 */),
                _hW/* sFs9 */ = _hV/* sFs8 */.a,
                _hX/* sFsb */ = new T(function(){
                  return E(_hW/* sFs9 */)*E(_g7/* sFm1 */)+0*E(_g8/* sFm2 */);
                }),
                _hY/* sFsl */ = new T(function(){
                  return E(_hW/* sFs9 */)*E(_g4/* sFlY */)+0*E(_g5/* sFlZ */);
                }),
                _hZ/* sFsT */ = function(_i0/* sFsv */){
                  var _i1/* sFsw */ = E(_i0/* sFsv */),
                  _i2/* sFsx */ = _i1/* sFsw */.a;
                  return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[_gg/* sFmu */.b, _hY/* sFsl */, new T(function(){
                    return 0*E(_g4/* sFlY */)+E(_i2/* sFsx */)*E(_g5/* sFlZ */);
                  }), _ga/* sFm4 */, _hX/* sFsb */, new T(function(){
                    return 0*E(_g7/* sFm1 */)+E(_i2/* sFsx */)*E(_g8/* sFm2 */);
                  }), _gb/* sFmf */, _i1/* sFsw */.b, _hR/* sFs2 */]);});
                };
                return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hM/* sFrV */.b, _hV/* sFs8 */.b, _hZ/* sFsT */);});
              };
              return new F(function(){return _fD/* Core.Ease.valueOf1 */(_hM/* sFrV */.a, _hP/* sFs0 */, _hT/* sFsU */);});
            };
            return E(_hO/* sFsV */);
          default:
            var _i3/* sFsZ */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(_gg/* sFmu */.b, _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */));
            }),
            _i4/* sFt0 */ = new T(function(){
              return B(_fU/* Core.Render.Internal.applyTransform_world */(B(A1(_gf/* sFmt */,_gg/* sFmu */.c)), _g4/* sFlY */, _g5/* sFlZ */, _g6/* sFm0 */, _g7/* sFm1 */, _g8/* sFm2 */, _g9/* sFm3 */));
            }),
            _i5/* sFtb */ = function(_i6/* sFt2 */){
              var _i7/* sFt3 */ = new T(function(){
                return B(A1(_i3/* sFsZ */,_i6/* sFt2 */));
              }),
              _i8/* sFta */ = function(_i9/* sFt4 */){
                return new F(function(){return A1(_i7/* sFt3 */,function(_ia/* sFt5 */){
                  return new F(function(){return A2(_i4/* sFt0 */,E(_ia/* sFt5 */).b, _i9/* sFt4 */);});
                });});
              };
              return E(_i8/* sFta */);
            };
            return E(_i5/* sFtb */);
        }
      }
    })(_fV/*  sFlX */, _fW/*  sFlY */, _fX/*  sFlZ */, _fY/*  sFm0 */, _fZ/*  sFm1 */, _g0/*  sFm2 */, _g1/*  sFm3 */));
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
_id/* $fMorphDouble_$clerp */ = function(_ie/* slbc */, _if/* slbd */, _ig/* slbe */){
  var _ih/* slbh */ = E(_ie/* slbc */);
  return E(_if/* slbd */)*(1-_ih/* slbh */)+E(_ig/* slbe */)*_ih/* slbh */;
},
_ii/* waitUntil2 */ = new T1(1,_6/* GHC.Types.[] */),
_ij/* $wa6 */ = function(_ik/* sbVt */, _il/* sbVu */, _im/* sbVv */){
  return function(_/* EXTERNAL */){
    var _in/* sbVx */ = nMV/* EXTERNAL */(_ii/* Core.World.Internal.waitUntil2 */),
    _io/* sbVz */ = _in/* sbVx */;
    return new T(function(){
      var _ip/* sbVX */ = function(_iq/* sbVJ */){
        var _ir/* sbVN */ = new T(function(){
          return B(A1(_im/* sbVv */,new T2(0,_7/* GHC.Tuple.() */,E(_iq/* sbVJ */).b)));
        }),
        _is/* sbVP */ = function(_it/* sbVQ */){
          return E(_ir/* sbVN */);
        };
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_io/* sbVz */, function(_iu/* sbVR */){
          return new T1(0,B(_9p/* Haste.Concurrent.$wa */(_cp/* Core.World.Internal.switch2 */, _is/* sbVP */)));
        })));
      },
      _iv/* sbVI */ = function(_iw/* sbVB */, _ix/* sbVC */){
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_io/* sbVz */, _7/* GHC.Tuple.() */, function(_iy/* sbVD */){
          return new F(function(){return A1(_ix/* sbVC */,new T2(0,_iy/* sbVD */,_iw/* sbVB */));});
        })));
      };
      return B(A3(_ik/* sbVt */,_iv/* sbVI */, _il/* sbVu */, _ip/* sbVX */));
    });
  };
},
_iz/* a7 */ = function(_iA/* slbp */, _iB/* slbq */, _iC/* slbr */){
  var _iD/* slbs */ = new T(function(){
    return E(E(_iA/* slbp */).b);
  });
  return new F(function(){return A1(_iC/* slbr */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,new T(function(){
    return E(E(_iA/* slbp */).a);
  }),new T4(0,new T(function(){
    return E(E(_iD/* slbs */).a);
  }),new T(function(){
    return E(E(_iD/* slbs */).b);
  }),new T(function(){
    return E(E(_iD/* slbs */).c);
  }),_av/* GHC.Types.False */))),_iB/* slbq */));});
},
_iE/* divideDouble */ = function(_iF/* s18yD */, _iG/* s18yE */){
  return E(_iF/* s18yD */)/E(_iG/* s18yE */);
},
_iH/* ease2 */ = 0,
_iI/* easeRegister1 */ = function(_iJ/* sc33 */, _iK/* sc34 */, _iL/* sc35 */, _iM/* sc36 */){
  var _iN/* sc3k */ = function(_iO/* sc38 */, _iP/* sc39 */, _iQ/* sc3a */){
    return new F(function(){return A1(_iQ/* sc3a */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
      var _iR/* sc3b */ = E(_iO/* sc38 */);
      return new T4(0,E(new T2(1,new T2(0,_iJ/* sc33 */,_iK/* sc34 */),_iR/* sc3b */.a)),_iR/* sc3b */.b,E(_iR/* sc3b */.c),E(_iR/* sc3b */.d));
    })),_iP/* sc39 */));});
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _iL/* sc35 */, _iN/* sc3k */, _iL/* sc35 */, _iM/* sc36 */]);});
},
_iS/* $weaseHandle */ = function(_iT/* slbW */, _iU/* slbX */, _iV/* slbY */, _iW/* slbZ */, _iX/* slc0 */, _iY/* slc1 */){
  var _iZ/* slc2 */ = new T(function(){
    var _j0/* slc3 */ = new T(function(){
      return B(A1(_iV/* slbY */,_2E/* GHC.Base.id */));
    }),
    _j1/* slcm */ = function(_j2/* slc4 */, _j3/* slc5 */, _j4/* slc6 */){
      var _j5/* slc7 */ = E(_j2/* slc4 */),
      _j6/* slca */ = E(_j5/* slc7 */.b),
      _j7/* slch */ = new T(function(){
        var _j8/* slcg */ = new T(function(){
          return B(A1(_j0/* slc3 */,new T(function(){
            return B(_iE/* GHC.Float.divideDouble */(_j6/* slca */.c, _iU/* slbX */));
          })));
        });
        return B(A3(_iT/* slbW */,_j8/* slcg */, _j6/* slca */.a, _j6/* slca */.b));
      });
      return new F(function(){return A1(_j4/* slc6 */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_j5/* slc7 */.a,new T4(0,_j7/* slch */,_iX/* slc0 */,_iH/* Core.Ease.ease2 */,_j6/* slca */.d))),_j3/* slc5 */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iW/* slbZ */, _j1/* slcm */));
  }),
  _j9/* slcn */ = new T(function(){
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iW/* slbZ */, _iz/* Core.Ease.a7 */));
  }),
  _ja/* slco */ = new T(function(){
    var _jb/* slcp */ = new T(function(){
      return B(A1(_iY/* slc1 */,_av/* GHC.Types.False */));
    }),
    _jc/* slcq */ = new T(function(){
      return B(A1(_iY/* slc1 */,_aw/* GHC.Types.True */));
    }),
    _jd/* slcr */ = new T(function(){
      return B(A1(_iV/* slbY */,_2E/* GHC.Base.id */));
    }),
    _je/* slde */ = function(_jf/* slcs */, _jg/* slct */, _jh/* slcu */){
      var _ji/* slcv */ = E(_jf/* slcs */),
      _jj/* slcy */ = E(_ji/* slcv */.b),
      _jk/* slcz */ = _jj/* slcy */.a,
      _jl/* slcA */ = _jj/* slcy */.b;
      if(!E(_jj/* slcy */.d)){
        var _jm/* slcE */ = E(_iU/* slbX */),
        _jn/* slcI */ = E(_jj/* slcy */.c)+1,
        _jo/* slcJ */ = function(_jp/* slcK */, _jq/* slcL */){
          var _jr/* slcM */ = new T(function(){
            var _js/* slcP */ = new T(function(){
              return B(A1(_jd/* slcr */,new T(function(){
                return _jp/* slcK *//_jm/* slcE */;
              })));
            });
            return B(A3(_iT/* slbW */,_js/* slcP */, _jk/* slcz */, _jl/* slcA */));
          }),
          _jt/* slcQ */ = new T4(0,_jk/* slcz */,_jl/* slcA */,_jq/* slcL */,_aw/* GHC.Types.True */);
          if(_jp/* slcK */>=_jm/* slcE */){
            return new F(function(){return A2(_jc/* slcq */,_jg/* slct */, function(_ju/* slcV */){
              return new F(function(){return A1(_jh/* slcu */,new T2(0,new T2(0,_av/* GHC.Types.False */,new T2(0,_jr/* slcM */,_jt/* slcQ */)),E(_ju/* slcV */).b));});
            });});
          }else{
            return new F(function(){return A1(_jh/* slcu */,new T2(0,new T2(0,_aw/* GHC.Types.True */,new T2(0,_jr/* slcM */,_jt/* slcQ */)),_jg/* slct */));});
          }
        };
        if(_jm/* slcE */>_jn/* slcI */){
          return new F(function(){return _jo/* slcJ */(_jn/* slcI */, _jn/* slcI */);});
        }else{
          return new F(function(){return _jo/* slcJ */(_jm/* slcE */, _jm/* slcE */);});
        }
      }else{
        return new F(function(){return A2(_jb/* slcp */,_jg/* slct */, function(_jv/* sld8 */){
          return new F(function(){return A1(_jh/* slcu */,new T2(0,new T2(0,_av/* GHC.Types.False */,_ji/* slcv */),E(_jv/* sld8 */).b));});
        });});
      }
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iW/* slbZ */, _je/* slde */));
  }),
  _jw/* sldo */ = function(_jx/* sldf */){
    var _jy/* sldg */ = new T(function(){
      return B(A1(_iZ/* slc2 */,_jx/* sldf */));
    }),
    _jz/* sldn */ = function(_jA/* sldh */){
      return new F(function(){return A1(_jy/* sldg */,function(_jB/* sldi */){
        return new F(function(){return _iI/* Core.World.Internal.easeRegister1 */(_j9/* slcn */, _ja/* slco */, E(_jB/* sldi */).b, _jA/* sldh */);});
      });});
    };
    return E(_jz/* sldn */);
  };
  return E(_jw/* sldo */);
},
_jC/* forceTo_b1 */ = 1,
_jD/* $wforceTo */ = function(_jE/* skZM */, _jF/* skZN */){
  var _jG/* skZO */ = new T(function(){
    var _jH/* sl05 */ = function(_jI/* skZP */, _jJ/* skZQ */, _jK/* skZR */){
      return new F(function(){return A1(_jK/* skZR */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_jF/* skZN */,new T4(0,_jF/* skZN */,_jF/* skZN */,_jC/* Core.Ease.forceTo_b1 */,new T(function(){
        return E(E(E(_jI/* skZP */).b).d);
      })))),_jJ/* skZQ */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _jE/* skZM */, _jH/* sl05 */));
  }),
  _jL/* sl0w */ = function(_jM/* sl06 */, _jN/* sl07 */){
    var _jO/* sl08 */ = new T(function(){
      return B(A2(_jG/* skZO */,_jM/* sl06 */, _jN/* sl07 */));
    }),
    _jP/* sl0t */ = function(_jQ/* sl09 */){
      var _jR/* sl0a */ = new T(function(){
        var _jS/* sl0b */ = E(_jQ/* sl09 */),
        _jT/* sl0e */ = E(_jS/* sl0b */.a),
        _jU/* sl0f */ = E(_jS/* sl0b */.b),
        _jV/* sl0k */ = E(_jU/* sl0f */.a),
        _jW/* sl0l */ = E(_jU/* sl0f */.b),
        _jX/* sl0n */ = E(_jU/* sl0f */.c),
        _jY/* sl0o */ = E(_jU/* sl0f */.d);
        return E(_jO/* sl08 */);
      });
      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_jE/* skZM */, _jQ/* sl09 */, function(_jZ/* sl0p */){
        return E(_jR/* sl0a */);
      })));
    };
    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_jE/* skZM */, _jP/* sl0t */)));
  };
  return E(_jL/* sl0w */);
},
_k0/* $fAffineShape2 */ = function(_k1/* stet */, _k2/* steu */, _k3/* stev */, _k4/* stew */, _/* EXTERNAL */){
  var _k5/* stey */ = E(_k1/* stet */);
  switch(_k5/* stey */._){
    case 0:
      return new F(function(){return A(_k2/* steu */,[_k5/* stey */.a, _k3/* stev */, _k4/* stew */, _/* EXTERNAL */]);});
      break;
    case 1:
      var _k6/* steB */ = B(A1(_k5/* stey */.a,_/* EXTERNAL */));
      return new F(function(){return A(_k2/* steu */,[_k6/* steB */, _k3/* stev */, _k4/* stew */, _/* EXTERNAL */]);});
      break;
    case 2:
      var _k7/* steM */ = rMV/* EXTERNAL */(E(E(_k5/* stey */.a).c)),
      _k8/* steP */ = E(_k7/* steM */);
      if(!_k8/* steP */._){
        var _k9/* steT */ = new T(function(){
          return B(A1(_k5/* stey */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_k8/* steP */.a));
          })));
        });
        return new F(function(){return A(_k2/* steu */,[_k9/* steT */, _k3/* stev */, _k4/* stew */, _/* EXTERNAL */]);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _ka/* stf3 */ = rMV/* EXTERNAL */(E(E(_k5/* stey */.a).c)),
      _kb/* stf6 */ = E(_ka/* stf3 */);
      if(!_kb/* stf6 */._){
        var _kc/* stfc */ = B(A2(_k5/* stey */.b,E(_kb/* stf6 */.a).a, _/* EXTERNAL */));
        return new F(function(){return A(_k2/* steu */,[_kc/* stfc */, _k3/* stev */, _k4/* stew */, _/* EXTERNAL */]);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
  }
},
_kd/* $fAffineShape3 */ = function(_ke/* stfg */, _kf/* stfh */, _/* EXTERNAL */){
  var _kg/* stfj */ = E(_ke/* stfg */);
  switch(_kg/* stfj */._){
    case 0:
      return new F(function(){return A2(_kf/* stfh */,_kg/* stfj */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _kh/* stfm */ = B(A1(_kg/* stfj */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_kf/* stfh */,_kh/* stfm */, _/* EXTERNAL */);});
      break;
    case 2:
      var _ki/* stfx */ = rMV/* EXTERNAL */(E(E(_kg/* stfj */.a).c)),
      _kj/* stfA */ = E(_ki/* stfx */);
      if(!_kj/* stfA */._){
        var _kk/* stfE */ = new T(function(){
          return B(A1(_kg/* stfj */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_kj/* stfA */.a));
          })));
        });
        return new F(function(){return A2(_kf/* stfh */,_kk/* stfE */, _/* EXTERNAL */);});
      }else{
        return _av/* GHC.Types.False */;
      }
      break;
    default:
      var _kl/* stfO */ = rMV/* EXTERNAL */(E(E(_kg/* stfj */.a).c)),
      _km/* stfR */ = E(_kl/* stfO */);
      if(!_km/* stfR */._){
        var _kn/* stfX */ = B(A2(_kg/* stfj */.b,E(_km/* stfR */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_kf/* stfh */,_kn/* stfX */, _/* EXTERNAL */);});
      }else{
        return _av/* GHC.Types.False */;
      }
  }
},
_ko/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _7/* GHC.Tuple.() */;
},
_kp/* bezier_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.moveTo(x,y);})");
}),
_kq/* line_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.lineTo(x,y);})");
}),
_kr/* $wrect */ = function(_ks/* stAy */, _kt/* stAz */, _ku/* stAA */, _kv/* stAB */){
  var _kw/* stCD */ = function(_kx/* stBA */, _ky/* stBB */, _kz/* stBC */, _/* EXTERNAL */){
    var _kA/* stCC */ = function(_kB/* stBE */, _kC/* stBF */, _kD/* stBG */, _/* EXTERNAL */){
      var _kE/* stCB */ = function(_kF/* stBI */, _kG/* stBJ */, _kH/* stBK */, _/* EXTERNAL */){
        return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_kv/* stAB */, function(_kI/* stBM */, _kJ/* stBN */, _kK/* stBO */, _/* EXTERNAL */){
          var _kL/* stBQ */ = E(_kx/* stBA */),
          _kM/* stBU */ = E(_kB/* stBE */),
          _kN/* stBY */ = E(_kJ/* stBN */),
          _kO/* stC2 */ = E(_kK/* stBO */),
          _kP/* stC5 */ = __app4/* EXTERNAL */(E(_kp/* Core.Shape.Internal.bezier_f2 */), _kL/* stBQ */, _kM/* stBU */, _kN/* stBY */, _kO/* stC2 */),
          _kQ/* stCa */ = _kL/* stBQ */+E(_kF/* stBI */),
          _kR/* stCd */ = E(_kq/* Core.Shape.Internal.line_f1 */),
          _kS/* stCg */ = __app4/* EXTERNAL */(_kR/* stCd */, _kQ/* stCa */, _kM/* stBU */, _kN/* stBY */, _kO/* stC2 */),
          _kT/* stCl */ = _kM/* stBU */+E(_kI/* stBM */),
          _kU/* stCp */ = __app4/* EXTERNAL */(_kR/* stCd */, _kQ/* stCa */, _kT/* stCl */, _kN/* stBY */, _kO/* stC2 */),
          _kV/* stCt */ = __app4/* EXTERNAL */(_kR/* stCd */, _kL/* stBQ */, _kT/* stCl */, _kN/* stBY */, _kO/* stC2 */),
          _kW/* stCx */ = __app4/* EXTERNAL */(_kR/* stCd */, _kL/* stBQ */, _kM/* stBU */, _kN/* stBY */, _kO/* stC2 */);
          return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _kG/* stBJ */, _kH/* stBK */, _/* EXTERNAL */);});
      };
      return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_ku/* stAA */, _kE/* stCB */, _kC/* stBF */, _kD/* stBG */, _/* EXTERNAL */);});
    };
    return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_kt/* stAz */, _kA/* stCC */, _ky/* stBB */, _kz/* stBC */, _/* EXTERNAL */);});
  },
  _kX/* stBz */ = function(_kY/* stAC */, _/* EXTERNAL */){
    var _kZ/* stAE */ = E(_kY/* stAC */),
    _l0/* stBy */ = function(_l1/* stAH */, _/* EXTERNAL */){
      var _l2/* stBx */ = function(_l3/* stAJ */, _/* EXTERNAL */){
        var _l4/* stBw */ = function(_l5/* stAL */, _/* EXTERNAL */){
          var _l6/* stBv */ = function(_l7/* stAN */, _/* EXTERNAL */){
            return new T(function(){
              var _l8/* stAT */ = E(_l5/* stAL */),
              _l9/* stAV */ = function(_la/* stAW */){
                var _lb/* stB1 */ = E(_l7/* stAN */),
                _lc/* stB5 */ = E(_kZ/* stAE */.b)-E(_l3/* stAJ */)-_lb/* stB1 *//2;
                return (_lc/* stB5 */==0) ? 0<_lb/* stB1 *//2 : (_lc/* stB5 */<=0) ?  -_lc/* stB5 */<_lb/* stB1 *//2 : _lc/* stB5 */<_lb/* stB1 *//2;
              },
              _ld/* stBh */ = E(_kZ/* stAE */.a)-E(_l1/* stAH */)-_l8/* stAT *//2;
              if(!_ld/* stBh */){
                if(0>=_l8/* stAT *//2){
                  return false;
                }else{
                  return B(_l9/* stAV */(_/* EXTERNAL */));
                }
              }else{
                if(_ld/* stBh */<=0){
                  if( -_ld/* stBh */>=_l8/* stAT *//2){
                    return false;
                  }else{
                    return B(_l9/* stAV */(_/* EXTERNAL */));
                  }
                }else{
                  if(_ld/* stBh */>=_l8/* stAT *//2){
                    return false;
                  }else{
                    return B(_l9/* stAV */(_/* EXTERNAL */));
                  }
                }
              }
            });
          };
          return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_kv/* stAB */, _l6/* stBv */, _/* EXTERNAL */);});
        };
        return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_ku/* stAA */, _l4/* stBw */, _/* EXTERNAL */);});
      };
      return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_kt/* stAz */, _l2/* stBx */, _/* EXTERNAL */);});
    };
    return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_ks/* stAy */, _l0/* stBy */, _/* EXTERNAL */);});
  };
  return new T3(0,_kX/* stBz */,function(_le/* B3 */, _lf/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_ks/* stAy */, _kw/* stCD */, _le/* B3 */, _lf/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_lg/* a */ = 100,
_lh/* a4 */ = function(_li/* sNuv */, _lj/* sNuw */){
  var _lk/* sNuC */ = B(A1(_li/* sNuv */,new T(function(){
    return 1-(1-E(_lj/* sNuw */));
  })));
  return 1-(1-_lk/* sNuC */*_lk/* sNuC */);
},
_ll/* dur */ = 20,
_lm/* e */ = function(_ln/* sNul */, _lo/* sNum */){
  var _lp/* sNur */ = B(A1(_ln/* sNul */,new T(function(){
    return 1-E(_lo/* sNum */);
  })));
  return 1-_lp/* sNur */*_lp/* sNur */;
},
_lq/* easeIn */ = function(_lr/* skZK */, _ls/* skZL */){
  return new F(function(){return A1(_lr/* skZK */,_ls/* skZL */);});
},
_lt/* $wa */ = function(_lu/* sFyy */, _lv/* sFyz */, _lw/* sFyA */, _lx/* sFyB */, _/* EXTERNAL */){
  var _ly/* sFyD */ = function(_/* EXTERNAL */, _lz/* sFyF */){
    var _lA/* sFyG */ = function(_/* EXTERNAL */, _lB/* sFyI */){
      var _lC/* sFyJ */ = function(_/* EXTERNAL */, _lD/* sFyL */){
        var _lE/* sFyM */ = E(_lx/* sFyB */);
        switch(_lE/* sFyM */._){
          case 0:
            return new T(function(){
              var _lF/* sFyO */ = function(_lG/* sFyP */){
                var _lH/* sFyQ */ = _lG/* sFyP */*256,
                _lI/* sFyR */ = _lH/* sFyQ */&4294967295,
                _lJ/* sFyS */ = function(_lK/* sFyT */){
                  var _lL/* sFyW */ = E(_lB/* sFyI */)*256,
                  _lM/* sFyX */ = _lL/* sFyW */&4294967295,
                  _lN/* sFyY */ = function(_lO/* sFyZ */){
                    var _lP/* sFz0 */ = function(_lQ/* sFz1 */){
                      var _lR/* sFz2 */ = _lQ/* sFz1 */*256,
                      _lS/* sFz3 */ = _lR/* sFz2 */&4294967295,
                      _lT/* sFz4 */ = function(_lU/* sFz5 */){
                        var _lV/* sFz6 */ = E(_lE/* sFyM */.a);
                        return (1>_lV/* sFz6 */) ? (0>_lV/* sFz6 */) ? new T4(1,_lK/* sFyT */,_lO/* sFyZ */,_lU/* sFz5 */,0) : new T4(1,_lK/* sFyT */,_lO/* sFyZ */,_lU/* sFz5 */,_lV/* sFz6 */) : new T4(1,_lK/* sFyT */,_lO/* sFyZ */,_lU/* sFz5 */,1);
                      };
                      if(_lR/* sFz2 */>=_lS/* sFz3 */){
                        if(255>_lS/* sFz3 */){
                          if(0>_lS/* sFz3 */){
                            return new F(function(){return _lT/* sFz4 */(0);});
                          }else{
                            return new F(function(){return _lT/* sFz4 */(_lS/* sFz3 */);});
                          }
                        }else{
                          return new F(function(){return _lT/* sFz4 */(255);});
                        }
                      }else{
                        var _lW/* sFzj */ = _lS/* sFz3 */-1|0;
                        if(255>_lW/* sFzj */){
                          if(0>_lW/* sFzj */){
                            return new F(function(){return _lT/* sFz4 */(0);});
                          }else{
                            return new F(function(){return _lT/* sFz4 */(_lW/* sFzj */);});
                          }
                        }else{
                          return new F(function(){return _lT/* sFz4 */(255);});
                        }
                      }
                    },
                    _lX/* sFzo */ = E(_lD/* sFyL */);
                    if(!_lX/* sFzo */._){
                      return new F(function(){return _lP/* sFz0 */(0);});
                    }else{
                      return new F(function(){return _lP/* sFz0 */(E(_lX/* sFzo */.a));});
                    }
                  };
                  if(_lL/* sFyW */>=_lM/* sFyX */){
                    if(255>_lM/* sFyX */){
                      if(0>_lM/* sFyX */){
                        return new F(function(){return _lN/* sFyY */(0);});
                      }else{
                        return new F(function(){return _lN/* sFyY */(_lM/* sFyX */);});
                      }
                    }else{
                      return new F(function(){return _lN/* sFyY */(255);});
                    }
                  }else{
                    var _lY/* sFzz */ = _lM/* sFyX */-1|0;
                    if(255>_lY/* sFzz */){
                      if(0>_lY/* sFzz */){
                        return new F(function(){return _lN/* sFyY */(0);});
                      }else{
                        return new F(function(){return _lN/* sFyY */(_lY/* sFzz */);});
                      }
                    }else{
                      return new F(function(){return _lN/* sFyY */(255);});
                    }
                  }
                };
                if(_lH/* sFyQ */>=_lI/* sFyR */){
                  if(255>_lI/* sFyR */){
                    if(0>_lI/* sFyR */){
                      return new F(function(){return _lJ/* sFyS */(0);});
                    }else{
                      return new F(function(){return _lJ/* sFyS */(_lI/* sFyR */);});
                    }
                  }else{
                    return new F(function(){return _lJ/* sFyS */(255);});
                  }
                }else{
                  var _lZ/* sFzL */ = _lI/* sFyR */-1|0;
                  if(255>_lZ/* sFzL */){
                    if(0>_lZ/* sFzL */){
                      return new F(function(){return _lJ/* sFyS */(0);});
                    }else{
                      return new F(function(){return _lJ/* sFyS */(_lZ/* sFzL */);});
                    }
                  }else{
                    return new F(function(){return _lJ/* sFyS */(255);});
                  }
                }
              },
              _m0/* sFzQ */ = E(_lz/* sFyF */);
              if(!_m0/* sFzQ */._){
                return B(_lF/* sFyO */(0));
              }else{
                return B(_lF/* sFyO */(E(_m0/* sFzQ */.a)));
              }
            });
          case 1:
            var _m1/* sFzW */ = B(A1(_lE/* sFyM */.a,_/* EXTERNAL */)),
            _m2/* sFzY */ = _m1/* sFzW */;
            return new T(function(){
              var _m3/* sFzZ */ = function(_m4/* sFA0 */){
                var _m5/* sFA1 */ = _m4/* sFA0 */*256,
                _m6/* sFA2 */ = _m5/* sFA1 */&4294967295,
                _m7/* sFA3 */ = function(_m8/* sFA4 */){
                  var _m9/* sFA7 */ = E(_lB/* sFyI */)*256,
                  _ma/* sFA8 */ = _m9/* sFA7 */&4294967295,
                  _mb/* sFA9 */ = function(_mc/* sFAa */){
                    var _md/* sFAb */ = function(_me/* sFAc */){
                      var _mf/* sFAd */ = _me/* sFAc */*256,
                      _mg/* sFAe */ = _mf/* sFAd */&4294967295,
                      _mh/* sFAf */ = function(_mi/* sFAg */){
                        var _mj/* sFAh */ = E(_m2/* sFzY */);
                        return (1>_mj/* sFAh */) ? (0>_mj/* sFAh */) ? new T4(1,_m8/* sFA4 */,_mc/* sFAa */,_mi/* sFAg */,0) : new T4(1,_m8/* sFA4 */,_mc/* sFAa */,_mi/* sFAg */,_mj/* sFAh */) : new T4(1,_m8/* sFA4 */,_mc/* sFAa */,_mi/* sFAg */,1);
                      };
                      if(_mf/* sFAd */>=_mg/* sFAe */){
                        if(255>_mg/* sFAe */){
                          if(0>_mg/* sFAe */){
                            return new F(function(){return _mh/* sFAf */(0);});
                          }else{
                            return new F(function(){return _mh/* sFAf */(_mg/* sFAe */);});
                          }
                        }else{
                          return new F(function(){return _mh/* sFAf */(255);});
                        }
                      }else{
                        var _mk/* sFAu */ = _mg/* sFAe */-1|0;
                        if(255>_mk/* sFAu */){
                          if(0>_mk/* sFAu */){
                            return new F(function(){return _mh/* sFAf */(0);});
                          }else{
                            return new F(function(){return _mh/* sFAf */(_mk/* sFAu */);});
                          }
                        }else{
                          return new F(function(){return _mh/* sFAf */(255);});
                        }
                      }
                    },
                    _ml/* sFAz */ = E(_lD/* sFyL */);
                    if(!_ml/* sFAz */._){
                      return new F(function(){return _md/* sFAb */(0);});
                    }else{
                      return new F(function(){return _md/* sFAb */(E(_ml/* sFAz */.a));});
                    }
                  };
                  if(_m9/* sFA7 */>=_ma/* sFA8 */){
                    if(255>_ma/* sFA8 */){
                      if(0>_ma/* sFA8 */){
                        return new F(function(){return _mb/* sFA9 */(0);});
                      }else{
                        return new F(function(){return _mb/* sFA9 */(_ma/* sFA8 */);});
                      }
                    }else{
                      return new F(function(){return _mb/* sFA9 */(255);});
                    }
                  }else{
                    var _mm/* sFAK */ = _ma/* sFA8 */-1|0;
                    if(255>_mm/* sFAK */){
                      if(0>_mm/* sFAK */){
                        return new F(function(){return _mb/* sFA9 */(0);});
                      }else{
                        return new F(function(){return _mb/* sFA9 */(_mm/* sFAK */);});
                      }
                    }else{
                      return new F(function(){return _mb/* sFA9 */(255);});
                    }
                  }
                };
                if(_m5/* sFA1 */>=_m6/* sFA2 */){
                  if(255>_m6/* sFA2 */){
                    if(0>_m6/* sFA2 */){
                      return new F(function(){return _m7/* sFA3 */(0);});
                    }else{
                      return new F(function(){return _m7/* sFA3 */(_m6/* sFA2 */);});
                    }
                  }else{
                    return new F(function(){return _m7/* sFA3 */(255);});
                  }
                }else{
                  var _mn/* sFAW */ = _m6/* sFA2 */-1|0;
                  if(255>_mn/* sFAW */){
                    if(0>_mn/* sFAW */){
                      return new F(function(){return _m7/* sFA3 */(0);});
                    }else{
                      return new F(function(){return _m7/* sFA3 */(_mn/* sFAW */);});
                    }
                  }else{
                    return new F(function(){return _m7/* sFA3 */(255);});
                  }
                }
              },
              _mo/* sFB1 */ = E(_lz/* sFyF */);
              if(!_mo/* sFB1 */._){
                return B(_m3/* sFzZ */(0));
              }else{
                return B(_m3/* sFzZ */(E(_mo/* sFB1 */.a)));
              }
            });
          case 2:
            var _mp/* sFBe */ = rMV/* EXTERNAL */(E(E(_lE/* sFyM */.a).c)),
            _mq/* sFBh */ = E(_mp/* sFBe */);
            return (_mq/* sFBh */._==0) ? new T(function(){
              var _mr/* sFBk */ = function(_ms/* sFBl */){
                var _mt/* sFBm */ = _ms/* sFBl */*256,
                _mu/* sFBn */ = _mt/* sFBm */&4294967295,
                _mv/* sFBo */ = function(_mw/* sFBp */){
                  var _mx/* sFBs */ = E(_lB/* sFyI */)*256,
                  _my/* sFBt */ = _mx/* sFBs */&4294967295,
                  _mz/* sFBu */ = function(_mA/* sFBv */){
                    var _mB/* sFBw */ = function(_mC/* sFBx */){
                      var _mD/* sFBy */ = _mC/* sFBx */*256,
                      _mE/* sFBz */ = _mD/* sFBy */&4294967295,
                      _mF/* sFBA */ = function(_mG/* sFBB */){
                        var _mH/* sFBD */ = B(A1(_lE/* sFyM */.b,new T(function(){
                          return B(_fB/* Data.Tuple.fst */(_mq/* sFBh */.a));
                        })));
                        return (1>_mH/* sFBD */) ? (0>_mH/* sFBD */) ? new T4(1,_mw/* sFBp */,_mA/* sFBv */,_mG/* sFBB */,0) : new T4(1,_mw/* sFBp */,_mA/* sFBv */,_mG/* sFBB */,_mH/* sFBD */) : new T4(1,_mw/* sFBp */,_mA/* sFBv */,_mG/* sFBB */,1);
                      };
                      if(_mD/* sFBy */>=_mE/* sFBz */){
                        if(255>_mE/* sFBz */){
                          if(0>_mE/* sFBz */){
                            return new F(function(){return _mF/* sFBA */(0);});
                          }else{
                            return new F(function(){return _mF/* sFBA */(_mE/* sFBz */);});
                          }
                        }else{
                          return new F(function(){return _mF/* sFBA */(255);});
                        }
                      }else{
                        var _mI/* sFBQ */ = _mE/* sFBz */-1|0;
                        if(255>_mI/* sFBQ */){
                          if(0>_mI/* sFBQ */){
                            return new F(function(){return _mF/* sFBA */(0);});
                          }else{
                            return new F(function(){return _mF/* sFBA */(_mI/* sFBQ */);});
                          }
                        }else{
                          return new F(function(){return _mF/* sFBA */(255);});
                        }
                      }
                    },
                    _mJ/* sFBV */ = E(_lD/* sFyL */);
                    if(!_mJ/* sFBV */._){
                      return new F(function(){return _mB/* sFBw */(0);});
                    }else{
                      return new F(function(){return _mB/* sFBw */(E(_mJ/* sFBV */.a));});
                    }
                  };
                  if(_mx/* sFBs */>=_my/* sFBt */){
                    if(255>_my/* sFBt */){
                      if(0>_my/* sFBt */){
                        return new F(function(){return _mz/* sFBu */(0);});
                      }else{
                        return new F(function(){return _mz/* sFBu */(_my/* sFBt */);});
                      }
                    }else{
                      return new F(function(){return _mz/* sFBu */(255);});
                    }
                  }else{
                    var _mK/* sFC6 */ = _my/* sFBt */-1|0;
                    if(255>_mK/* sFC6 */){
                      if(0>_mK/* sFC6 */){
                        return new F(function(){return _mz/* sFBu */(0);});
                      }else{
                        return new F(function(){return _mz/* sFBu */(_mK/* sFC6 */);});
                      }
                    }else{
                      return new F(function(){return _mz/* sFBu */(255);});
                    }
                  }
                };
                if(_mt/* sFBm */>=_mu/* sFBn */){
                  if(255>_mu/* sFBn */){
                    if(0>_mu/* sFBn */){
                      return new F(function(){return _mv/* sFBo */(0);});
                    }else{
                      return new F(function(){return _mv/* sFBo */(_mu/* sFBn */);});
                    }
                  }else{
                    return new F(function(){return _mv/* sFBo */(255);});
                  }
                }else{
                  var _mL/* sFCi */ = _mu/* sFBn */-1|0;
                  if(255>_mL/* sFCi */){
                    if(0>_mL/* sFCi */){
                      return new F(function(){return _mv/* sFBo */(0);});
                    }else{
                      return new F(function(){return _mv/* sFBo */(_mL/* sFCi */);});
                    }
                  }else{
                    return new F(function(){return _mv/* sFBo */(255);});
                  }
                }
              },
              _mM/* sFCn */ = E(_lz/* sFyF */);
              if(!_mM/* sFCn */._){
                return B(_mr/* sFBk */(0));
              }else{
                return B(_mr/* sFBk */(E(_mM/* sFCn */.a)));
              }
            }) : new T(function(){
              var _mN/* sFCt */ = function(_mO/* sFCu */){
                var _mP/* sFCv */ = _mO/* sFCu */*256,
                _mQ/* sFCw */ = _mP/* sFCv */&4294967295,
                _mR/* sFCx */ = function(_mS/* sFCy */){
                  var _mT/* sFCB */ = E(_lB/* sFyI */)*256,
                  _mU/* sFCC */ = _mT/* sFCB */&4294967295,
                  _mV/* sFCD */ = function(_mW/* sFCE */){
                    var _mX/* sFCF */ = function(_mY/* sFCG */){
                      var _mZ/* sFCH */ = _mY/* sFCG */*256,
                      _n0/* sFCI */ = _mZ/* sFCH */&4294967295;
                      if(_mZ/* sFCH */>=_n0/* sFCI */){
                        return (255>_n0/* sFCI */) ? (0>_n0/* sFCI */) ? new T4(1,_mS/* sFCy */,_mW/* sFCE */,0,1) : new T4(1,_mS/* sFCy */,_mW/* sFCE */,_n0/* sFCI */,1) : new T4(1,_mS/* sFCy */,_mW/* sFCE */,255,1);
                      }else{
                        var _n1/* sFCQ */ = _n0/* sFCI */-1|0;
                        return (255>_n1/* sFCQ */) ? (0>_n1/* sFCQ */) ? new T4(1,_mS/* sFCy */,_mW/* sFCE */,0,1) : new T4(1,_mS/* sFCy */,_mW/* sFCE */,_n1/* sFCQ */,1) : new T4(1,_mS/* sFCy */,_mW/* sFCE */,255,1);
                      }
                    },
                    _n2/* sFCV */ = E(_lD/* sFyL */);
                    if(!_n2/* sFCV */._){
                      return new F(function(){return _mX/* sFCF */(0);});
                    }else{
                      return new F(function(){return _mX/* sFCF */(E(_n2/* sFCV */.a));});
                    }
                  };
                  if(_mT/* sFCB */>=_mU/* sFCC */){
                    if(255>_mU/* sFCC */){
                      if(0>_mU/* sFCC */){
                        return new F(function(){return _mV/* sFCD */(0);});
                      }else{
                        return new F(function(){return _mV/* sFCD */(_mU/* sFCC */);});
                      }
                    }else{
                      return new F(function(){return _mV/* sFCD */(255);});
                    }
                  }else{
                    var _n3/* sFD6 */ = _mU/* sFCC */-1|0;
                    if(255>_n3/* sFD6 */){
                      if(0>_n3/* sFD6 */){
                        return new F(function(){return _mV/* sFCD */(0);});
                      }else{
                        return new F(function(){return _mV/* sFCD */(_n3/* sFD6 */);});
                      }
                    }else{
                      return new F(function(){return _mV/* sFCD */(255);});
                    }
                  }
                };
                if(_mP/* sFCv */>=_mQ/* sFCw */){
                  if(255>_mQ/* sFCw */){
                    if(0>_mQ/* sFCw */){
                      return new F(function(){return _mR/* sFCx */(0);});
                    }else{
                      return new F(function(){return _mR/* sFCx */(_mQ/* sFCw */);});
                    }
                  }else{
                    return new F(function(){return _mR/* sFCx */(255);});
                  }
                }else{
                  var _n4/* sFDi */ = _mQ/* sFCw */-1|0;
                  if(255>_n4/* sFDi */){
                    if(0>_n4/* sFDi */){
                      return new F(function(){return _mR/* sFCx */(0);});
                    }else{
                      return new F(function(){return _mR/* sFCx */(_n4/* sFDi */);});
                    }
                  }else{
                    return new F(function(){return _mR/* sFCx */(255);});
                  }
                }
              },
              _n5/* sFDn */ = E(_lz/* sFyF */);
              if(!_n5/* sFDn */._){
                return B(_mN/* sFCt */(0));
              }else{
                return B(_mN/* sFCt */(E(_n5/* sFDn */.a)));
              }
            });
          default:
            var _n6/* sFDA */ = rMV/* EXTERNAL */(E(E(_lE/* sFyM */.a).c)),
            _n7/* sFDD */ = E(_n6/* sFDA */);
            if(!_n7/* sFDD */._){
              var _n8/* sFDJ */ = B(A2(_lE/* sFyM */.b,E(_n7/* sFDD */.a).a, _/* EXTERNAL */)),
              _n9/* sFDL */ = _n8/* sFDJ */;
              return new T(function(){
                var _na/* sFDM */ = function(_nb/* sFDN */){
                  var _nc/* sFDO */ = _nb/* sFDN */*256,
                  _nd/* sFDP */ = _nc/* sFDO */&4294967295,
                  _ne/* sFDQ */ = function(_nf/* sFDR */){
                    var _ng/* sFDU */ = E(_lB/* sFyI */)*256,
                    _nh/* sFDV */ = _ng/* sFDU */&4294967295,
                    _ni/* sFDW */ = function(_nj/* sFDX */){
                      var _nk/* sFDY */ = function(_nl/* sFDZ */){
                        var _nm/* sFE0 */ = _nl/* sFDZ */*256,
                        _nn/* sFE1 */ = _nm/* sFE0 */&4294967295,
                        _no/* sFE2 */ = function(_np/* sFE3 */){
                          var _nq/* sFE4 */ = E(_n9/* sFDL */);
                          return (1>_nq/* sFE4 */) ? (0>_nq/* sFE4 */) ? new T4(1,_nf/* sFDR */,_nj/* sFDX */,_np/* sFE3 */,0) : new T4(1,_nf/* sFDR */,_nj/* sFDX */,_np/* sFE3 */,_nq/* sFE4 */) : new T4(1,_nf/* sFDR */,_nj/* sFDX */,_np/* sFE3 */,1);
                        };
                        if(_nm/* sFE0 */>=_nn/* sFE1 */){
                          if(255>_nn/* sFE1 */){
                            if(0>_nn/* sFE1 */){
                              return new F(function(){return _no/* sFE2 */(0);});
                            }else{
                              return new F(function(){return _no/* sFE2 */(_nn/* sFE1 */);});
                            }
                          }else{
                            return new F(function(){return _no/* sFE2 */(255);});
                          }
                        }else{
                          var _nr/* sFEh */ = _nn/* sFE1 */-1|0;
                          if(255>_nr/* sFEh */){
                            if(0>_nr/* sFEh */){
                              return new F(function(){return _no/* sFE2 */(0);});
                            }else{
                              return new F(function(){return _no/* sFE2 */(_nr/* sFEh */);});
                            }
                          }else{
                            return new F(function(){return _no/* sFE2 */(255);});
                          }
                        }
                      },
                      _ns/* sFEm */ = E(_lD/* sFyL */);
                      if(!_ns/* sFEm */._){
                        return new F(function(){return _nk/* sFDY */(0);});
                      }else{
                        return new F(function(){return _nk/* sFDY */(E(_ns/* sFEm */.a));});
                      }
                    };
                    if(_ng/* sFDU */>=_nh/* sFDV */){
                      if(255>_nh/* sFDV */){
                        if(0>_nh/* sFDV */){
                          return new F(function(){return _ni/* sFDW */(0);});
                        }else{
                          return new F(function(){return _ni/* sFDW */(_nh/* sFDV */);});
                        }
                      }else{
                        return new F(function(){return _ni/* sFDW */(255);});
                      }
                    }else{
                      var _nt/* sFEx */ = _nh/* sFDV */-1|0;
                      if(255>_nt/* sFEx */){
                        if(0>_nt/* sFEx */){
                          return new F(function(){return _ni/* sFDW */(0);});
                        }else{
                          return new F(function(){return _ni/* sFDW */(_nt/* sFEx */);});
                        }
                      }else{
                        return new F(function(){return _ni/* sFDW */(255);});
                      }
                    }
                  };
                  if(_nc/* sFDO */>=_nd/* sFDP */){
                    if(255>_nd/* sFDP */){
                      if(0>_nd/* sFDP */){
                        return new F(function(){return _ne/* sFDQ */(0);});
                      }else{
                        return new F(function(){return _ne/* sFDQ */(_nd/* sFDP */);});
                      }
                    }else{
                      return new F(function(){return _ne/* sFDQ */(255);});
                    }
                  }else{
                    var _nu/* sFEJ */ = _nd/* sFDP */-1|0;
                    if(255>_nu/* sFEJ */){
                      if(0>_nu/* sFEJ */){
                        return new F(function(){return _ne/* sFDQ */(0);});
                      }else{
                        return new F(function(){return _ne/* sFDQ */(_nu/* sFEJ */);});
                      }
                    }else{
                      return new F(function(){return _ne/* sFDQ */(255);});
                    }
                  }
                },
                _nv/* sFEO */ = E(_lz/* sFyF */);
                if(!_nv/* sFEO */._){
                  return B(_na/* sFDM */(0));
                }else{
                  return B(_na/* sFDM */(E(_nv/* sFEO */.a)));
                }
              });
            }else{
              return new T(function(){
                var _nw/* sFEU */ = function(_nx/* sFEV */){
                  var _ny/* sFEW */ = _nx/* sFEV */*256,
                  _nz/* sFEX */ = _ny/* sFEW */&4294967295,
                  _nA/* sFEY */ = function(_nB/* sFEZ */){
                    var _nC/* sFF2 */ = E(_lB/* sFyI */)*256,
                    _nD/* sFF3 */ = _nC/* sFF2 */&4294967295,
                    _nE/* sFF4 */ = function(_nF/* sFF5 */){
                      var _nG/* sFF6 */ = function(_nH/* sFF7 */){
                        var _nI/* sFF8 */ = _nH/* sFF7 */*256,
                        _nJ/* sFF9 */ = _nI/* sFF8 */&4294967295;
                        if(_nI/* sFF8 */>=_nJ/* sFF9 */){
                          return (255>_nJ/* sFF9 */) ? (0>_nJ/* sFF9 */) ? new T4(1,_nB/* sFEZ */,_nF/* sFF5 */,0,1) : new T4(1,_nB/* sFEZ */,_nF/* sFF5 */,_nJ/* sFF9 */,1) : new T4(1,_nB/* sFEZ */,_nF/* sFF5 */,255,1);
                        }else{
                          var _nK/* sFFh */ = _nJ/* sFF9 */-1|0;
                          return (255>_nK/* sFFh */) ? (0>_nK/* sFFh */) ? new T4(1,_nB/* sFEZ */,_nF/* sFF5 */,0,1) : new T4(1,_nB/* sFEZ */,_nF/* sFF5 */,_nK/* sFFh */,1) : new T4(1,_nB/* sFEZ */,_nF/* sFF5 */,255,1);
                        }
                      },
                      _nL/* sFFm */ = E(_lD/* sFyL */);
                      if(!_nL/* sFFm */._){
                        return new F(function(){return _nG/* sFF6 */(0);});
                      }else{
                        return new F(function(){return _nG/* sFF6 */(E(_nL/* sFFm */.a));});
                      }
                    };
                    if(_nC/* sFF2 */>=_nD/* sFF3 */){
                      if(255>_nD/* sFF3 */){
                        if(0>_nD/* sFF3 */){
                          return new F(function(){return _nE/* sFF4 */(0);});
                        }else{
                          return new F(function(){return _nE/* sFF4 */(_nD/* sFF3 */);});
                        }
                      }else{
                        return new F(function(){return _nE/* sFF4 */(255);});
                      }
                    }else{
                      var _nM/* sFFx */ = _nD/* sFF3 */-1|0;
                      if(255>_nM/* sFFx */){
                        if(0>_nM/* sFFx */){
                          return new F(function(){return _nE/* sFF4 */(0);});
                        }else{
                          return new F(function(){return _nE/* sFF4 */(_nM/* sFFx */);});
                        }
                      }else{
                        return new F(function(){return _nE/* sFF4 */(255);});
                      }
                    }
                  };
                  if(_ny/* sFEW */>=_nz/* sFEX */){
                    if(255>_nz/* sFEX */){
                      if(0>_nz/* sFEX */){
                        return new F(function(){return _nA/* sFEY */(0);});
                      }else{
                        return new F(function(){return _nA/* sFEY */(_nz/* sFEX */);});
                      }
                    }else{
                      return new F(function(){return _nA/* sFEY */(255);});
                    }
                  }else{
                    var _nN/* sFFJ */ = _nz/* sFEX */-1|0;
                    if(255>_nN/* sFFJ */){
                      if(0>_nN/* sFFJ */){
                        return new F(function(){return _nA/* sFEY */(0);});
                      }else{
                        return new F(function(){return _nA/* sFEY */(_nN/* sFFJ */);});
                      }
                    }else{
                      return new F(function(){return _nA/* sFEY */(255);});
                    }
                  }
                },
                _nO/* sFFO */ = E(_lz/* sFyF */);
                if(!_nO/* sFFO */._){
                  return B(_nw/* sFEU */(0));
                }else{
                  return B(_nw/* sFEU */(E(_nO/* sFFO */.a)));
                }
              });
            }
        }
      },
      _nP/* sFFT */ = E(_lw/* sFyA */);
      switch(_nP/* sFFT */._){
        case 0:
          return new F(function(){return _lC/* sFyJ */(_/* EXTERNAL */, new T1(1,_nP/* sFFT */.a));});
          break;
        case 1:
          var _nQ/* sFFX */ = B(A1(_nP/* sFFT */.a,_/* EXTERNAL */));
          return new F(function(){return _lC/* sFyJ */(_/* EXTERNAL */, new T1(1,_nQ/* sFFX */));});
          break;
        case 2:
          var _nR/* sFG9 */ = rMV/* EXTERNAL */(E(E(_nP/* sFFT */.a).c)),
          _nS/* sFGc */ = E(_nR/* sFG9 */);
          if(!_nS/* sFGc */._){
            var _nT/* sFGg */ = new T(function(){
              return B(A1(_nP/* sFFT */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_nS/* sFGc */.a));
              })));
            });
            return new F(function(){return _lC/* sFyJ */(_/* EXTERNAL */, new T1(1,_nT/* sFGg */));});
          }else{
            return new F(function(){return _lC/* sFyJ */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _nU/* sFGr */ = rMV/* EXTERNAL */(E(E(_nP/* sFFT */.a).c)),
          _nV/* sFGu */ = E(_nU/* sFGr */);
          if(!_nV/* sFGu */._){
            var _nW/* sFGA */ = B(A2(_nP/* sFFT */.b,E(_nV/* sFGu */.a).a, _/* EXTERNAL */));
            return new F(function(){return _lC/* sFyJ */(_/* EXTERNAL */, new T1(1,_nW/* sFGA */));});
          }else{
            return new F(function(){return _lC/* sFyJ */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _nX/* sFGF */ = function(_/* EXTERNAL */){
      var _nY/* sFGH */ = function(_/* EXTERNAL */, _nZ/* sFGJ */){
        var _o0/* sFGK */ = E(_lx/* sFyB */);
        switch(_o0/* sFGK */._){
          case 0:
            return new T(function(){
              var _o1/* sFGM */ = function(_o2/* sFGN */){
                var _o3/* sFGO */ = _o2/* sFGN */*256,
                _o4/* sFGP */ = _o3/* sFGO */&4294967295,
                _o5/* sFGQ */ = function(_o6/* sFGR */){
                  var _o7/* sFGS */ = function(_o8/* sFGT */){
                    var _o9/* sFGU */ = _o8/* sFGT */*256,
                    _oa/* sFGV */ = _o9/* sFGU */&4294967295,
                    _ob/* sFGW */ = function(_oc/* sFGX */){
                      var _od/* sFGY */ = E(_o0/* sFGK */.a);
                      return (1>_od/* sFGY */) ? (0>_od/* sFGY */) ? new T4(1,_o6/* sFGR */,0,_oc/* sFGX */,0) : new T4(1,_o6/* sFGR */,0,_oc/* sFGX */,_od/* sFGY */) : new T4(1,_o6/* sFGR */,0,_oc/* sFGX */,1);
                    };
                    if(_o9/* sFGU */>=_oa/* sFGV */){
                      if(255>_oa/* sFGV */){
                        if(0>_oa/* sFGV */){
                          return new F(function(){return _ob/* sFGW */(0);});
                        }else{
                          return new F(function(){return _ob/* sFGW */(_oa/* sFGV */);});
                        }
                      }else{
                        return new F(function(){return _ob/* sFGW */(255);});
                      }
                    }else{
                      var _oe/* sFHb */ = _oa/* sFGV */-1|0;
                      if(255>_oe/* sFHb */){
                        if(0>_oe/* sFHb */){
                          return new F(function(){return _ob/* sFGW */(0);});
                        }else{
                          return new F(function(){return _ob/* sFGW */(_oe/* sFHb */);});
                        }
                      }else{
                        return new F(function(){return _ob/* sFGW */(255);});
                      }
                    }
                  },
                  _of/* sFHg */ = E(_nZ/* sFGJ */);
                  if(!_of/* sFHg */._){
                    return new F(function(){return _o7/* sFGS */(0);});
                  }else{
                    return new F(function(){return _o7/* sFGS */(E(_of/* sFHg */.a));});
                  }
                };
                if(_o3/* sFGO */>=_o4/* sFGP */){
                  if(255>_o4/* sFGP */){
                    if(0>_o4/* sFGP */){
                      return new F(function(){return _o5/* sFGQ */(0);});
                    }else{
                      return new F(function(){return _o5/* sFGQ */(_o4/* sFGP */);});
                    }
                  }else{
                    return new F(function(){return _o5/* sFGQ */(255);});
                  }
                }else{
                  var _og/* sFHr */ = _o4/* sFGP */-1|0;
                  if(255>_og/* sFHr */){
                    if(0>_og/* sFHr */){
                      return new F(function(){return _o5/* sFGQ */(0);});
                    }else{
                      return new F(function(){return _o5/* sFGQ */(_og/* sFHr */);});
                    }
                  }else{
                    return new F(function(){return _o5/* sFGQ */(255);});
                  }
                }
              },
              _oh/* sFHw */ = E(_lz/* sFyF */);
              if(!_oh/* sFHw */._){
                return B(_o1/* sFGM */(0));
              }else{
                return B(_o1/* sFGM */(E(_oh/* sFHw */.a)));
              }
            });
          case 1:
            var _oi/* sFHC */ = B(A1(_o0/* sFGK */.a,_/* EXTERNAL */)),
            _oj/* sFHE */ = _oi/* sFHC */;
            return new T(function(){
              var _ok/* sFHF */ = function(_ol/* sFHG */){
                var _om/* sFHH */ = _ol/* sFHG */*256,
                _on/* sFHI */ = _om/* sFHH */&4294967295,
                _oo/* sFHJ */ = function(_op/* sFHK */){
                  var _oq/* sFHL */ = function(_or/* sFHM */){
                    var _os/* sFHN */ = _or/* sFHM */*256,
                    _ot/* sFHO */ = _os/* sFHN */&4294967295,
                    _ou/* sFHP */ = function(_ov/* sFHQ */){
                      var _ow/* sFHR */ = E(_oj/* sFHE */);
                      return (1>_ow/* sFHR */) ? (0>_ow/* sFHR */) ? new T4(1,_op/* sFHK */,0,_ov/* sFHQ */,0) : new T4(1,_op/* sFHK */,0,_ov/* sFHQ */,_ow/* sFHR */) : new T4(1,_op/* sFHK */,0,_ov/* sFHQ */,1);
                    };
                    if(_os/* sFHN */>=_ot/* sFHO */){
                      if(255>_ot/* sFHO */){
                        if(0>_ot/* sFHO */){
                          return new F(function(){return _ou/* sFHP */(0);});
                        }else{
                          return new F(function(){return _ou/* sFHP */(_ot/* sFHO */);});
                        }
                      }else{
                        return new F(function(){return _ou/* sFHP */(255);});
                      }
                    }else{
                      var _ox/* sFI4 */ = _ot/* sFHO */-1|0;
                      if(255>_ox/* sFI4 */){
                        if(0>_ox/* sFI4 */){
                          return new F(function(){return _ou/* sFHP */(0);});
                        }else{
                          return new F(function(){return _ou/* sFHP */(_ox/* sFI4 */);});
                        }
                      }else{
                        return new F(function(){return _ou/* sFHP */(255);});
                      }
                    }
                  },
                  _oy/* sFI9 */ = E(_nZ/* sFGJ */);
                  if(!_oy/* sFI9 */._){
                    return new F(function(){return _oq/* sFHL */(0);});
                  }else{
                    return new F(function(){return _oq/* sFHL */(E(_oy/* sFI9 */.a));});
                  }
                };
                if(_om/* sFHH */>=_on/* sFHI */){
                  if(255>_on/* sFHI */){
                    if(0>_on/* sFHI */){
                      return new F(function(){return _oo/* sFHJ */(0);});
                    }else{
                      return new F(function(){return _oo/* sFHJ */(_on/* sFHI */);});
                    }
                  }else{
                    return new F(function(){return _oo/* sFHJ */(255);});
                  }
                }else{
                  var _oz/* sFIk */ = _on/* sFHI */-1|0;
                  if(255>_oz/* sFIk */){
                    if(0>_oz/* sFIk */){
                      return new F(function(){return _oo/* sFHJ */(0);});
                    }else{
                      return new F(function(){return _oo/* sFHJ */(_oz/* sFIk */);});
                    }
                  }else{
                    return new F(function(){return _oo/* sFHJ */(255);});
                  }
                }
              },
              _oA/* sFIp */ = E(_lz/* sFyF */);
              if(!_oA/* sFIp */._){
                return B(_ok/* sFHF */(0));
              }else{
                return B(_ok/* sFHF */(E(_oA/* sFIp */.a)));
              }
            });
          case 2:
            var _oB/* sFIC */ = rMV/* EXTERNAL */(E(E(_o0/* sFGK */.a).c)),
            _oC/* sFIF */ = E(_oB/* sFIC */);
            return (_oC/* sFIF */._==0) ? new T(function(){
              var _oD/* sFII */ = function(_oE/* sFIJ */){
                var _oF/* sFIK */ = _oE/* sFIJ */*256,
                _oG/* sFIL */ = _oF/* sFIK */&4294967295,
                _oH/* sFIM */ = function(_oI/* sFIN */){
                  var _oJ/* sFIO */ = function(_oK/* sFIP */){
                    var _oL/* sFIQ */ = _oK/* sFIP */*256,
                    _oM/* sFIR */ = _oL/* sFIQ */&4294967295,
                    _oN/* sFIS */ = function(_oO/* sFIT */){
                      var _oP/* sFIV */ = B(A1(_o0/* sFGK */.b,new T(function(){
                        return B(_fB/* Data.Tuple.fst */(_oC/* sFIF */.a));
                      })));
                      return (1>_oP/* sFIV */) ? (0>_oP/* sFIV */) ? new T4(1,_oI/* sFIN */,0,_oO/* sFIT */,0) : new T4(1,_oI/* sFIN */,0,_oO/* sFIT */,_oP/* sFIV */) : new T4(1,_oI/* sFIN */,0,_oO/* sFIT */,1);
                    };
                    if(_oL/* sFIQ */>=_oM/* sFIR */){
                      if(255>_oM/* sFIR */){
                        if(0>_oM/* sFIR */){
                          return new F(function(){return _oN/* sFIS */(0);});
                        }else{
                          return new F(function(){return _oN/* sFIS */(_oM/* sFIR */);});
                        }
                      }else{
                        return new F(function(){return _oN/* sFIS */(255);});
                      }
                    }else{
                      var _oQ/* sFJ8 */ = _oM/* sFIR */-1|0;
                      if(255>_oQ/* sFJ8 */){
                        if(0>_oQ/* sFJ8 */){
                          return new F(function(){return _oN/* sFIS */(0);});
                        }else{
                          return new F(function(){return _oN/* sFIS */(_oQ/* sFJ8 */);});
                        }
                      }else{
                        return new F(function(){return _oN/* sFIS */(255);});
                      }
                    }
                  },
                  _oR/* sFJd */ = E(_nZ/* sFGJ */);
                  if(!_oR/* sFJd */._){
                    return new F(function(){return _oJ/* sFIO */(0);});
                  }else{
                    return new F(function(){return _oJ/* sFIO */(E(_oR/* sFJd */.a));});
                  }
                };
                if(_oF/* sFIK */>=_oG/* sFIL */){
                  if(255>_oG/* sFIL */){
                    if(0>_oG/* sFIL */){
                      return new F(function(){return _oH/* sFIM */(0);});
                    }else{
                      return new F(function(){return _oH/* sFIM */(_oG/* sFIL */);});
                    }
                  }else{
                    return new F(function(){return _oH/* sFIM */(255);});
                  }
                }else{
                  var _oS/* sFJo */ = _oG/* sFIL */-1|0;
                  if(255>_oS/* sFJo */){
                    if(0>_oS/* sFJo */){
                      return new F(function(){return _oH/* sFIM */(0);});
                    }else{
                      return new F(function(){return _oH/* sFIM */(_oS/* sFJo */);});
                    }
                  }else{
                    return new F(function(){return _oH/* sFIM */(255);});
                  }
                }
              },
              _oT/* sFJt */ = E(_lz/* sFyF */);
              if(!_oT/* sFJt */._){
                return B(_oD/* sFII */(0));
              }else{
                return B(_oD/* sFII */(E(_oT/* sFJt */.a)));
              }
            }) : new T(function(){
              var _oU/* sFJz */ = function(_oV/* sFJA */){
                var _oW/* sFJB */ = _oV/* sFJA */*256,
                _oX/* sFJC */ = _oW/* sFJB */&4294967295,
                _oY/* sFJD */ = function(_oZ/* sFJE */){
                  var _p0/* sFJF */ = function(_p1/* sFJG */){
                    var _p2/* sFJH */ = _p1/* sFJG */*256,
                    _p3/* sFJI */ = _p2/* sFJH */&4294967295;
                    if(_p2/* sFJH */>=_p3/* sFJI */){
                      return (255>_p3/* sFJI */) ? (0>_p3/* sFJI */) ? new T4(1,_oZ/* sFJE */,0,0,1) : new T4(1,_oZ/* sFJE */,0,_p3/* sFJI */,1) : new T4(1,_oZ/* sFJE */,0,255,1);
                    }else{
                      var _p4/* sFJQ */ = _p3/* sFJI */-1|0;
                      return (255>_p4/* sFJQ */) ? (0>_p4/* sFJQ */) ? new T4(1,_oZ/* sFJE */,0,0,1) : new T4(1,_oZ/* sFJE */,0,_p4/* sFJQ */,1) : new T4(1,_oZ/* sFJE */,0,255,1);
                    }
                  },
                  _p5/* sFJV */ = E(_nZ/* sFGJ */);
                  if(!_p5/* sFJV */._){
                    return new F(function(){return _p0/* sFJF */(0);});
                  }else{
                    return new F(function(){return _p0/* sFJF */(E(_p5/* sFJV */.a));});
                  }
                };
                if(_oW/* sFJB */>=_oX/* sFJC */){
                  if(255>_oX/* sFJC */){
                    if(0>_oX/* sFJC */){
                      return new F(function(){return _oY/* sFJD */(0);});
                    }else{
                      return new F(function(){return _oY/* sFJD */(_oX/* sFJC */);});
                    }
                  }else{
                    return new F(function(){return _oY/* sFJD */(255);});
                  }
                }else{
                  var _p6/* sFK6 */ = _oX/* sFJC */-1|0;
                  if(255>_p6/* sFK6 */){
                    if(0>_p6/* sFK6 */){
                      return new F(function(){return _oY/* sFJD */(0);});
                    }else{
                      return new F(function(){return _oY/* sFJD */(_p6/* sFK6 */);});
                    }
                  }else{
                    return new F(function(){return _oY/* sFJD */(255);});
                  }
                }
              },
              _p7/* sFKb */ = E(_lz/* sFyF */);
              if(!_p7/* sFKb */._){
                return B(_oU/* sFJz */(0));
              }else{
                return B(_oU/* sFJz */(E(_p7/* sFKb */.a)));
              }
            });
          default:
            var _p8/* sFKo */ = rMV/* EXTERNAL */(E(E(_o0/* sFGK */.a).c)),
            _p9/* sFKr */ = E(_p8/* sFKo */);
            if(!_p9/* sFKr */._){
              var _pa/* sFKx */ = B(A2(_o0/* sFGK */.b,E(_p9/* sFKr */.a).a, _/* EXTERNAL */)),
              _pb/* sFKz */ = _pa/* sFKx */;
              return new T(function(){
                var _pc/* sFKA */ = function(_pd/* sFKB */){
                  var _pe/* sFKC */ = _pd/* sFKB */*256,
                  _pf/* sFKD */ = _pe/* sFKC */&4294967295,
                  _pg/* sFKE */ = function(_ph/* sFKF */){
                    var _pi/* sFKG */ = function(_pj/* sFKH */){
                      var _pk/* sFKI */ = _pj/* sFKH */*256,
                      _pl/* sFKJ */ = _pk/* sFKI */&4294967295,
                      _pm/* sFKK */ = function(_pn/* sFKL */){
                        var _po/* sFKM */ = E(_pb/* sFKz */);
                        return (1>_po/* sFKM */) ? (0>_po/* sFKM */) ? new T4(1,_ph/* sFKF */,0,_pn/* sFKL */,0) : new T4(1,_ph/* sFKF */,0,_pn/* sFKL */,_po/* sFKM */) : new T4(1,_ph/* sFKF */,0,_pn/* sFKL */,1);
                      };
                      if(_pk/* sFKI */>=_pl/* sFKJ */){
                        if(255>_pl/* sFKJ */){
                          if(0>_pl/* sFKJ */){
                            return new F(function(){return _pm/* sFKK */(0);});
                          }else{
                            return new F(function(){return _pm/* sFKK */(_pl/* sFKJ */);});
                          }
                        }else{
                          return new F(function(){return _pm/* sFKK */(255);});
                        }
                      }else{
                        var _pp/* sFKZ */ = _pl/* sFKJ */-1|0;
                        if(255>_pp/* sFKZ */){
                          if(0>_pp/* sFKZ */){
                            return new F(function(){return _pm/* sFKK */(0);});
                          }else{
                            return new F(function(){return _pm/* sFKK */(_pp/* sFKZ */);});
                          }
                        }else{
                          return new F(function(){return _pm/* sFKK */(255);});
                        }
                      }
                    },
                    _pq/* sFL4 */ = E(_nZ/* sFGJ */);
                    if(!_pq/* sFL4 */._){
                      return new F(function(){return _pi/* sFKG */(0);});
                    }else{
                      return new F(function(){return _pi/* sFKG */(E(_pq/* sFL4 */.a));});
                    }
                  };
                  if(_pe/* sFKC */>=_pf/* sFKD */){
                    if(255>_pf/* sFKD */){
                      if(0>_pf/* sFKD */){
                        return new F(function(){return _pg/* sFKE */(0);});
                      }else{
                        return new F(function(){return _pg/* sFKE */(_pf/* sFKD */);});
                      }
                    }else{
                      return new F(function(){return _pg/* sFKE */(255);});
                    }
                  }else{
                    var _pr/* sFLf */ = _pf/* sFKD */-1|0;
                    if(255>_pr/* sFLf */){
                      if(0>_pr/* sFLf */){
                        return new F(function(){return _pg/* sFKE */(0);});
                      }else{
                        return new F(function(){return _pg/* sFKE */(_pr/* sFLf */);});
                      }
                    }else{
                      return new F(function(){return _pg/* sFKE */(255);});
                    }
                  }
                },
                _ps/* sFLk */ = E(_lz/* sFyF */);
                if(!_ps/* sFLk */._){
                  return B(_pc/* sFKA */(0));
                }else{
                  return B(_pc/* sFKA */(E(_ps/* sFLk */.a)));
                }
              });
            }else{
              return new T(function(){
                var _pt/* sFLq */ = function(_pu/* sFLr */){
                  var _pv/* sFLs */ = _pu/* sFLr */*256,
                  _pw/* sFLt */ = _pv/* sFLs */&4294967295,
                  _px/* sFLu */ = function(_py/* sFLv */){
                    var _pz/* sFLw */ = function(_pA/* sFLx */){
                      var _pB/* sFLy */ = _pA/* sFLx */*256,
                      _pC/* sFLz */ = _pB/* sFLy */&4294967295;
                      if(_pB/* sFLy */>=_pC/* sFLz */){
                        return (255>_pC/* sFLz */) ? (0>_pC/* sFLz */) ? new T4(1,_py/* sFLv */,0,0,1) : new T4(1,_py/* sFLv */,0,_pC/* sFLz */,1) : new T4(1,_py/* sFLv */,0,255,1);
                      }else{
                        var _pD/* sFLH */ = _pC/* sFLz */-1|0;
                        return (255>_pD/* sFLH */) ? (0>_pD/* sFLH */) ? new T4(1,_py/* sFLv */,0,0,1) : new T4(1,_py/* sFLv */,0,_pD/* sFLH */,1) : new T4(1,_py/* sFLv */,0,255,1);
                      }
                    },
                    _pE/* sFLM */ = E(_nZ/* sFGJ */);
                    if(!_pE/* sFLM */._){
                      return new F(function(){return _pz/* sFLw */(0);});
                    }else{
                      return new F(function(){return _pz/* sFLw */(E(_pE/* sFLM */.a));});
                    }
                  };
                  if(_pv/* sFLs */>=_pw/* sFLt */){
                    if(255>_pw/* sFLt */){
                      if(0>_pw/* sFLt */){
                        return new F(function(){return _px/* sFLu */(0);});
                      }else{
                        return new F(function(){return _px/* sFLu */(_pw/* sFLt */);});
                      }
                    }else{
                      return new F(function(){return _px/* sFLu */(255);});
                    }
                  }else{
                    var _pF/* sFLX */ = _pw/* sFLt */-1|0;
                    if(255>_pF/* sFLX */){
                      if(0>_pF/* sFLX */){
                        return new F(function(){return _px/* sFLu */(0);});
                      }else{
                        return new F(function(){return _px/* sFLu */(_pF/* sFLX */);});
                      }
                    }else{
                      return new F(function(){return _px/* sFLu */(255);});
                    }
                  }
                },
                _pG/* sFM2 */ = E(_lz/* sFyF */);
                if(!_pG/* sFM2 */._){
                  return B(_pt/* sFLq */(0));
                }else{
                  return B(_pt/* sFLq */(E(_pG/* sFM2 */.a)));
                }
              });
            }
        }
      },
      _pH/* sFM7 */ = E(_lw/* sFyA */);
      switch(_pH/* sFM7 */._){
        case 0:
          return new F(function(){return _nY/* sFGH */(_/* EXTERNAL */, new T1(1,_pH/* sFM7 */.a));});
          break;
        case 1:
          var _pI/* sFMb */ = B(A1(_pH/* sFM7 */.a,_/* EXTERNAL */));
          return new F(function(){return _nY/* sFGH */(_/* EXTERNAL */, new T1(1,_pI/* sFMb */));});
          break;
        case 2:
          var _pJ/* sFMn */ = rMV/* EXTERNAL */(E(E(_pH/* sFM7 */.a).c)),
          _pK/* sFMq */ = E(_pJ/* sFMn */);
          if(!_pK/* sFMq */._){
            var _pL/* sFMu */ = new T(function(){
              return B(A1(_pH/* sFM7 */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_pK/* sFMq */.a));
              })));
            });
            return new F(function(){return _nY/* sFGH */(_/* EXTERNAL */, new T1(1,_pL/* sFMu */));});
          }else{
            return new F(function(){return _nY/* sFGH */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _pM/* sFMF */ = rMV/* EXTERNAL */(E(E(_pH/* sFM7 */.a).c)),
          _pN/* sFMI */ = E(_pM/* sFMF */);
          if(!_pN/* sFMI */._){
            var _pO/* sFMO */ = B(A2(_pH/* sFM7 */.b,E(_pN/* sFMI */.a).a, _/* EXTERNAL */));
            return new F(function(){return _nY/* sFGH */(_/* EXTERNAL */, new T1(1,_pO/* sFMO */));});
          }else{
            return new F(function(){return _nY/* sFGH */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _pP/* sFMT */ = E(_lv/* sFyz */);
    switch(_pP/* sFMT */._){
      case 0:
        return new F(function(){return _lA/* sFyG */(_/* EXTERNAL */, _pP/* sFMT */.a);});
        break;
      case 1:
        var _pQ/* sFMW */ = B(A1(_pP/* sFMT */.a,_/* EXTERNAL */));
        return new F(function(){return _lA/* sFyG */(_/* EXTERNAL */, _pQ/* sFMW */);});
        break;
      case 2:
        var _pR/* sFN7 */ = rMV/* EXTERNAL */(E(E(_pP/* sFMT */.a).c)),
        _pS/* sFNa */ = E(_pR/* sFN7 */);
        if(!_pS/* sFNa */._){
          var _pT/* sFNh */ = new T(function(){
            return B(A1(_pP/* sFMT */.b,new T(function(){
              return E(E(_pS/* sFNa */.a).a);
            })));
          });
          return new F(function(){return _lA/* sFyG */(_/* EXTERNAL */, _pT/* sFNh */);});
        }else{
          return new F(function(){return _nX/* sFGF */(_/* EXTERNAL */);});
        }
        break;
      default:
        var _pU/* sFNr */ = rMV/* EXTERNAL */(E(E(_pP/* sFMT */.a).c)),
        _pV/* sFNu */ = E(_pU/* sFNr */);
        if(!_pV/* sFNu */._){
          var _pW/* sFNA */ = B(A2(_pP/* sFMT */.b,E(_pV/* sFNu */.a).a, _/* EXTERNAL */));
          return new F(function(){return _lA/* sFyG */(_/* EXTERNAL */, _pW/* sFNA */);});
        }else{
          return new F(function(){return _nX/* sFGF */(_/* EXTERNAL */);});
        }
    }
  },
  _pX/* sFNE */ = E(_lu/* sFyy */);
  switch(_pX/* sFNE */._){
    case 0:
      return new F(function(){return _ly/* sFyD */(_/* EXTERNAL */, new T1(1,_pX/* sFNE */.a));});
      break;
    case 1:
      var _pY/* sFNI */ = B(A1(_pX/* sFNE */.a,_/* EXTERNAL */));
      return new F(function(){return _ly/* sFyD */(_/* EXTERNAL */, new T1(1,_pY/* sFNI */));});
      break;
    case 2:
      var _pZ/* sFNU */ = rMV/* EXTERNAL */(E(E(_pX/* sFNE */.a).c)),
      _q0/* sFNX */ = E(_pZ/* sFNU */);
      if(!_q0/* sFNX */._){
        var _q1/* sFO1 */ = new T(function(){
          return B(A1(_pX/* sFNE */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_q0/* sFNX */.a));
          })));
        });
        return new F(function(){return _ly/* sFyD */(_/* EXTERNAL */, new T1(1,_q1/* sFO1 */));});
      }else{
        return new F(function(){return _ly/* sFyD */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
      }
      break;
    default:
      var _q2/* sFOc */ = rMV/* EXTERNAL */(E(E(_pX/* sFNE */.a).c)),
      _q3/* sFOf */ = E(_q2/* sFOc */);
      if(!_q3/* sFOf */._){
        var _q4/* sFOl */ = B(A2(_pX/* sFNE */.b,E(_q3/* sFOf */.a).a, _/* EXTERNAL */));
        return new F(function(){return _ly/* sFyD */(_/* EXTERNAL */, new T1(1,_q4/* sFOl */));});
      }else{
        return new F(function(){return _ly/* sFyD */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
      }
  }
},
_q5/* lvl1 */ = new T(function(){
  return toJSStr/* EXTERNAL */(_6/* GHC.Types.[] */);
}),
_q6/* lvl2 */ = "rgb(",
_q7/* lvl3 */ = ",",
_q8/* lvl5 */ = "rgba(",
_q9/* lvl4 */ = ")",
_qa/* lvl6 */ = new T2(1,_q9/* Core.Render.Internal.lvl4 */,_6/* GHC.Types.[] */),
_qb/* $wcolor2JSString */ = function(_qc/* sFk6 */){
  var _qd/* sFk7 */ = E(_qc/* sFk6 */);
  if(!_qd/* sFk7 */._){
    var _qe/* sFkG */ = jsCat/* EXTERNAL */(new T2(1,_q6/* Core.Render.Internal.lvl2 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qd/* sFk7 */.a);
    }),new T2(1,_q7/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qd/* sFk7 */.b);
    }),new T2(1,_q7/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qd/* sFk7 */.c);
    }),_qa/* Core.Render.Internal.lvl6 */)))))), E(_q5/* Core.Render.Internal.lvl1 */));
    return E(_qe/* sFkG */);
  }else{
    var _qf/* sFlp */ = jsCat/* EXTERNAL */(new T2(1,_q8/* Core.Render.Internal.lvl5 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qd/* sFk7 */.a);
    }),new T2(1,_q7/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qd/* sFk7 */.b);
    }),new T2(1,_q7/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qd/* sFk7 */.c);
    }),new T2(1,_q7/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qd/* sFk7 */.d);
    }),_qa/* Core.Render.Internal.lvl6 */)))))))), E(_q5/* Core.Render.Internal.lvl1 */));
    return E(_qf/* sFlp */);
  }
},
_qg/* $w$c<*> */ = function(_qh/* s1DM */, _qi/* s1DN */){
  var _qj/* s1DO */ = E(_qh/* s1DM */),
  _qk/* s1E2 */ = function(_ql/* s1DR */){
    var _qm/* s1DS */ = E(_qi/* s1DN */),
    _qn/* s1DZ */ = function(_qo/* s1DV */){
      return new T2(0,E(new T1(0,new T(function(){
        return B(A1(_ql/* s1DR */,_qo/* s1DV */));
      }))),E(new T1(0,_/* EXTERNAL */)));
    };
    return new T2(0,E(_qm/* s1DS */.a),E(new T2(2,_qm/* s1DS */.b,new T1(1,_qn/* s1DZ */))));
  };
  return new T2(0,E(_qj/* s1DO */.a),E(new T2(2,_qj/* s1DO */.b,new T1(1,_qk/* s1E2 */))));
},
_qp/* <$ */ = function(_qq/* s35r */){
  return E(E(_qq/* s35r */).b);
},
_qr/* $fApplicativeSkeleton_$c*> */ = function(_qs/* s1E9 */, _qt/* s1Ea */, _qu/* s1Eb */){
  return new F(function(){return _qg/* Control.Monad.Skeleton.$w$c<*> */(B(A3(_qp/* GHC.Base.<$ */,_qs/* s1E9 */, _2E/* GHC.Base.id */, _qt/* s1Ea */)), _qu/* s1Eb */);});
},
_qv/* const */ = function(_qw/* s3aC */, _qx/* s3aD */){
  return E(_qw/* s3aC */);
},
_qy/* fmap */ = function(_qz/* s35n */){
  return E(E(_qz/* s35n */).a);
},
_qA/* $fApplicativeSkeleton_$c<* */ = function(_qB/* s1E5 */, _qC/* s1E6 */, _qD/* s1E7 */){
  return new F(function(){return _qg/* Control.Monad.Skeleton.$w$c<*> */(B(A3(_qy/* GHC.Base.fmap */,_qB/* s1E5 */, _qv/* GHC.Base.const */, _qC/* s1E6 */)), _qD/* s1E7 */);});
},
_qE/* a1 */ = function(_qF/* s1Dn */, _qG/* s1Do */){
  return new T2(0,E(new T1(0,_qG/* s1Do */)),E(new T1(0,_/* EXTERNAL */)));
},
_qH/* $fApplicativeSkeleton_$creturn */ = function(_qI/* B2 */, _qJ/* B1 */){
  return new F(function(){return _qE/* Control.Monad.Skeleton.a1 */(_qI/* B2 */, _qJ/* B1 */);});
},
_qK/* lvl1 */ = new T(function(){
  return B(_bo/* Control.Exception.Base.absentError */("w_s1yq Functor (Skeleton t)"));
}),
_qL/* lvl3 */ = new T(function(){
  return B(_qM/* Control.Monad.Skeleton.$fApplicativeSkeleton */(_qK/* Control.Monad.Skeleton.lvl1 */));
}),
_qN/* lvl4 */ = function(_qJ/* B1 */){
  return new F(function(){return _qH/* Control.Monad.Skeleton.$fApplicativeSkeleton_$creturn */(_qL/* Control.Monad.Skeleton.lvl3 */, _qJ/* B1 */);});
},
_qO/* $w$cpure */ = function(_qP/* s1Ek */, _qJ/* B1 */){
  return new F(function(){return _qN/* Control.Monad.Skeleton.lvl4 */(_qJ/* B1 */);});
},
_qQ/* lvl2 */ = function(_qJ/* B1 */){
  return new F(function(){return _qO/* Control.Monad.Skeleton.$w$cpure */(_/* EXTERNAL */, _qJ/* B1 */);});
},
_qM/* $fApplicativeSkeleton */ = function(_qR/* s1Eh */){
  return new T5(0,_qR/* s1Eh */,_qQ/* Control.Monad.Skeleton.lvl2 */,_qg/* Control.Monad.Skeleton.$w$c<*> */,function(_qI/* B2 */, _qJ/* B1 */){
    return new F(function(){return _qr/* Control.Monad.Skeleton.$fApplicativeSkeleton_$c*> */(_qR/* s1Eh */, _qI/* B2 */, _qJ/* B1 */);});
  },function(_qI/* B2 */, _qJ/* B1 */){
    return new F(function(){return _qA/* Control.Monad.Skeleton.$fApplicativeSkeleton_$c<* */(_qR/* s1Eh */, _qI/* B2 */, _qJ/* B1 */);});
  });
},
_qS/* $fMonadSkeleton_$c>> */ = function(_qT/* s1DC */, _qU/* s1DD */, _qV/* s1DE */){
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,B(_qW/* Control.Monad.Skeleton.$fMonadSkeleton */(_qT/* s1DC */)), _qU/* s1DD */, function(_qX/* s1DG */){
    return E(_qV/* s1DE */);
  });});
},
_qY/* $fMonadSkeleton_$c>>= */ = function(_qZ/* s1Dr */, _r0/* s1Ds */, _r1/* s1Dt */){
  var _r2/* s1Du */ = E(_r0/* s1Ds */);
  return new T2(0,E(_r2/* s1Du */.a),E(new T2(2,_r2/* s1Du */.b,new T1(1,_r1/* s1Dt */))));
},
_r3/* lvl */ = function(_r4/* s1DB */){
  return new F(function(){return err/* EXTERNAL */(_r4/* s1DB */);});
},
_qW/* $fMonadSkeleton */ = function(_r5/* s1DI */){
  return new T5(0,_r5/* s1DI */,function(_qI/* B2 */, _qJ/* B1 */){
    return new F(function(){return _qY/* Control.Monad.Skeleton.$fMonadSkeleton_$c>>= */(_r5/* s1DI */, _qI/* B2 */, _qJ/* B1 */);});
  },function(_qI/* B2 */, _qJ/* B1 */){
    return new F(function(){return _qS/* Control.Monad.Skeleton.$fMonadSkeleton_$c>> */(_r5/* s1DI */, _qI/* B2 */, _qJ/* B1 */);});
  },function(_qJ/* B1 */){
    return new F(function(){return _qH/* Control.Monad.Skeleton.$fApplicativeSkeleton_$creturn */(_r5/* s1DI */, _qJ/* B1 */);});
  },_r3/* Control.Monad.Skeleton.lvl */);
},
_r6/* $dMonad */ = new T(function(){
  return B(_qW/* Control.Monad.Skeleton.$fMonadSkeleton */(_r7/* Control.Monad.Skeleton.$dApplicative */));
}),
_r8/* liftM */ = function(_r9/* s3mK */, _ra/* s3mL */, _rb/* s3mM */){
  var _rc/* s3mP */ = function(_rd/* s3mN */){
    return new F(function(){return A2(_6T/* GHC.Base.return */,_r9/* s3mK */, new T(function(){
      return B(A1(_ra/* s3mL */,_rd/* s3mN */));
    }));});
  };
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_r9/* s3mK */, _rb/* s3mM */, _rc/* s3mP */);});
},
_re/* $fFunctorSkeleton_$cfmap */ = function(_qI/* B2 */, _qJ/* B1 */){
  return new F(function(){return _r8/* GHC.Base.liftM */(_r6/* Control.Monad.Skeleton.$dMonad */, _qI/* B2 */, _qJ/* B1 */);});
},
_rf/* $fFunctorSkeleton_$c<$ */ = function(_rg/* s1El */, _rh/* s1Em */){
  return new F(function(){return _re/* Control.Monad.Skeleton.$fFunctorSkeleton_$cfmap */(function(_ri/* s1En */){
    return E(_rg/* s1El */);
  }, _rh/* s1Em */);});
},
_rj/* $fFunctorSkeleton */ = new T(function(){
  return new T2(0,_re/* Control.Monad.Skeleton.$fFunctorSkeleton_$cfmap */,_rf/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */);
}),
_r7/* $dApplicative */ = new T(function(){
  return B(_qM/* Control.Monad.Skeleton.$fApplicativeSkeleton */(_rj/* Control.Monad.Skeleton.$fFunctorSkeleton */));
}),
_rk/* lvl5 */ = function(_qJ/* B1 */){
  return new F(function(){return _qH/* Control.Monad.Skeleton.$fApplicativeSkeleton_$creturn */(_r7/* Control.Monad.Skeleton.$dApplicative */, _qJ/* B1 */);});
},
_rl/* a2 */ = function(_rm/* s1Ep */){
  return new T2(0,E(new T2(1,_rm/* s1Ep */,_rk/* Control.Monad.Skeleton.lvl5 */)),E(new T1(0,_/* EXTERNAL */)));
},
_rn/* bone */ = function(_qJ/* B1 */){
  return new F(function(){return _rl/* Control.Monad.Skeleton.a2 */(_qJ/* B1 */);});
},
_ro/* clip_f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.beginPath();})");
}),
_rp/* fill2 */ = "fillStyle",
_rq/* fill_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.fill();})");
}),
_rr/* fill1 */ = function(_rs/* sFOq */, _rt/* sFOr */){
  return new F(function(){return _rn/* Control.Monad.Skeleton.bone */(new T2(0,function(_ru/* sFOs */, _/* EXTERNAL */){
    var _rv/* sFOu */ = E(_rs/* sFOq */),
    _rw/* sFOz */ = B(_lt/* Core.Render.Internal.$wa */(_rv/* sFOu */.a, _rv/* sFOu */.b, _rv/* sFOu */.c, _rv/* sFOu */.d, _/* EXTERNAL */)),
    _rx/* sFOC */ = E(_ru/* sFOs */),
    _ry/* sFOK */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), _rx/* sFOC */, E(_rp/* Core.Render.Internal.fill2 */), B(_qb/* Core.Render.Internal.$wcolor2JSString */(_rw/* sFOz */))),
    _rz/* sFOQ */ = __app1/* EXTERNAL */(E(_ro/* Core.Render.Internal.clip_f3 */), _rx/* sFOC */),
    _rA/* sFOX */ = B(A3(E(_rt/* sFOr */).b,_rx/* sFOC */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _rB/* sFP3 */ = __app1/* EXTERNAL */(E(_rq/* Core.Render.Internal.fill_f1 */), _rx/* sFOC */);
    return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */));});
},
_rC/* lvl */ = 50,
_rD/* lvl1 */ = 3,
_rE/* lvl10 */ = function(_rF/* sNuH */){
  return  -E(_rF/* sNuH */);
},
_rG/* lvl9 */ = 0,
_rH/* lvl11 */ = new T4(0,_rG/* Motion.Bounce.lvl9 */,_rG/* Motion.Bounce.lvl9 */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_rI/* lvl12 */ = new T2(0,_rG/* Motion.Bounce.lvl9 */,_rH/* Motion.Bounce.lvl11 */),
_rJ/* lvl13 */ = new T2(0,_rI/* Motion.Bounce.lvl12 */,_6/* GHC.Types.[] */),
_rK/* lvl14 */ = new T4(0,_lg/* Motion.Bounce.a */,_lg/* Motion.Bounce.a */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_rL/* lvl15 */ = new T2(0,_lg/* Motion.Bounce.a */,_rK/* Motion.Bounce.lvl14 */),
_rM/* lvl16 */ = new T2(0,_rL/* Motion.Bounce.lvl15 */,_6/* GHC.Types.[] */),
_rN/* lvl2 */ = -30,
_rO/* lvl3 */ = 30,
_rP/* lvl4 */ = -10,
_rQ/* lvl5 */ = 0,
_rR/* lvl6 */ = new T1(0,_lg/* Motion.Bounce.a */),
_rS/* a1 */ = 50,
_rT/* lvl7 */ = new T1(0,_rS/* Motion.Bounce.a1 */),
_rU/* a2 */ = 75,
_rV/* lvl8 */ = new T1(0,_rU/* Motion.Bounce.a2 */),
_rW/* liftA1 */ = function(_rX/* s3h5 */, _rY/* s3h6 */, _rZ/* s3h7 */, _/* EXTERNAL */){
  var _s0/* s3h9 */ = B(A1(_rY/* s3h6 */,_/* EXTERNAL */)),
  _s1/* s3hc */ = B(A1(_rZ/* s3h7 */,_/* EXTERNAL */));
  return new T(function(){
    return B(A2(_rX/* s3h5 */,_s0/* s3h9 */, _s1/* s3hc */));
  });
},
_s2/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Unable to operate opLift"));
}),
_s3/* $wpoly_fail */ = function(_s4/* sl4z */){
  return new F(function(){return err/* EXTERNAL */(_s2/* Core.Ease.lvl */);});
},
_s5/* lvl1 */ = new T(function(){
  return B(_s3/* Core.Ease.$wpoly_fail */(_/* EXTERNAL */));
}),
_s6/* opLift */ = function(_s7/* sl4A */, _s8/* sl4B */, _s9/* sl4C */){
  var _sa/* sl4D */ = function(_sb/* sl4E */){
    var _sc/* sl76 */ = function(_/* EXTERNAL */){
      var _sd/* sl4G */ = function(_/* EXTERNAL */, _se/* sl4I */){
        var _sf/* sl4J */ = E(_s9/* sl4C */);
        switch(_sf/* sl4J */._){
          case 0:
            return new T(function(){
              return B(A2(_s7/* sl4A */,_se/* sl4I */, _sf/* sl4J */.a));
            });
          case 1:
            var _sg/* sl4N */ = B(A1(_sf/* sl4J */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_s7/* sl4A */,_se/* sl4I */, _sg/* sl4N */));
            });
          case 2:
            var _sh/* sl4Z */ = rMV/* EXTERNAL */(E(E(_sf/* sl4J */.a).c)),
            _si/* sl52 */ = E(_sh/* sl4Z */);
            return (_si/* sl52 */._==0) ? new T(function(){
              var _sj/* sl56 */ = new T(function(){
                return B(A1(_sf/* sl4J */.b,new T(function(){
                  return B(_fB/* Data.Tuple.fst */(_si/* sl52 */.a));
                })));
              });
              return B(A2(_s7/* sl4A */,_se/* sl4I */, _sj/* sl56 */));
            }) : E(_s5/* Core.Ease.lvl1 */);
          default:
            var _sk/* sl5i */ = rMV/* EXTERNAL */(E(E(_sf/* sl4J */.a).c)),
            _sl/* sl5l */ = E(_sk/* sl5i */);
            if(!_sl/* sl5l */._){
              var _sm/* sl5r */ = B(A2(_sf/* sl4J */.b,E(_sl/* sl5l */.a).a, _/* EXTERNAL */));
              return new T(function(){
                return B(A2(_s7/* sl4A */,_se/* sl4I */, _sm/* sl5r */));
              });
            }else{
              return E(_s5/* Core.Ease.lvl1 */);
            }
        }
      },
      _sn/* sl5x */ = function(_/* EXTERNAL */){
        var _so/* sl5z */ = E(_s9/* sl4C */);
        switch(_so/* sl5z */._){
          case 0:
            return E(_s5/* Core.Ease.lvl1 */);
          case 1:
            var _sp/* sl5D */ = B(A1(_so/* sl5z */.a,_/* EXTERNAL */));
            return E(_s5/* Core.Ease.lvl1 */);
          case 2:
            var _sq/* sl5P */ = rMV/* EXTERNAL */(E(E(_so/* sl5z */.a).c));
            return (E(_sq/* sl5P */)._==0) ? E(_s5/* Core.Ease.lvl1 */) : E(_s5/* Core.Ease.lvl1 */);
          default:
            var _sr/* sl66 */ = rMV/* EXTERNAL */(E(E(_so/* sl5z */.a).c)),
            _ss/* sl69 */ = E(_sr/* sl66 */);
            if(!_ss/* sl69 */._){
              var _st/* sl6f */ = B(A2(_so/* sl5z */.b,E(_ss/* sl69 */.a).a, _/* EXTERNAL */));
              return E(_s5/* Core.Ease.lvl1 */);
            }else{
              return E(_s5/* Core.Ease.lvl1 */);
            }
        }
      },
      _su/* sl6l */ = E(_s8/* sl4B */);
      switch(_su/* sl6l */._){
        case 0:
          return new F(function(){return _sd/* sl4G */(_/* EXTERNAL */, _su/* sl6l */.a);});
          break;
        case 1:
          var _sv/* sl6o */ = B(A1(_su/* sl6l */.a,_/* EXTERNAL */));
          return new F(function(){return _sd/* sl4G */(_/* EXTERNAL */, _sv/* sl6o */);});
          break;
        case 2:
          var _sw/* sl6z */ = rMV/* EXTERNAL */(E(E(_su/* sl6l */.a).c)),
          _sx/* sl6C */ = E(_sw/* sl6z */);
          if(!_sx/* sl6C */._){
            var _sy/* sl6J */ = new T(function(){
              return B(A1(_su/* sl6l */.b,new T(function(){
                return E(E(_sx/* sl6C */.a).a);
              })));
            });
            return new F(function(){return _sd/* sl4G */(_/* EXTERNAL */, _sy/* sl6J */);});
          }else{
            return new F(function(){return _sn/* sl5x */(_/* EXTERNAL */);});
          }
          break;
        default:
          var _sz/* sl6T */ = rMV/* EXTERNAL */(E(E(_su/* sl6l */.a).c)),
          _sA/* sl6W */ = E(_sz/* sl6T */);
          if(!_sA/* sl6W */._){
            var _sB/* sl72 */ = B(A2(_su/* sl6l */.b,E(_sA/* sl6W */.a).a, _/* EXTERNAL */));
            return new F(function(){return _sd/* sl4G */(_/* EXTERNAL */, _sB/* sl72 */);});
          }else{
            return new F(function(){return _sn/* sl5x */(_/* EXTERNAL */);});
          }
      }
    };
    return new T1(1,_sc/* sl76 */);
  },
  _sC/* sl77 */ = E(_s8/* sl4B */);
  switch(_sC/* sl77 */._){
    case 0:
      var _sD/* sl78 */ = _sC/* sl77 */.a,
      _sE/* sl79 */ = E(_s9/* sl4C */);
      switch(_sE/* sl79 */._){
        case 0:
          return new T1(0,new T(function(){
            return B(A2(_s7/* sl4A */,_sD/* sl78 */, _sE/* sl79 */.a));
          }));
        case 1:
          var _sF/* sl7i */ = function(_/* EXTERNAL */){
            var _sG/* sl7e */ = B(A1(_sE/* sl79 */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_s7/* sl4A */,_sD/* sl78 */, _sG/* sl7e */));
            });
          };
          return new T1(1,_sF/* sl7i */);
        case 2:
          var _sH/* sl7l */ = new T(function(){
            return B(A1(_s7/* sl4A */,_sD/* sl78 */));
          }),
          _sI/* sl7o */ = function(_sJ/* sl7m */){
            return new F(function(){return A1(_sH/* sl7l */,new T(function(){
              return B(A1(_sE/* sl79 */.b,_sJ/* sl7m */));
            }));});
          };
          return new T2(2,_sE/* sl79 */.a,_sI/* sl7o */);
        default:
          var _sK/* sl7r */ = new T(function(){
            return B(A1(_s7/* sl4A */,_sD/* sl78 */));
          }),
          _sL/* sl7y */ = function(_sM/* sl7s */, _/* EXTERNAL */){
            var _sN/* sl7u */ = B(A2(_sE/* sl79 */.b,_sM/* sl7s */, _/* EXTERNAL */));
            return new T(function(){
              return B(A1(_sK/* sl7r */,_sN/* sl7u */));
            });
          };
          return new T2(3,_sE/* sl79 */.a,_sL/* sl7y */);
      }
      break;
    case 1:
      var _sO/* sl7z */ = _sC/* sl77 */.a,
      _sP/* sl7A */ = E(_s9/* sl4C */);
      switch(_sP/* sl7A */._){
        case 0:
          var _sQ/* sl7H */ = function(_/* EXTERNAL */){
            var _sR/* sl7D */ = B(A1(_sO/* sl7z */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_s7/* sl4A */,_sR/* sl7D */, _sP/* sl7A */.a));
            });
          };
          return new T1(1,_sQ/* sl7H */);
        case 1:
          return new T1(1,function(_/* EXTERNAL */){
            return new F(function(){return _rW/* GHC.Base.liftA1 */(_s7/* sl4A */, _sO/* sl7z */, _sP/* sl7A */.a, _/* EXTERNAL */);});
          });
        case 2:
          var _sS/* sl7T */ = function(_sT/* sl7M */, _/* EXTERNAL */){
            var _sU/* sl7O */ = B(A1(_sO/* sl7z */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_s7/* sl4A */,_sU/* sl7O */, new T(function(){
                return B(A1(_sP/* sl7A */.b,_sT/* sl7M */));
              })));
            });
          };
          return new T2(3,_sP/* sl7A */.a,_sS/* sl7T */);
        default:
          var _sV/* sl85 */ = function(_sW/* sl7W */, _/* EXTERNAL */){
            var _sX/* sl7Y */ = B(A1(_sO/* sl7z */,_/* EXTERNAL */)),
            _sY/* sl81 */ = B(A2(_sP/* sl7A */.b,_sW/* sl7W */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_s7/* sl4A */,_sX/* sl7Y */, _sY/* sl81 */));
            });
          };
          return new T2(3,_sP/* sl7A */.a,_sV/* sl85 */);
      }
      break;
    case 2:
      var _sZ/* sl86 */ = _sC/* sl77 */.a,
      _t0/* sl87 */ = _sC/* sl77 */.b,
      _t1/* sl88 */ = E(_s9/* sl4C */);
      switch(_t1/* sl88 */._){
        case 0:
          var _t2/* sl8c */ = function(_t3/* sl8a */){
            return new F(function(){return A2(_s7/* sl4A */,new T(function(){
              return B(A1(_t0/* sl87 */,_t3/* sl8a */));
            }), _t1/* sl88 */.a);});
          };
          return new T2(2,_sZ/* sl86 */,_t2/* sl8c */);
        case 1:
          var _t4/* sl8l */ = function(_t5/* sl8e */, _/* EXTERNAL */){
            var _t6/* sl8g */ = B(A1(_t1/* sl88 */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_s7/* sl4A */,new T(function(){
                return B(A1(_t0/* sl87 */,_t5/* sl8e */));
              }), _t6/* sl8g */));
            });
          };
          return new T2(3,_sZ/* sl86 */,_t4/* sl8l */);
        default:
          return new F(function(){return _sa/* sl4D */(_/* EXTERNAL */);});
      }
      break;
    default:
      var _t7/* sl8m */ = _sC/* sl77 */.a,
      _t8/* sl8n */ = _sC/* sl77 */.b,
      _t9/* sl8o */ = E(_s9/* sl4C */);
      switch(_t9/* sl8o */._){
        case 0:
          var _ta/* sl8w */ = function(_tb/* sl8q */, _/* EXTERNAL */){
            var _tc/* sl8s */ = B(A2(_t8/* sl8n */,_tb/* sl8q */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_s7/* sl4A */,_tc/* sl8s */, _t9/* sl8o */.a));
            });
          };
          return new T2(3,_t7/* sl8m */,_ta/* sl8w */);
        case 1:
          var _td/* sl8H */ = function(_te/* sl8y */, _/* EXTERNAL */){
            var _tf/* sl8A */ = B(A2(_t8/* sl8n */,_te/* sl8y */, _/* EXTERNAL */)),
            _tg/* sl8D */ = B(A1(_t9/* sl8o */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_s7/* sl4A */,_tf/* sl8A */, _tg/* sl8D */));
            });
          };
          return new T2(3,_t7/* sl8m */,_td/* sl8H */);
        default:
          return new F(function(){return _sa/* sl4D */(_/* EXTERNAL */);});
      }
  }
},
_th/* plusDouble */ = function(_ti/* s18yY */, _tj/* s18yZ */){
  return E(_ti/* s18yY */)+E(_tj/* s18yZ */);
},
_tk/* Zero */ = 0,
_tl/* sleep1 */ = function(_tm/* sc1a */, _tn/* sc1b */, _to/* sc1c */){
  var _tp/* sc32 */ = function(_tq/* sc1d */){
    var _tr/* sc1e */ = E(_tq/* sc1d */),
    _ts/* sc1g */ = _tr/* sc1e */.b,
    _tt/* sc1h */ = new T(function(){
      return E(_tr/* sc1e */.a)+E(_tm/* sc1a */)|0;
    }),
    _tu/* sc31 */ = function(_/* EXTERNAL */){
      var _tv/* sc1o */ = nMV/* EXTERNAL */(_ii/* Core.World.Internal.waitUntil2 */),
      _tw/* sc1q */ = _tv/* sc1o */;
      return new T(function(){
        var _tx/* sc2Z */ = function(_ty/* sc2P */){
          var _tz/* sc2T */ = new T(function(){
            return B(A1(_to/* sc1c */,new T2(0,_7/* GHC.Tuple.() */,E(_ty/* sc2P */).b)));
          });
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_tw/* sc1q */, function(_tA/* sc2V */){
            return E(_tz/* sc2T */);
          })));
        },
        _tB/* sc1s */ = new T2(0,_tt/* sc1h */,_tw/* sc1q */),
        _tC/* sc2O */ = function(_tD/* sc1u */){
          var _tE/* sc1v */ = new T(function(){
            var _tF/* sc1w */ = E(_tD/* sc1u */),
            _tG/* sc1B */ = E(_tF/* sc1w */.c);
            if(!_tG/* sc1B */._){
              var _tH/* sc1B#result */ = E(new T3(1,1,_tB/* sc1s */,E(_ax/* Data.PQueue.Internals.Nil */)));
            }else{
              var _tI/* sc1C */ = _tG/* sc1B */.a,
              _tJ/* sc1E */ = _tG/* sc1B */.c,
              _tK/* sc1F */ = E(_tG/* sc1B */.b),
              _tL/* sc1I */ = E(_tt/* sc1h */),
              _tM/* sc1K */ = E(_tK/* sc1F */.a);
              if(_tL/* sc1I */>=_tM/* sc1K */){
                if(_tL/* sc1I */!=_tM/* sc1K */){
                  var _tN/* sc1P#result */ = new T3(1,_tI/* sc1C */+1|0,_tK/* sc1F */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_tO/* sc1Q */, _tP/* sc1R */){
                    var _tQ/* sc1Y */ = E(E(_tO/* sc1Q */).a),
                    _tR/* sc20 */ = E(E(_tP/* sc1R */).a);
                    return (_tQ/* sc1Y */>=_tR/* sc20 */) ? _tQ/* sc1Y */==_tR/* sc20 */ : true;
                  }, _tB/* sc1s */, _tk/* Data.PQueue.Internals.Zero */, _tJ/* sc1E */))));
                }else{
                  var _tN/* sc1P#result */ = new T3(1,_tI/* sc1C */+1|0,_tB/* sc1s */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_tS/* sc28 */, _tT/* sc29 */){
                    var _tU/* sc2g */ = E(E(_tS/* sc28 */).a),
                    _tV/* sc2i */ = E(E(_tT/* sc29 */).a);
                    return (_tU/* sc2g */>=_tV/* sc2i */) ? _tU/* sc2g */==_tV/* sc2i */ : true;
                  }, _tK/* sc1F */, _tk/* Data.PQueue.Internals.Zero */, _tJ/* sc1E */))));
                }
                var _tW/* sc1N#result */ = _tN/* sc1P#result */;
              }else{
                var _tW/* sc1N#result */ = new T3(1,_tI/* sc1C */+1|0,_tB/* sc1s */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_tX/* sc2q */, _tY/* sc2r */){
                  var _tZ/* sc2y */ = E(E(_tX/* sc2q */).a),
                  _u0/* sc2A */ = E(E(_tY/* sc2r */).a);
                  return (_tZ/* sc2y */>=_u0/* sc2A */) ? _tZ/* sc2y */==_u0/* sc2A */ : true;
                }, _tK/* sc1F */, _tk/* Data.PQueue.Internals.Zero */, _tJ/* sc1E */))));
              }
              var _tH/* sc1B#result */ = _tW/* sc1N#result */;
            }
            return new T4(0,E(_tF/* sc1w */.a),_tF/* sc1w */.b,E(_tH/* sc1B#result */),E(_tF/* sc1w */.d));
          });
          return function(_u1/* sc2K */, _u2/* sc2L */){
            return new F(function(){return A1(_u2/* sc2L */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,_tE/* sc1v */),_u1/* sc2K */));});
          };
        };
        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _ts/* sc1g */, _tC/* sc2O */, _ts/* sc1g */, _tx/* sc2Z */]));
      });
    };
    return new T1(0,_tu/* sc31 */);
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _tn/* sc1b */, _ar/* Core.World.Internal.a */, _tn/* sc1b */, _tp/* sc32 */]);});
},
_u3/* $wa */ = function(_u4/* sNuL */, _u5/* sNuM */, _u6/* sNuN */){
  return function(_/* EXTERNAL */){
    var _u7/* sNuP */ = nMV/* EXTERNAL */(_rM/* Motion.Bounce.lvl16 */),
    _u8/* sNuR */ = _u7/* sNuP */,
    _u9/* sNuT */ = function(_ua/* sNuU */){
      return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _ll/* Motion.Bounce.dur */, _lh/* Motion.Bounce.a4 */, _u8/* sNuR */, _lg/* Motion.Bounce.a */, function(_ub/* sNuV */){
        return E(_ua/* sNuU */);
      });});
    },
    _uc/* sNuX */ = function(_ud/* sNuY */){
      return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _ll/* Motion.Bounce.dur */, _lm/* Motion.Bounce.e */, _u8/* sNuR */, _rO/* Motion.Bounce.lvl3 */, function(_ue/* sNuZ */){
        return E(_ud/* sNuY */);
      });});
    },
    _uf/* sNCB */ = function(_/* EXTERNAL */){
      var _ug/* sNv2 */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
      _uh/* sNv4 */ = _ug/* sNv2 */,
      _ui/* sNv6 */ = new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_uh/* sNv4 */),
      _uj/* sNCz */ = function(_/* EXTERNAL */){
        var _uk/* sNv8 */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
        _ul/* sNva */ = _uk/* sNv8 */,
        _um/* sNCx */ = function(_/* EXTERNAL */){
          var _un/* sNvd */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
          _uo/* sNvf */ = _un/* sNvd */,
          _up/* sNvh */ = new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_uo/* sNvf */),
          _uq/* sNCv */ = function(_/* EXTERNAL */){
            var _ur/* sNvj */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
            _us/* sNvl */ = _ur/* sNvj */,
            _ut/* sNCt */ = function(_/* EXTERNAL */){
              var _uu/* sNvo */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
              _uv/* sNvq */ = _uu/* sNvo */,
              _uw/* sNCr */ = function(_/* EXTERNAL */){
                var _ux/* sNvt */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
                _uy/* sNvv */ = _ux/* sNvt */,
                _uz/* sNCp */ = function(_/* EXTERNAL */){
                  var _uA/* sNvy */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
                  _uB/* sNvA */ = _uA/* sNvy */,
                  _uC/* sNvC */ = new T(function(){
                    return B(_jD/* Core.Ease.$wforceTo */(_uB/* sNvA */, _rN/* Motion.Bounce.lvl2 */));
                  }),
                  _uD/* sNCn */ = function(_/* EXTERNAL */){
                    var _uE/* sNvE */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
                    _uF/* sNvG */ = _uE/* sNvE */,
                    _uG/* sNCl */ = function(_/* EXTERNAL */){
                      var _uH/* sNvJ */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
                      _uI/* sNvL */ = _uH/* sNvJ */,
                      _uJ/* sNvN */ = new T(function(){
                        return B(_jD/* Core.Ease.$wforceTo */(_uI/* sNvL */, _rD/* Motion.Bounce.lvl1 */));
                      }),
                      _uK/* sNCj */ = function(_/* EXTERNAL */){
                        var _uL/* sNvP */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
                        _uM/* sNvR */ = _uL/* sNvP */,
                        _uN/* sNvT */ = new T(function(){
                          return B(_jD/* Core.Ease.$wforceTo */(_uM/* sNvR */, _rD/* Motion.Bounce.lvl1 */));
                        }),
                        _uO/* sNCh */ = function(_/* EXTERNAL */){
                          var _uP/* sNvV */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
                          _uQ/* sNvX */ = _uP/* sNvV */,
                          _uR/* sNCf */ = function(_/* EXTERNAL */){
                            var _uS/* sNw0 */ = nMV/* EXTERNAL */(_rJ/* Motion.Bounce.lvl13 */),
                            _uT/* sNw2 */ = _uS/* sNw0 */;
                            return new T(function(){
                              var _uU/* sNw5 */ = function(_uV/* sNwa */){
                                return new F(function(){return _uW/* sNw7 */(E(_uV/* sNwa */).b);});
                              },
                              _uX/* sNw6 */ = function(_uY/* sNwe */){
                                return new F(function(){return _tl/* Core.World.Internal.sleep1 */(_rQ/* Motion.Bounce.lvl5 */, E(_uY/* sNwe */).b, _uU/* sNw5 */);});
                              },
                              _uW/* sNw7 */ = function(_uZ/* sNwi */){
                                var _v0/* sNAX */ = function(_v1/* sNwj */){
                                  var _v2/* sNwk */ = new T(function(){
                                    var _v3/* sNAQ */ = function(_v4/* sNwl */){
                                      var _v5/* sNwm */ = new T(function(){
                                        var _v6/* sNAJ */ = function(_v7/* sNwn */){
                                          var _v8/* sNwo */ = new T(function(){
                                            var _v9/* sNAC */ = function(_va/* sNwp */){
                                              var _vb/* sNwq */ = new T(function(){
                                                var _vc/* sNAv */ = function(_vd/* sNwr */){
                                                  var _ve/* sNws */ = new T(function(){
                                                    var _vf/* sNwt */ = new T(function(){
                                                      return E(E(_vd/* sNwr */).a);
                                                    }),
                                                    _vg/* sNwx */ = new T(function(){
                                                      return B(_jD/* Core.Ease.$wforceTo */(_uh/* sNv4 */, new T(function(){
                                                        return (E(E(_v1/* sNwj */).a)+E(_vf/* sNwt */))*0.7;
                                                      })));
                                                    }),
                                                    _vh/* sNAo */ = function(_vi/* sNwI */){
                                                      var _vj/* sNwJ */ = new T(function(){
                                                        var _vk/* sNwK */ = new T(function(){
                                                          return E(E(_vi/* sNwI */).a);
                                                        }),
                                                        _vl/* sNwO */ = new T(function(){
                                                          return B(_jD/* Core.Ease.$wforceTo */(_ul/* sNva */, new T(function(){
                                                            return (E(E(_v4/* sNwl */).a)+E(_vk/* sNwK */))*0.7;
                                                          })));
                                                        }),
                                                        _vm/* sNAh */ = function(_vn/* sNwZ */){
                                                          var _vo/* sNx0 */ = new T(function(){
                                                            var _vp/* sNx1 */ = new T(function(){
                                                              return E(E(_vn/* sNwZ */).a);
                                                            }),
                                                            _vq/* sNx5 */ = new T(function(){
                                                              return B(_jD/* Core.Ease.$wforceTo */(_uo/* sNvf */, new T(function(){
                                                                return (E(E(_v7/* sNwn */).a)+E(_vp/* sNx1 */))*0.7;
                                                              })));
                                                            }),
                                                            _vr/* sNAa */ = function(_vs/* sNxg */){
                                                              var _vt/* sNxh */ = new T(function(){
                                                                var _vu/* sNxi */ = new T(function(){
                                                                  return E(E(_vs/* sNxg */).a);
                                                                }),
                                                                _vv/* sNxm */ = new T(function(){
                                                                  return B(_jD/* Core.Ease.$wforceTo */(_us/* sNvl */, new T(function(){
                                                                    return (E(E(_va/* sNwp */).a)+E(_vu/* sNxi */))*0.7;
                                                                  })));
                                                                }),
                                                                _vw/* sNxx */ = function(_vx/* sNxy */){
                                                                  return new F(function(){return A2(_vv/* sNxm */,E(_vx/* sNxy */).b, _uX/* sNw6 */);});
                                                                },
                                                                _vy/* sNxC */ = function(_vz/* sNxD */){
                                                                  return new F(function(){return A2(_vq/* sNx5 */,E(_vz/* sNxD */).b, _vw/* sNxx */);});
                                                                },
                                                                _vA/* sNxH */ = function(_vB/* sNxI */){
                                                                  return new F(function(){return A2(_vl/* sNwO */,E(_vB/* sNxI */).b, _vy/* sNxC */);});
                                                                },
                                                                _vC/* sNxM */ = function(_vD/* sNxN */){
                                                                  return new F(function(){return A2(_vg/* sNwx */,E(_vD/* sNxN */).b, _vA/* sNxH */);});
                                                                },
                                                                _vE/* sNA3 */ = function(_vF/* sNxR */){
                                                                  var _vG/* sNxS */ = new T(function(){
                                                                    var _vH/* sNxT */ = new T(function(){
                                                                      return E(E(_vF/* sNxR */).a);
                                                                    }),
                                                                    _vI/* sNxX */ = new T(function(){
                                                                      return B(_jD/* Core.Ease.$wforceTo */(_uI/* sNvL */, new T(function(){
                                                                        return E(_vH/* sNxT */)*0.7;
                                                                      })));
                                                                    }),
                                                                    _vJ/* sNy2 */ = new T(function(){
                                                                      return B(_jD/* Core.Ease.$wforceTo */(_uv/* sNvq */, new T(function(){
                                                                        return (E(_vf/* sNwt */)+E(_vH/* sNxT */))*0.7;
                                                                      })));
                                                                    }),
                                                                    _vK/* sNzW */ = function(_vL/* sNya */){
                                                                      var _vM/* sNyb */ = new T(function(){
                                                                        var _vN/* sNyc */ = new T(function(){
                                                                          return E(E(_vL/* sNya */).a);
                                                                        }),
                                                                        _vO/* sNyg */ = new T(function(){
                                                                          return B(_jD/* Core.Ease.$wforceTo */(_uM/* sNvR */, new T(function(){
                                                                            return E(_vN/* sNyc */)*0.7;
                                                                          })));
                                                                        }),
                                                                        _vP/* sNyl */ = new T(function(){
                                                                          return B(_jD/* Core.Ease.$wforceTo */(_uy/* sNvv */, new T(function(){
                                                                            return (E(_vk/* sNwK */)+E(_vN/* sNyc */))*0.7;
                                                                          })));
                                                                        }),
                                                                        _vQ/* sNzP */ = function(_vR/* sNyt */){
                                                                          var _vS/* sNyu */ = new T(function(){
                                                                            var _vT/* sNyv */ = new T(function(){
                                                                              return E(E(_vR/* sNyt */).a);
                                                                            }),
                                                                            _vU/* sNyz */ = new T(function(){
                                                                              return B(_jD/* Core.Ease.$wforceTo */(_uQ/* sNvX */, new T(function(){
                                                                                return E(_vT/* sNyv */)*0.7;
                                                                              })));
                                                                            }),
                                                                            _vV/* sNyE */ = new T(function(){
                                                                              return B(_jD/* Core.Ease.$wforceTo */(_uB/* sNvA */, new T(function(){
                                                                                return (E(_vp/* sNx1 */)+E(_vT/* sNyv */))*0.7;
                                                                              })));
                                                                            }),
                                                                            _vW/* sNzI */ = function(_vX/* sNyM */){
                                                                              var _vY/* sNyN */ = new T(function(){
                                                                                var _vZ/* sNyO */ = new T(function(){
                                                                                  return E(E(_vX/* sNyM */).a);
                                                                                }),
                                                                                _w0/* sNyS */ = new T(function(){
                                                                                  return B(_jD/* Core.Ease.$wforceTo */(_uT/* sNw2 */, new T(function(){
                                                                                    return E(_vZ/* sNyO */)*0.7;
                                                                                  })));
                                                                                }),
                                                                                _w1/* sNyX */ = new T(function(){
                                                                                  return B(_jD/* Core.Ease.$wforceTo */(_uF/* sNvG */, new T(function(){
                                                                                    return (E(_vu/* sNxi */)+E(_vZ/* sNyO */))*0.7;
                                                                                  })));
                                                                                }),
                                                                                _w2/* sNz5 */ = function(_w3/* sNz6 */){
                                                                                  return new F(function(){return A2(_w1/* sNyX */,E(_w3/* sNz6 */).b, _vC/* sNxM */);});
                                                                                },
                                                                                _w4/* sNza */ = function(_w5/* sNzb */){
                                                                                  return new F(function(){return A2(_vV/* sNyE */,E(_w5/* sNzb */).b, _w2/* sNz5 */);});
                                                                                },
                                                                                _w6/* sNzf */ = function(_w7/* sNzg */){
                                                                                  return new F(function(){return A2(_vP/* sNyl */,E(_w7/* sNzg */).b, _w4/* sNza */);});
                                                                                },
                                                                                _w8/* sNzk */ = function(_w9/* sNzl */){
                                                                                  return new F(function(){return A2(_vJ/* sNy2 */,E(_w9/* sNzl */).b, _w6/* sNzf */);});
                                                                                },
                                                                                _wa/* sNzp */ = function(_wb/* sNzq */){
                                                                                  return new F(function(){return A2(_w0/* sNyS */,E(_wb/* sNzq */).b, _w8/* sNzk */);});
                                                                                },
                                                                                _wc/* sNzu */ = function(_wd/* sNzv */){
                                                                                  return new F(function(){return A2(_vU/* sNyz */,E(_wd/* sNzv */).b, _wa/* sNzp */);});
                                                                                };
                                                                                return B(A2(_vI/* sNxX */,_uZ/* sNwi */, function(_we/* sNzz */){
                                                                                  return new F(function(){return A2(_vO/* sNyg */,E(_we/* sNzz */).b, _wc/* sNzu */);});
                                                                                }));
                                                                              });
                                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uT/* sNw2 */, _vX/* sNyM */, function(_wf/* sNzE */){
                                                                                return E(_vY/* sNyN */);
                                                                              })));
                                                                            };
                                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uT/* sNw2 */, _vW/* sNzI */)));
                                                                          });
                                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uQ/* sNvX */, _vR/* sNyt */, function(_wg/* sNzL */){
                                                                            return E(_vS/* sNyu */);
                                                                          })));
                                                                        };
                                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uQ/* sNvX */, _vQ/* sNzP */)));
                                                                      });
                                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uM/* sNvR */, _vL/* sNya */, function(_wh/* sNzS */){
                                                                        return E(_vM/* sNyb */);
                                                                      })));
                                                                    };
                                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uM/* sNvR */, _vK/* sNzW */)));
                                                                  });
                                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uI/* sNvL */, _vF/* sNxR */, function(_wi/* sNzZ */){
                                                                    return E(_vG/* sNxS */);
                                                                  })));
                                                                };
                                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uI/* sNvL */, _vE/* sNA3 */)));
                                                              });
                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uF/* sNvG */, _vs/* sNxg */, function(_wj/* sNA6 */){
                                                                return E(_vt/* sNxh */);
                                                              })));
                                                            };
                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uF/* sNvG */, _vr/* sNAa */)));
                                                          });
                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uB/* sNvA */, _vn/* sNwZ */, function(_wk/* sNAd */){
                                                            return E(_vo/* sNx0 */);
                                                          })));
                                                        };
                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uB/* sNvA */, _vm/* sNAh */)));
                                                      });
                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uy/* sNvv */, _vi/* sNwI */, function(_wl/* sNAk */){
                                                        return E(_vj/* sNwJ */);
                                                      })));
                                                    };
                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uy/* sNvv */, _vh/* sNAo */)));
                                                  });
                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uv/* sNvq */, _vd/* sNwr */, function(_wm/* sNAr */){
                                                    return E(_ve/* sNws */);
                                                  })));
                                                };
                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uv/* sNvq */, _vc/* sNAv */)));
                                              });
                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_us/* sNvl */, _va/* sNwp */, function(_wn/* sNAy */){
                                                return E(_vb/* sNwq */);
                                              })));
                                            };
                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_us/* sNvl */, _v9/* sNAC */)));
                                          });
                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uo/* sNvf */, _v7/* sNwn */, function(_wo/* sNAF */){
                                            return E(_v8/* sNwo */);
                                          })));
                                        };
                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uo/* sNvf */, _v6/* sNAJ */)));
                                      });
                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_ul/* sNva */, _v4/* sNwl */, function(_wp/* sNAM */){
                                        return E(_v5/* sNwm */);
                                      })));
                                    };
                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_ul/* sNva */, _v3/* sNAQ */)));
                                  });
                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uh/* sNv4 */, _v1/* sNwj */, function(_wq/* sNAT */){
                                    return E(_v2/* sNwk */);
                                  })));
                                };
                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uh/* sNv4 */, _v0/* sNAX */)));
                              },
                              _wr/* sNB0 */ = new T(function(){
                                return B(_jD/* Core.Ease.$wforceTo */(_uT/* sNw2 */, _rP/* Motion.Bounce.lvl4 */));
                              }),
                              _ws/* sNB2 */ = function(_wt/* sNBc */){
                                return new F(function(){return _wu/* sNB9 */(E(_wt/* sNBc */).b);});
                              },
                              _wv/* sNB3 */ = function(_ww/* sNBg */){
                                return new F(function(){return _tl/* Core.World.Internal.sleep1 */(_rC/* Motion.Bounce.lvl */, E(_ww/* sNBg */).b, _ws/* sNB2 */);});
                              },
                              _wx/* sNB4 */ = function(_wy/* sNBk */){
                                return new F(function(){return A2(_uN/* sNvT */,E(_wy/* sNBk */).b, _wv/* sNB3 */);});
                              },
                              _wz/* sNB5 */ = function(_wA/* sNBo */){
                                return new F(function(){return A2(_uJ/* sNvN */,E(_wA/* sNBo */).b, _wx/* sNB4 */);});
                              },
                              _wB/* sNB6 */ = function(_wC/* sNBs */){
                                return new F(function(){return A2(_uC/* sNvC */,E(_wC/* sNBs */).b, _wz/* sNB5 */);});
                              },
                              _wD/* sNB7 */ = function(_wE/* sNBw */){
                                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_u9/* sNuT */, E(_wE/* sNBw */).b, _wB/* sNB6 */)));
                              },
                              _wF/* sNB8 */ = function(_wG/* sNBC */){
                                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_uc/* sNuX */, E(_wG/* sNBC */).b, _wD/* sNB7 */)));
                              },
                              _wu/* sNB9 */ = function(_wH/* sNBI */){
                                return new F(function(){return A2(_wr/* sNB0 */,_wH/* sNBI */, _wF/* sNB8 */);});
                              },
                              _wI/* sNCb */ = function(_wJ/* sNC5 */, _wK/* sNC6 */){
                                return new T1(1,new T2(1,new T(function(){
                                  return B(_wu/* sNB9 */(_wJ/* sNC5 */));
                                }),new T2(1,new T(function(){
                                  return B(_uW/* sNw7 */(_wJ/* sNC5 */));
                                }),_6/* GHC.Types.[] */)));
                              },
                              _wL/* sNC4 */ = new T(function(){
                                var _wM/* sNC3 */ = new T(function(){
                                  var _wN/* sNBZ */ = B(_kr/* Core.Shape.Internal.$wrect */(new T(function(){
                                    return B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, _rV/* Motion.Bounce.lvl8 */, new T2(2,_ui/* sNv6 */,_rE/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, new T2(2,new T3(0,_ll/* Motion.Bounce.dur */,_lm/* Motion.Bounce.e */,_u8/* sNuR */),_2E/* GHC.Base.id */), new T2(2,_up/* sNvh */,_rE/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, _rT/* Motion.Bounce.lvl7 */, new T2(2,_ui/* sNv6 */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_ul/* sNva */),_2E/* GHC.Base.id */)));
                                  }), new T(function(){
                                    return B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, _rR/* Motion.Bounce.lvl6 */, new T2(2,_up/* sNvh */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_us/* sNvl */),_2E/* GHC.Base.id */)));
                                  })));
                                  return new T3(0,_wN/* sNBZ */.a,_wN/* sNBZ */.b,_wN/* sNBZ */.c);
                                });
                                return B(_rr/* Core.Render.Internal.fill1 */(_u4/* sNuL */, _wM/* sNC3 */));
                              });
                              return B(A1(_u6/* sNuN */,new T2(0,new T2(0,_wL/* sNC4 */,_wI/* sNCb */),_u5/* sNuM */)));
                            });
                          };
                          return new T1(0,_uR/* sNCf */);
                        };
                        return new T1(0,_uO/* sNCh */);
                      };
                      return new T1(0,_uK/* sNCj */);
                    };
                    return new T1(0,_uG/* sNCl */);
                  };
                  return new T1(0,_uD/* sNCn */);
                };
                return new T1(0,_uz/* sNCp */);
              };
              return new T1(0,_uw/* sNCr */);
            };
            return new T1(0,_ut/* sNCt */);
          };
          return new T1(0,_uq/* sNCv */);
        };
        return new T1(0,_um/* sNCx */);
      };
      return new T1(0,_uj/* sNCz */);
    };
    return new T1(0,_uf/* sNCB */);
  };
},
_wO/* bounceMot1 */ = function(_wP/* sNCE */, _wQ/* sNCF */, _wR/* sNCG */){
  return new T1(0,B(_u3/* Motion.Bounce.$wa */(_wP/* sNCE */, _wQ/* sNCF */, _wR/* sNCG */)));
},
_wS/* clip_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.restore();})");
}),
_wT/* clip5 */ = function(_wU/* sFxI */, _/* EXTERNAL */){
  var _wV/* sFxP */ = __app1/* EXTERNAL */(E(_wS/* Core.Render.Internal.clip_f1 */), E(_wU/* sFxI */));
  return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_wW/* clip4 */ = new T2(0,_wT/* Core.Render.Internal.clip5 */,_7/* GHC.Tuple.() */),
_wX/* clip3 */ = new T(function(){
  return B(_rn/* Control.Monad.Skeleton.bone */(_wW/* Core.Render.Internal.clip4 */));
}),
_wY/* clip2 */ = function(_wZ/* sFxS */){
  return E(_wX/* Core.Render.Internal.clip3 */);
},
_x0/* clip1 */ = new T1(1,_wY/* Core.Render.Internal.clip2 */),
_x1/* clip_f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.save();})");
}),
_x2/* getImage2 */ = function(_x3/* sFgp */, _x4/* sFgq */, _/* EXTERNAL */){
  var _x5/* sFgs */ = E(_x3/* sFgp */);
  switch(_x5/* sFgs */._){
    case 0:
      return new F(function(){return A2(_x4/* sFgq */,_x5/* sFgs */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _x6/* sFgv */ = B(A1(_x5/* sFgs */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_x4/* sFgq */,_x6/* sFgv */, _/* EXTERNAL */);});
      break;
    case 2:
      var _x7/* sFgG */ = rMV/* EXTERNAL */(E(E(_x5/* sFgs */.a).c)),
      _x8/* sFgJ */ = E(_x7/* sFgG */);
      if(!_x8/* sFgJ */._){
        var _x9/* sFgN */ = new T(function(){
          return B(A1(_x5/* sFgs */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_x8/* sFgJ */.a));
          })));
        });
        return new F(function(){return A2(_x4/* sFgq */,_x9/* sFgN */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _xa/* sFgX */ = rMV/* EXTERNAL */(E(E(_x5/* sFgs */.a).c)),
      _xb/* sFh0 */ = E(_xa/* sFgX */);
      if(!_xb/* sFh0 */._){
        var _xc/* sFh6 */ = B(A2(_x5/* sFgs */.b,E(_xb/* sFh0 */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_x4/* sFgq */,_xc/* sFh6 */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
  }
},
_xd/* lvl10 */ = "shadowBlur",
_xe/* lvl7 */ = "shadowColor",
_xf/* lvl8 */ = "shadowOffsetX",
_xg/* lvl9 */ = "shadowOffsetY",
_xh/* $wshadowed */ = function(_xi/* sFQ7 */, _xj/* sFQ8 */, _xk/* sFQ9 */, _xl/* sFQa */, _xm/* sFQb */){
  var _xn/* sFRs */ = function(_xo/* sFQc */, _/* EXTERNAL */){
    var _xp/* sFRr */ = function(_xq/* sFQe */, _/* EXTERNAL */){
      var _xr/* sFRq */ = function(_xs/* sFQg */, _/* EXTERNAL */){
        return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_xk/* sFQ9 */, function(_xt/* sFQi */, _/* EXTERNAL */){
          var _xu/* sFQk */ = E(_xl/* sFQa */),
          _xv/* sFQp */ = B(_lt/* Core.Render.Internal.$wa */(_xu/* sFQk */.a, _xu/* sFQk */.b, _xu/* sFQk */.c, _xu/* sFQk */.d, _/* EXTERNAL */)),
          _xw/* sFQs */ = E(_xo/* sFQc */),
          _xx/* sFQx */ = __app1/* EXTERNAL */(E(_x1/* Core.Render.Internal.clip_f4 */), _xw/* sFQs */),
          _xy/* sFQD */ = E(_ic/* Haste.DOM.Core.jsSet_f1 */),
          _xz/* sFQG */ = __app3/* EXTERNAL */(_xy/* sFQD */, _xw/* sFQs */, E(_xe/* Core.Render.Internal.lvl7 */), B(_qb/* Core.Render.Internal.$wcolor2JSString */(_xv/* sFQp */))),
          _xA/* sFQO */ = String/* EXTERNAL */(E(_xq/* sFQe */)),
          _xB/* sFQS */ = __app3/* EXTERNAL */(_xy/* sFQD */, _xw/* sFQs */, E(_xf/* Core.Render.Internal.lvl8 */), _xA/* sFQO */),
          _xC/* sFR0 */ = String/* EXTERNAL */(E(_xs/* sFQg */)),
          _xD/* sFR4 */ = __app3/* EXTERNAL */(_xy/* sFQD */, _xw/* sFQs */, E(_xg/* Core.Render.Internal.lvl9 */), _xC/* sFR0 */),
          _xE/* sFRc */ = String/* EXTERNAL */(E(_xt/* sFQi */)),
          _xF/* sFRg */ = __app3/* EXTERNAL */(_xy/* sFQD */, _xw/* sFQs */, E(_xd/* Core.Render.Internal.lvl10 */), _xE/* sFRc */),
          _xG/* sFRm */ = __app1/* EXTERNAL */(E(_ro/* Core.Render.Internal.clip_f3 */), _xw/* sFQs */);
          return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _/* EXTERNAL */);});
      };
      return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_xj/* sFQ8 */, _xr/* sFRq */, _/* EXTERNAL */);});
    };
    return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_xi/* sFQ7 */, _xp/* sFRr */, _/* EXTERNAL */);});
  },
  _xH/* sFRu */ = B(_rn/* Control.Monad.Skeleton.bone */(new T2(0,_xn/* sFRs */,_7/* GHC.Tuple.() */)));
  return new T2(0,E(_xH/* sFRu */.a),E(new T2(2,new T2(2,_xH/* sFRu */.b,new T1(1,function(_xI/* sFRx */){
    return E(_xm/* sFQb */);
  })),_x0/* Core.Render.Internal.clip1 */)));
},
_xJ/* $fAffineShape_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,_){ctx.restore();})");
}),
_xK/* $fApplicativeShape4 */ = function(_/* EXTERNAL */){
  return _av/* GHC.Types.False */;
},
_xL/* $fApplicativeShape3 */ = function(_xM/* stcD */, _/* EXTERNAL */){
  return new F(function(){return _xK/* Core.Shape.Internal.$fApplicativeShape4 */(_/* EXTERNAL */);});
},
_xN/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,_){ctx.save();})");
}),
_xO/* f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.scale(x,y);})");
}),
_xP/* f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(str,x,y,ctx,_){ctx.strokeText(str,x,y);})");
}),
_xQ/* f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(str,x,y,ctx,_){ctx.fillText(str,x,y);})");
}),
_xR/* f5 */ = new T(function(){
  return eval/* EXTERNAL */("(function(x,y,ctx,_){ctx.translate(x,y);})");
}),
_xS/* lvl */ = "alphabetic",
_xT/* lvl1 */ = "middle",
_xU/* lvl2 */ = "hanging",
_xV/* lvl3 */ = "right",
_xW/* lvl4 */ = "center",
_xX/* lvl5 */ = "left",
_xY/* lvl6 */ = "(function(fn,a,b,ctx){ctx.font=\"10px \"+fn;ctx.textAlign=a;ctx.textBaseline=b;})",
_xZ/* $wtext */ = function(_y0/* stTg */, _y1/* stTh */, _y2/* stTi */, _y3/* stTj */, _y4/* stTk */, _y5/* stTl */, _y6/* stTm */){
  var _y7/* stVu */ = function(_y8/* stTn */, _y9/* stTo */, _ya/* stTp */, _/* EXTERNAL */){
    var _yb/* stVt */ = function(_yc/* stTr */, _yd/* stTs */, _ye/* stTt */, _/* EXTERNAL */){
      var _yf/* stVs */ = function(_yg/* stTv */, _yh/* stTw */, _yi/* stTx */, _/* EXTERNAL */){
        var _yj/* stVr */ = function(_yk/* stTz */, _yl/* stTA */, _ym/* stTB */, _/* EXTERNAL */){
          var _yn/* stTD */ = E(_yl/* stTA */),
          _yo/* stTH */ = E(_ym/* stTB */),
          _yp/* stTK */ = __app2/* EXTERNAL */(E(_xN/* Core.Shape.Internal.f1 */), _yn/* stTD */, _yo/* stTH */),
          _yq/* stTP */ = function(_yr/* stTQ */){
            var _ys/* stTR */ = function(_yt/* stTS */){
              var _yu/* stTW */ = eval/* EXTERNAL */(E(_xY/* Core.Shape.Internal.lvl6 */)),
              _yv/* stU4 */ = __app4/* EXTERNAL */(E(_yu/* stTW */), E(_y0/* stTg */), _yr/* stTQ */, _yt/* stTS */, _yn/* stTD */),
              _yw/* stUi */ = __app4/* EXTERNAL */(E(_xR/* Core.Shape.Internal.f5 */), E(_yc/* stTr */), E(_yg/* stTv */), _yn/* stTD */, _yo/* stTH */),
              _yx/* stUn */ = E(_yk/* stTz */)/10,
              _yy/* stUt */ = __app4/* EXTERNAL */(E(_xO/* Core.Shape.Internal.f2 */), _yx/* stUn */, _yx/* stUn */, _yn/* stTD */, _yo/* stTH */);
              if(!_yo/* stTH */){
                var _yz/* stUJ */ = __app5/* EXTERNAL */(E(_xP/* Core.Shape.Internal.f3 */), toJSStr/* EXTERNAL */(E(_y8/* stTn */)), 0, 0, _yn/* stTD */, false),
                _yA/* stUP */ = __app2/* EXTERNAL */(E(_xJ/* Core.Shape.Internal.$fAffineShape_f1 */), _yn/* stTD */, false);
                return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }else{
                var _yB/* stV4 */ = __app5/* EXTERNAL */(E(_xQ/* Core.Shape.Internal.f4 */), toJSStr/* EXTERNAL */(E(_y8/* stTn */)), 0, 0, _yn/* stTD */, true),
                _yC/* stVa */ = __app2/* EXTERNAL */(E(_xJ/* Core.Shape.Internal.$fAffineShape_f1 */), _yn/* stTD */, true);
                return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }
            };
            switch(E(_y3/* stTj */)){
              case 0:
                return new F(function(){return _ys/* stTR */(E(_xU/* Core.Shape.Internal.lvl2 */));});
                break;
              case 1:
                return new F(function(){return _ys/* stTR */(E(_xT/* Core.Shape.Internal.lvl1 */));});
                break;
              default:
                return new F(function(){return _ys/* stTR */(E(_xS/* Core.Shape.Internal.lvl */));});
            }
          };
          switch(E(_y2/* stTi */)){
            case 0:
              return new F(function(){return _yq/* stTP */(E(_xX/* Core.Shape.Internal.lvl5 */));});
              break;
            case 1:
              return new F(function(){return _yq/* stTP */(E(_xW/* Core.Shape.Internal.lvl4 */));});
              break;
            default:
              return new F(function(){return _yq/* stTP */(E(_xV/* Core.Shape.Internal.lvl3 */));});
          }
        };
        return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_y6/* stTm */, _yj/* stVr */, _yh/* stTw */, _yi/* stTx */, _/* EXTERNAL */);});
      };
      return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_y5/* stTl */, _yf/* stVs */, _yd/* stTs */, _ye/* stTt */, _/* EXTERNAL */);});
    };
    return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_y4/* stTk */, _yb/* stVt */, _y9/* stTo */, _ya/* stTp */, _/* EXTERNAL */);});
  };
  return new T3(0,_xL/* Core.Shape.Internal.$fApplicativeShape3 */,function(_le/* B3 */, _lf/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_y1/* stTh */, _y7/* stVu */, _le/* B3 */, _lf/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_yD/* BottomBase */ = 2,
_yE/* Just */ = function(_yF/* B1 */){
  return new T1(1,_yF/* B1 */);
},
_yG/* LeftAlign */ = 0,
_yH/* TopBase */ = 0,
_yI/* a15 */ = 0,
_yJ/* lvl4 */ = new T1(0,_yI/* Motion.Main.a15 */),
_yK/* size */ = 150,
_yL/* sz */ = new T1(0,_yK/* Motion.Main.size */),
_yM/* shape */ = new T(function(){
  var _yN/* s7Db */ = B(_kr/* Core.Shape.Internal.$wrect */(_yJ/* Motion.Main.lvl4 */, _yJ/* Motion.Main.lvl4 */, _yL/* Motion.Main.sz */, _yL/* Motion.Main.sz */));
  return new T3(0,_yN/* s7Db */.a,_yN/* s7Db */.b,_yN/* s7Db */.c);
}),
_yO/* black1 */ = new T1(0,_f3/* Core.Render.Internal.applyTransform2 */),
_yP/* white */ = new T4(0,_yO/* Core.Render.Internal.black1 */,_yO/* Core.Render.Internal.black1 */,_yO/* Core.Render.Internal.black1 */,_yO/* Core.Render.Internal.black1 */),
_yQ/* a17 */ = new T(function(){
  return B(_rr/* Core.Render.Internal.fill1 */(_yP/* Core.Render.Internal.white */, _yM/* Motion.Main.shape */));
}),
_yR/* a23 */ = function(_yS/* s7Df */, _yT/* s7Dg */){
  return new F(function(){return A1(_yT/* s7Dg */,new T2(0,_7/* GHC.Tuple.() */,_yS/* s7Df */));});
},
_yU/* black2 */ = new T1(0,_f2/* Core.Render.Internal.applyTransform1 */),
_yV/* black */ = new T4(0,_yU/* Core.Render.Internal.black2 */,_yU/* Core.Render.Internal.black2 */,_yU/* Core.Render.Internal.black2 */,_yO/* Core.Render.Internal.black1 */),
_yW/* Leave */ = 2,
_yX/* lvl2 */ = function(_yY/* sZro */){
  switch(E(_yY/* sZro */)){
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
_yZ/* lvl3 */ = function(_z0/* sZrq */){
  return (E(_z0/* sZrq */)==2) ? true : false;
},
_z1/* lvl4 */ = function(_z2/* sZrs */){
  switch(E(_z2/* sZrs */)){
    case 5:
      return true;
    case 6:
      return true;
    default:
      return false;
  }
},
_z3/* waitFor */ = function(_z4/* s6dr */, _z5/* s6ds */, _z6/* s6dt */){
  var _z7/* s6du */ = new T(function(){
    return B(_z3/* Core.Util.waitFor */(_z4/* s6dr */, _z5/* s6ds */, _z6/* s6dt */));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_z4/* s6dr */, _z6/* s6dt */, function(_z8/* s6dv */){
    if(!B(A1(_z5/* s6ds */,_z8/* s6dv */))){
      return E(_z7/* s6du */);
    }else{
      return new F(function(){return A2(_6T/* GHC.Base.return */,_z4/* s6dr */, _z8/* s6dv */);});
    }
  });});
},
_z9/* button */ = function(_za/* sZru */, _zb/* sZrv */, _zc/* sZrw */, _zd/* sZrx */){
  var _ze/* sZry */ = new T(function(){
    var _zf/* sZrz */ = new T(function(){
      var _zg/* sZrH */ = function(_zh/* sZrA */, _zi/* sZrB */){
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zd/* sZrx */, function(_zj/* sZrC */){
          return new F(function(){return A1(_zi/* sZrB */,new T2(0,_zj/* sZrC */,_zh/* sZrA */));});
        })));
      };
      return B(_z3/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _z1/* Core.UI.lvl4 */, _zg/* sZrH */));
    }),
    _zk/* sZs4 */ = function(_zl/* sZrI */, _zm/* sZrJ */){
      var _zn/* sZrK */ = new T(function(){
        var _zo/* sZrX */ = function(_zp/* sZrL */){
          var _zq/* sZrM */ = E(_zp/* sZrL */),
          _zr/* sZrO */ = _zq/* sZrM */.b,
          _zs/* sZrP */ = E(_zq/* sZrM */.a);
          if(_zs/* sZrP */==6){
            return new F(function(){return A1(_zm/* sZrJ */,new T2(0,_yW/* Core.View.Leave */,_zr/* sZrO */));});
          }else{
            return new F(function(){return A2(_zc/* sZrw */,_zr/* sZrO */, function(_zt/* sZrQ */){
              return new F(function(){return A1(_zm/* sZrJ */,new T2(0,_zs/* sZrP */,E(_zt/* sZrQ */).b));});
            });});
          }
        };
        return B(A2(_zf/* sZrz */,_zl/* sZrI */, _zo/* sZrX */));
      });
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zd/* sZrx */, function(_zu/* sZrY */){
        var _zv/* sZrZ */ = E(_zu/* sZrY */);
        if(_zv/* sZrZ */==3){
          return E(_zn/* sZrK */);
        }else{
          return new F(function(){return A1(_zm/* sZrJ */,new T2(0,_zv/* sZrZ */,_zl/* sZrI */));});
        }
      })));
    };
    return B(_z3/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _yZ/* Core.UI.lvl3 */, _zk/* sZs4 */));
  }),
  _zw/* sZs5 */ = new T(function(){
    var _zx/* sZsd */ = function(_zy/* sZs6 */, _zz/* sZs7 */){
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zd/* sZrx */, function(_zA/* sZs8 */){
        return new F(function(){return A1(_zz/* sZs7 */,new T2(0,_zA/* sZs8 */,_zy/* sZs6 */));});
      })));
    };
    return B(_z3/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _yX/* Core.UI.lvl2 */, _zx/* sZsd */));
  }),
  _zB/* sZse */ = function(_zC/* sZsf */){
    var _zD/* sZsg */ = new T(function(){
      return B(A1(_za/* sZru */,_zC/* sZsf */));
    }),
    _zE/* sZsC */ = function(_zF/* sZsh */){
      var _zG/* sZsi */ = function(_zH/* sZsj */){
        return new F(function(){return A2(_zB/* sZse */,E(_zH/* sZsj */).b, _zF/* sZsh */);});
      },
      _zI/* sZsn */ = function(_zJ/* sZso */){
        return new F(function(){return A2(_ze/* sZry */,E(_zJ/* sZso */).b, _zG/* sZsi */);});
      },
      _zK/* sZss */ = function(_zL/* sZst */){
        return new F(function(){return A2(_zb/* sZrv */,E(_zL/* sZst */).b, _zI/* sZsn */);});
      };
      return new F(function(){return A1(_zD/* sZsg */,function(_zM/* sZsx */){
        return new F(function(){return A2(_zw/* sZs5 */,E(_zM/* sZsx */).b, _zK/* sZss */);});
      });});
    };
    return E(_zE/* sZsC */);
  };
  return E(_zB/* sZse */);
},
_zN/* clip_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.clip();})");
}),
_zO/* clip */ = function(_zP/* sFxT */, _zQ/* sFxU */){
  var _zR/* sFyq */ = B(_rn/* Control.Monad.Skeleton.bone */(new T2(0,function(_zS/* sFxV */, _/* EXTERNAL */){
    var _zT/* sFxX */ = E(_zS/* sFxV */),
    _zU/* sFy2 */ = __app1/* EXTERNAL */(E(_x1/* Core.Render.Internal.clip_f4 */), _zT/* sFxX */),
    _zV/* sFy8 */ = __app1/* EXTERNAL */(E(_ro/* Core.Render.Internal.clip_f3 */), _zT/* sFxX */),
    _zW/* sFyf */ = B(A3(E(_zP/* sFxT */).b,_zT/* sFxX */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _zX/* sFyl */ = __app1/* EXTERNAL */(E(_zN/* Core.Render.Internal.clip_f2 */), _zT/* sFxX */);
    return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */)));
  return new T2(0,E(_zR/* sFyq */.a),E(new T2(2,new T2(2,_zR/* sFyq */.b,new T1(1,function(_zY/* sFyt */){
    return E(_zQ/* sFxU */);
  })),_x0/* Core.Render.Internal.clip1 */)));
},
_zZ/* easeTo2 */ = function(_A0/* sldx */, _A1/* sldy */){
  return new F(function(){return A1(_A1/* sldy */,new T2(0,_7/* GHC.Tuple.() */,_A0/* sldx */));});
},
_A2/* easeTo1 */ = function(_A3/* sldA */, _A4/* B2 */, _A5/* B1 */){
  return new F(function(){return _zZ/* Core.Ease.easeTo2 */(_A4/* B2 */, _A5/* B1 */);});
},
_A6/* linear */ = function(_A4/* B2 */, _A5/* B1 */){
  return new F(function(){return _lq/* Core.Ease.easeIn */(_A4/* B2 */, _A5/* B1 */);});
},
_A7/* a20 */ = 0.2,
_A8/* lvl9 */ = new T1(0,_A7/* Motion.Main.a20 */),
_A9/* lvl10 */ = new T4(0,_yJ/* Motion.Main.lvl4 */,_yJ/* Motion.Main.lvl4 */,_yJ/* Motion.Main.lvl4 */,_A8/* Motion.Main.lvl9 */),
_Aa/* a21 */ = 1,
_Ab/* lvl11 */ = new T1(0,_Aa/* Motion.Main.a21 */),
_Ac/* lvl12 */ = new T4(0,_A8/* Motion.Main.lvl9 */,_A8/* Motion.Main.lvl9 */,_A8/* Motion.Main.lvl9 */,_Ab/* Motion.Main.lvl11 */),
_Ad/* lvl13 */ = "mplus",
_Ae/* lvl14 */ = 1.2,
_Af/* lvl15 */ = new T1(0,_Ae/* Motion.Main.lvl14 */),
_Ag/* timesDouble */ = function(_Ah/* s18yK */, _Ai/* s18yL */){
  return E(_Ah/* s18yK */)*E(_Ai/* s18yL */);
},
_Aj/* lvl16 */ = new T(function(){
  return B(_s6/* Core.Ease.opLift */(_Ag/* GHC.Float.timesDouble */, _yL/* Motion.Main.sz */, _Af/* Motion.Main.lvl15 */));
}),
_Ak/* lvl17 */ = 2,
_Al/* lvl18 */ = new T1(0,_Ak/* Motion.Main.lvl17 */),
_Am/* lvl19 */ = new T(function(){
  return B(_s6/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, _yL/* Motion.Main.sz */, _Al/* Motion.Main.lvl18 */));
}),
_An/* lvl2 */ = 6,
_Ao/* lvl20 */ = 0.3,
_Ap/* lvl21 */ = new T1(0,_Ao/* Motion.Main.lvl20 */),
_Aq/* lvl22 */ = new T(function(){
  return B(_s6/* Core.Ease.opLift */(_Ag/* GHC.Float.timesDouble */, _yL/* Motion.Main.sz */, _Ap/* Motion.Main.lvl21 */));
}),
_Ar/* a22 */ = 0.5,
_As/* lvl23 */ = new T1(0,_Ar/* Motion.Main.a22 */),
_At/* lvl24 */ = new T4(0,_As/* Motion.Main.lvl23 */,_As/* Motion.Main.lvl23 */,_As/* Motion.Main.lvl23 */,_Ab/* Motion.Main.lvl11 */),
_Au/* lvl25 */ = 0.6,
_Av/* lvl26 */ = new T1(0,_Au/* Motion.Main.lvl25 */),
_Aw/* lvl27 */ = new T(function(){
  return B(_s6/* Core.Ease.opLift */(_Ag/* GHC.Float.timesDouble */, _yL/* Motion.Main.sz */, _Av/* Motion.Main.lvl26 */));
}),
_Ax/* lvl3 */ = 10,
_Ay/* lvl28 */ = 0.15,
_Az/* lvl29 */ = new T1(0,_Ay/* Motion.Main.lvl28 */),
_AA/* lvl30 */ = new T(function(){
  return B(_s6/* Core.Ease.opLift */(_Ag/* GHC.Float.timesDouble */, _yL/* Motion.Main.sz */, _Az/* Motion.Main.lvl29 */));
}),
_AB/* lvl31 */ = 15,
_AC/* lvl32 */ = function(_AD/* s7Di */){
  var _AE/* s7Dj */ = E(_AD/* s7Di */);
  return new T0(2);
},
_AF/* lvl33 */ = new T4(0,_An/* Motion.Main.lvl2 */,_An/* Motion.Main.lvl2 */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_AG/* lvl34 */ = new T2(0,_An/* Motion.Main.lvl2 */,_AF/* Motion.Main.lvl33 */),
_AH/* lvl35 */ = new T2(0,_AG/* Motion.Main.lvl34 */,_6/* GHC.Types.[] */),
_AI/* a16 */ = 3,
_AJ/* lvl5 */ = new T1(0,_AI/* Motion.Main.a16 */),
_AK/* a18 */ = 0.75,
_AL/* lvl6 */ = new T1(0,_AK/* Motion.Main.a18 */),
_AM/* lvl7 */ = new T2(0,_AL/* Motion.Main.lvl6 */,_AL/* Motion.Main.lvl6 */),
_AN/* a19 */ = 5,
_AO/* lvl8 */ = new T1(0,_AN/* Motion.Main.a19 */),
_AP/* $fAffineShape1 */ = function(_AQ/* stnh */, _AR/* stni */, _AS/* stnj */, _/* EXTERNAL */){
  var _AT/* stns */ = __app2/* EXTERNAL */(E(_xJ/* Core.Shape.Internal.$fAffineShape_f1 */), E(_AR/* stni */), E(_AS/* stnj */));
  return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_AU/* $w$caffine */ = function(_AV/* stnv */, _AW/* stnw */, _AX/* stnx */, _AY/* stny */, _AZ/* stnz */, _B0/* stnA */, _B1/* stnB */){
  var _B2/* stpl */ = function(_B3/* stoX */, _B4/* stoY */, _B5/* stoZ */, _/* EXTERNAL */){
    var _B6/* stpk */ = function(_B7/* stp1 */, _B8/* stp2 */, _B9/* stp3 */, _/* EXTERNAL */){
      var _Ba/* stpj */ = function(_Bb/* stp5 */, _Bc/* stp6 */, _Bd/* stp7 */, _/* EXTERNAL */){
        var _Be/* stpi */ = function(_Bf/* stp9 */, _Bg/* stpa */, _Bh/* stpb */, _/* EXTERNAL */){
          return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_AZ/* stnz */, function(_Bi/* stpd */, _Bj/* stpe */, _Bk/* stpf */, _/* EXTERNAL */){
            return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_B0/* stnA */, _AP/* Core.Shape.Internal.$fAffineShape1 */, _Bj/* stpe */, _Bk/* stpf */, _/* EXTERNAL */);});
          }, _Bg/* stpa */, _Bh/* stpb */, _/* EXTERNAL */);});
        };
        return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_AY/* stny */, _Be/* stpi */, _Bc/* stp6 */, _Bd/* stp7 */, _/* EXTERNAL */);});
      };
      return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_AX/* stnx */, _Ba/* stpj */, _B8/* stp2 */, _B9/* stp3 */, _/* EXTERNAL */);});
    };
    return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_AW/* stnw */, _B6/* stpk */, _B4/* stoY */, _B5/* stoZ */, _/* EXTERNAL */);});
  },
  _Bl/* stoW */ = function(_Bm/* stnC */, _/* EXTERNAL */){
    var _Bn/* stnE */ = E(_Bm/* stnC */),
    _Bo/* stnF */ = _Bn/* stnE */.a,
    _Bp/* stnG */ = _Bn/* stnE */.b,
    _Bq/* stoV */ = function(_Br/* stnH */, _/* EXTERNAL */){
      var _Bs/* stoU */ = function(_Bt/* stnJ */, _/* EXTERNAL */){
        var _Bu/* stoT */ = function(_Bv/* stnL */, _/* EXTERNAL */){
          var _Bw/* stoS */ = function(_Bx/* stnN */, _/* EXTERNAL */){
            var _By/* stoR */ = function(_Bz/* stnP */, _/* EXTERNAL */){
              var _BA/* stoQ */ = function(_BB/* stnR */){
                var _BC/* stnS */ = new T(function(){
                  return E(_Bt/* stnJ */)*E(_Bx/* stnN */)-E(_Br/* stnH */)*E(_Bz/* stnP */);
                });
                return new F(function(){return A1(_B1/* stnB */,new T2(0,new T(function(){
                  var _BD/* sto4 */ = E(_Bt/* stnJ */),
                  _BE/* stoa */ = E(_Bz/* stnP */);
                  return ( -(_BD/* sto4 */*E(_BB/* stnR */))+_BD/* sto4 */*E(_Bp/* stnG */)+_BE/* stoa */*E(_Bv/* stnL */)-_BE/* stoa */*E(_Bo/* stnF */))/E(_BC/* stnS */);
                }),new T(function(){
                  var _BF/* stos */ = E(_Br/* stnH */),
                  _BG/* stoy */ = E(_Bx/* stnN */);
                  return (_BF/* stos */*E(_BB/* stnR */)-_BF/* stos */*E(_Bp/* stnG */)-_BG/* stoy */*E(_Bv/* stnL */)+_BG/* stoy */*E(_Bo/* stnF */))/E(_BC/* stnS */);
                })));});
              };
              return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_B0/* stnA */, _BA/* stoQ */, _/* EXTERNAL */);});
            };
            return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_AZ/* stnz */, _By/* stoR */, _/* EXTERNAL */);});
          };
          return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_AY/* stny */, _Bw/* stoS */, _/* EXTERNAL */);});
        };
        return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_AX/* stnx */, _Bu/* stoT */, _/* EXTERNAL */);});
      };
      return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_AW/* stnw */, _Bs/* stoU */, _/* EXTERNAL */);});
    };
    return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_AV/* stnv */, _Bq/* stoV */, _/* EXTERNAL */);});
  };
  return new T3(0,_Bl/* stoW */,function(_le/* B3 */, _lf/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_AV/* stnv */, _B2/* stpl */, _le/* B3 */, _lf/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_BH/* $winsert */ = function(_BI/* s3sqy */, _BJ/* s3sqz */, _BK/* s3sqA */){
  var _BL/* s3sqB */ = E(_BJ/* s3sqz */),
  _BM/* s3sqC */ = E(_BK/* s3sqA */);
  switch(_BM/* s3sqC */._){
    case 0:
      var _BN/* s3sqD */ = _BM/* s3sqC */.a,
      _BO/* s3sqE */ = _BM/* s3sqC */.b,
      _BP/* s3sqF */ = _BM/* s3sqC */.c,
      _BQ/* s3sqG */ = _BM/* s3sqC */.d,
      _BR/* s3sqH */ = _BO/* s3sqE */>>>0;
      if(((_BI/* s3sqy */>>>0&((_BR/* s3sqH */-1>>>0^4294967295)>>>0^_BR/* s3sqH */)>>>0)>>>0&4294967295)==_BN/* s3sqD */){
        return ((_BI/* s3sqy */>>>0&_BR/* s3sqH */)>>>0==0) ? new T4(0,_BN/* s3sqD */,_BO/* s3sqE */,E(B(_BH/* Data.IntMap.Strict.$winsert */(_BI/* s3sqy */, _BL/* s3sqB */, _BP/* s3sqF */))),E(_BQ/* s3sqG */)) : new T4(0,_BN/* s3sqD */,_BO/* s3sqE */,E(_BP/* s3sqF */),E(B(_BH/* Data.IntMap.Strict.$winsert */(_BI/* s3sqy */, _BL/* s3sqB */, _BQ/* s3sqG */))));
      }else{
        var _BS/* s3sqU */ = (_BI/* s3sqy */>>>0^_BN/* s3sqD */>>>0)>>>0,
        _BT/* s3sqX */ = (_BS/* s3sqU */|_BS/* s3sqU */>>>1)>>>0,
        _BU/* s3sqZ */ = (_BT/* s3sqX */|_BT/* s3sqX */>>>2)>>>0,
        _BV/* s3sr1 */ = (_BU/* s3sqZ */|_BU/* s3sqZ */>>>4)>>>0,
        _BW/* s3sr3 */ = (_BV/* s3sr1 */|_BV/* s3sr1 */>>>8)>>>0,
        _BX/* s3sr5 */ = (_BW/* s3sr3 */|_BW/* s3sr3 */>>>16)>>>0,
        _BY/* s3sr7 */ = (_BX/* s3sr5 */^_BX/* s3sr5 */>>>1)>>>0&4294967295,
        _BZ/* s3sra */ = _BY/* s3sr7 */>>>0;
        return ((_BI/* s3sqy */>>>0&_BZ/* s3sra */)>>>0==0) ? new T4(0,(_BI/* s3sqy */>>>0&((_BZ/* s3sra */-1>>>0^4294967295)>>>0^_BZ/* s3sra */)>>>0)>>>0&4294967295,_BY/* s3sr7 */,E(new T2(1,_BI/* s3sqy */,_BL/* s3sqB */)),E(_BM/* s3sqC */)) : new T4(0,(_BI/* s3sqy */>>>0&((_BZ/* s3sra */-1>>>0^4294967295)>>>0^_BZ/* s3sra */)>>>0)>>>0&4294967295,_BY/* s3sr7 */,E(_BM/* s3sqC */),E(new T2(1,_BI/* s3sqy */,_BL/* s3sqB */)));
      }
      break;
    case 1:
      var _C0/* s3srr */ = _BM/* s3sqC */.a;
      if(_BI/* s3sqy */!=_C0/* s3srr */){
        var _C1/* s3srv */ = (_BI/* s3sqy */>>>0^_C0/* s3srr */>>>0)>>>0,
        _C2/* s3sry */ = (_C1/* s3srv */|_C1/* s3srv */>>>1)>>>0,
        _C3/* s3srA */ = (_C2/* s3sry */|_C2/* s3sry */>>>2)>>>0,
        _C4/* s3srC */ = (_C3/* s3srA */|_C3/* s3srA */>>>4)>>>0,
        _C5/* s3srE */ = (_C4/* s3srC */|_C4/* s3srC */>>>8)>>>0,
        _C6/* s3srG */ = (_C5/* s3srE */|_C5/* s3srE */>>>16)>>>0,
        _C7/* s3srI */ = (_C6/* s3srG */^_C6/* s3srG */>>>1)>>>0&4294967295,
        _C8/* s3srL */ = _C7/* s3srI */>>>0;
        return ((_BI/* s3sqy */>>>0&_C8/* s3srL */)>>>0==0) ? new T4(0,(_BI/* s3sqy */>>>0&((_C8/* s3srL */-1>>>0^4294967295)>>>0^_C8/* s3srL */)>>>0)>>>0&4294967295,_C7/* s3srI */,E(new T2(1,_BI/* s3sqy */,_BL/* s3sqB */)),E(_BM/* s3sqC */)) : new T4(0,(_BI/* s3sqy */>>>0&((_C8/* s3srL */-1>>>0^4294967295)>>>0^_C8/* s3srL */)>>>0)>>>0&4294967295,_C7/* s3srI */,E(_BM/* s3sqC */),E(new T2(1,_BI/* s3sqy */,_BL/* s3sqB */)));
      }else{
        return new T2(1,_BI/* s3sqy */,_BL/* s3sqB */);
      }
      break;
    default:
      return new T2(1,_BI/* s3sqy */,_BL/* s3sqB */);
  }
},
_C9/* Cancel */ = 6,
_Ca/* Drag */ = 4,
_Cb/* Enter */ = 0,
_Cc/* Move */ = 1,
_Cd/* Press */ = 3,
_Ce/* Release */ = 5,
_Cf/* lvl23 */ = function(_Cg/* sWfn */, _Ch/* sWfo */){
  return new F(function(){return A1(_Ch/* sWfo */,new T2(0,_7/* GHC.Tuple.() */,_Cg/* sWfn */));});
},
_Ci/* lvl24 */ = new T1(1,_6/* GHC.Types.[] */),
_Cj/* lvl */ = 0,
_Ck/* lvl25 */ = new T4(0,_Cj/* Core.View.lvl */,_Cj/* Core.View.lvl */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_Cl/* lvl26 */ = new T2(0,_Cj/* Core.View.lvl */,_Ck/* Core.View.lvl25 */),
_Cm/* lvl27 */ = new T2(0,_Cl/* Core.View.lvl26 */,_6/* GHC.Types.[] */),
_Cn/* lvl1 */ = 1,
_Co/* lvl28 */ = new T4(0,_Cn/* Core.View.lvl1 */,_Cn/* Core.View.lvl1 */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_Cp/* lvl29 */ = new T2(0,_Cn/* Core.View.lvl1 */,_Co/* Core.View.lvl28 */),
_Cq/* lvl30 */ = new T2(0,_Cp/* Core.View.lvl29 */,_6/* GHC.Types.[] */),
_Cr/* fork */ = function(_Cs/* srPv */){
  return E(E(_Cs/* srPv */).c);
},
_Ct/* lvl */ = new T1(1,_6/* GHC.Types.[] */),
_Cu/* spawn1 */ = function(_Cv/* sJti */){
  var _Cw/* sJtp */ = function(_/* EXTERNAL */){
    var _Cx/* sJtk */ = nMV/* EXTERNAL */(_Ct/* Haste.Concurrent.lvl */);
    return new T(function(){
      return B(A1(_Cv/* sJti */,_Cx/* sJtk */));
    });
  };
  return new T1(0,_Cw/* sJtp */);
},
_Cy/* spawn */ = function(_Cz/* sJtK */, _CA/* sJtL */){
  var _CB/* sJtM */ = new T(function(){
    return B(_Cr/* Haste.Concurrent.Monad.fork */(_Cz/* sJtK */));
  }),
  _CC/* sJtN */ = B(_9x/* Haste.Concurrent.Monad.$p1MonadConc */(_Cz/* sJtK */)),
  _CD/* sJtT */ = function(_CE/* sJtP */){
    var _CF/* sJtR */ = new T(function(){
      return B(A1(_CB/* sJtM */,new T(function(){
        return B(A1(_CA/* sJtL */,_CE/* sJtP */));
      })));
    });
    return new F(function(){return A3(_9z/* GHC.Base.>> */,_CC/* sJtN */, _CF/* sJtR */, new T(function(){
      return B(A2(_6T/* GHC.Base.return */,_CC/* sJtN */, _CE/* sJtP */));
    }));});
  };
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_CC/* sJtN */, new T(function(){
    return B(A2(_2V/* Haste.Concurrent.Monad.liftConc */,_Cz/* sJtK */, _Cu/* Haste.Concurrent.spawn1 */));
  }), _CD/* sJtT */);});
},
_CG/* makeView */ = function(_CH/* sWfq */, _CI/* sWfr */, _CJ/* sWfs */, _CK/* sWft */){
  var _CL/* sWfu */ = new T(function(){
    return B(A1(_CH/* sWfq */,_yW/* Core.View.Leave */));
  }),
  _CM/* sWfv */ = new T(function(){
    return B(A1(_CH/* sWfq */,_Cb/* Core.View.Enter */));
  }),
  _CN/* sWfw */ = new T(function(){
    return B(A1(_CH/* sWfq */,_Ca/* Core.View.Drag */));
  }),
  _CO/* sWfx */ = new T(function(){
    return B(_Cy/* Haste.Concurrent.spawn */(_8l/* Core.World.Internal.$fMonadConcWorld */, _CK/* sWft */));
  }),
  _CP/* sWfy */ = new T(function(){
    return B(A1(_CH/* sWfq */,_C9/* Core.View.Cancel */));
  }),
  _CQ/* sWfz */ = new T(function(){
    return B(A1(_CH/* sWfq */,_Ce/* Core.View.Release */));
  }),
  _CR/* sWfA */ = new T(function(){
    return B(A1(_CH/* sWfq */,_Cd/* Core.View.Press */));
  }),
  _CS/* sWfB */ = new T(function(){
    return B(A1(_CH/* sWfq */,_Cc/* Core.View.Move */));
  }),
  _CT/* sWkQ */ = function(_CU/* sWfC */){
    var _CV/* sWfD */ = new T(function(){
      return B(A1(_CO/* sWfx */,_CU/* sWfC */));
    }),
    _CW/* sWkP */ = function(_CX/* sWfE */){
      var _CY/* sWkO */ = function(_CZ/* sWfF */){
        var _D0/* sWfG */ = E(_CZ/* sWfF */),
        _D1/* sWfH */ = _D0/* sWfG */.a,
        _D2/* sWfI */ = _D0/* sWfG */.b,
        _D3/* sWfJ */ = new T(function(){
          var _D4/* sWfK */ = E(_CL/* sWfu */);
          if(!_D4/* sWfK */._){
            return E(_Cf/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _D1/* sWfH */, _D4/* sWfK */.a));
          }
        }),
        _D5/* sWfM */ = new T(function(){
          var _D6/* sWfN */ = E(_CM/* sWfv */);
          if(!_D6/* sWfN */._){
            return E(_Cf/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _D1/* sWfH */, _D6/* sWfN */.a));
          }
        }),
        _D7/* sWfP */ = new T(function(){
          var _D8/* sWfQ */ = E(_CN/* sWfw */);
          if(!_D8/* sWfQ */._){
            return E(_Cf/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _D1/* sWfH */, _D8/* sWfQ */.a));
          }
        }),
        _D9/* sWfS */ = new T(function(){
          var _Da/* sWfT */ = E(_CP/* sWfy */);
          if(!_Da/* sWfT */._){
            return E(_Cf/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _D1/* sWfH */, _Da/* sWfT */.a));
          }
        }),
        _Db/* sWfV */ = new T(function(){
          var _Dc/* sWfW */ = E(_CQ/* sWfz */);
          if(!_Dc/* sWfW */._){
            return E(_Cf/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _D1/* sWfH */, _Dc/* sWfW */.a));
          }
        }),
        _Dd/* sWfY */ = new T(function(){
          var _De/* sWfZ */ = E(_CR/* sWfA */);
          if(!_De/* sWfZ */._){
            return E(_Cf/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _D1/* sWfH */, _De/* sWfZ */.a));
          }
        }),
        _Df/* sWg1 */ = new T(function(){
          var _Dg/* sWg2 */ = E(_CS/* sWfB */);
          if(!_Dg/* sWg2 */._){
            return E(_Cf/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _D1/* sWfH */, _Dg/* sWg2 */.a));
          }
        }),
        _Dh/* sWkN */ = function(_/* EXTERNAL */){
          var _Di/* sWg5 */ = nMV/* EXTERNAL */(_Cq/* Core.View.lvl30 */),
          _Dj/* sWg7 */ = _Di/* sWg5 */,
          _Dk/* sWkL */ = function(_/* EXTERNAL */){
            var _Dl/* sWga */ = nMV/* EXTERNAL */(_Cm/* Core.View.lvl27 */),
            _Dm/* sWgc */ = _Dl/* sWga */,
            _Dn/* sWkJ */ = function(_/* EXTERNAL */){
              var _Do/* sWgf */ = nMV/* EXTERNAL */(_Cm/* Core.View.lvl27 */),
              _Dp/* sWgh */ = _Do/* sWgf */,
              _Dq/* sWkH */ = function(_/* EXTERNAL */){
                var _Dr/* sWgk */ = nMV/* EXTERNAL */(_Cm/* Core.View.lvl27 */),
                _Ds/* sWgm */ = _Dr/* sWgk */,
                _Dt/* sWkF */ = function(_/* EXTERNAL */){
                  var _Du/* sWgp */ = nMV/* EXTERNAL */(_Cq/* Core.View.lvl30 */),
                  _Dv/* sWgr */ = _Du/* sWgp */,
                  _Dw/* sWkD */ = function(_/* EXTERNAL */){
                    var _Dx/* sWgu */ = nMV/* EXTERNAL */(_Cm/* Core.View.lvl27 */),
                    _Dy/* sWgw */ = _Dx/* sWgu */,
                    _Dz/* sWgy */ = new T(function(){
                      var _DA/* sWhl */ = function(_DB/* sWgz */, _DC/* sWgA */, _DD/* sWgB */, _DE/* sWgC */, _DF/* sWgD */, _DG/* sWgE */){
                        var _DH/* sWgF */ = new T(function(){
                          return B(_jD/* Core.Ease.$wforceTo */(_Dj/* sWg7 */, _DB/* sWgz */));
                        }),
                        _DI/* sWgG */ = new T(function(){
                          return B(_jD/* Core.Ease.$wforceTo */(_Dm/* sWgc */, _DC/* sWgA */));
                        }),
                        _DJ/* sWgH */ = new T(function(){
                          return B(_jD/* Core.Ease.$wforceTo */(_Dp/* sWgh */, _DD/* sWgB */));
                        }),
                        _DK/* sWgI */ = new T(function(){
                          return B(_jD/* Core.Ease.$wforceTo */(_Ds/* sWgm */, _DE/* sWgC */));
                        }),
                        _DL/* sWgJ */ = new T(function(){
                          return B(_jD/* Core.Ease.$wforceTo */(_Dv/* sWgr */, _DF/* sWgD */));
                        }),
                        _DM/* sWgK */ = new T(function(){
                          return B(_jD/* Core.Ease.$wforceTo */(_Dy/* sWgw */, _DG/* sWgE */));
                        }),
                        _DN/* sWhk */ = function(_DO/* sWgL */){
                          var _DP/* sWgM */ = new T(function(){
                            return B(A1(_DH/* sWgF */,_DO/* sWgL */));
                          }),
                          _DQ/* sWhj */ = function(_DR/* sWgN */){
                            var _DS/* sWgO */ = function(_DT/* sWgP */){
                              return new F(function(){return A1(_DR/* sWgN */,new T2(0,_7/* GHC.Tuple.() */,E(_DT/* sWgP */).b));});
                            },
                            _DU/* sWgU */ = function(_DV/* sWgV */){
                              return new F(function(){return A2(_DM/* sWgK */,E(_DV/* sWgV */).b, _DS/* sWgO */);});
                            },
                            _DW/* sWgZ */ = function(_DX/* sWh0 */){
                              return new F(function(){return A2(_DL/* sWgJ */,E(_DX/* sWh0 */).b, _DU/* sWgU */);});
                            },
                            _DY/* sWh4 */ = function(_DZ/* sWh5 */){
                              return new F(function(){return A2(_DK/* sWgI */,E(_DZ/* sWh5 */).b, _DW/* sWgZ */);});
                            },
                            _E0/* sWh9 */ = function(_E1/* sWha */){
                              return new F(function(){return A2(_DJ/* sWgH */,E(_E1/* sWha */).b, _DY/* sWh4 */);});
                            };
                            return new F(function(){return A1(_DP/* sWgM */,function(_E2/* sWhe */){
                              return new F(function(){return A2(_DI/* sWgG */,E(_E2/* sWhe */).b, _E0/* sWh9 */);});
                            });});
                          };
                          return E(_DQ/* sWhj */);
                        };
                        return E(_DN/* sWhk */);
                      };
                      return B(_rn/* Control.Monad.Skeleton.bone */(new T2(2,_DA/* sWhl */,_7/* GHC.Tuple.() */)));
                    }),
                    _E3/* sWhn */ = new T(function(){
                      var _E4/* sWho */ = E(_CJ/* sWfs */);
                      return new T2(0,E(_E4/* sWho */.a),E(new T2(2,_E4/* sWho */.b,new T1(1,function(_E5/* sWhr */){
                        return E(_Dz/* sWgy */);
                      }))));
                    }),
                    _E6/* sWhv */ = new T(function(){
                      var _E7/* sWhM */ = B(_AU/* Core.Shape.Internal.$w$caffine */(new T2(2,new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_Dj/* sWg7 */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_Dm/* sWgc */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_Dp/* sWgh */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_Ds/* sWgm */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_Dv/* sWgr */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_Dy/* sWgw */),_2E/* GHC.Base.id */), E(_CI/* sWfr */).a));
                      return new T3(0,_E7/* sWhM */.a,_E7/* sWhM */.b,_E7/* sWhM */.c);
                    }),
                    _E8/* sWkB */ = function(_/* EXTERNAL */){
                      var _E9/* sWhR */ = nMV/* EXTERNAL */(_Ci/* Core.View.lvl24 */),
                      _Ea/* sWhT */ = _E9/* sWhR */,
                      _Eb/* sWkx */ = new T(function(){
                        var _Ec/* sWiH */ = function(_Ed/* sWjf */){
                          return new F(function(){return _Ee/* sWiG */(E(_Ed/* sWjf */).b);});
                        },
                        _Ef/* sWiJ */ = function(_Eg/* sWjn */){
                          var _Eh/* sWjo */ = new T(function(){
                            return B(A2(_Df/* sWg1 */,_Eg/* sWjn */, _Ei/* sWiI */));
                          }),
                          _Ej/* sWjp */ = new T(function(){
                            return B(A2(_D3/* sWfJ */,_Eg/* sWjn */, _Ec/* sWiH */));
                          }),
                          _Ek/* sWjq */ = new T(function(){
                            return B(A2(_Dd/* sWfY */,_Eg/* sWjn */, _El/* sWiF */));
                          }),
                          _Em/* sWjr */ = new T(function(){
                            return B(_Ef/* sWiJ */(_Eg/* sWjn */));
                          }),
                          _En/* sWjI */ = function(_Eo/* sWjs */){
                            var _Ep/* sWjt */ = E(_Eo/* sWjs */);
                            if(!_Ep/* sWjt */._){
                              return (!E(_Ep/* sWjt */.a)) ? E(_Em/* sWjr */) : E(_Ek/* sWjq */);
                            }else{
                              var _Eq/* sWjH */ = function(_/* EXTERNAL */){
                                var _Er/* sWjC */ = B(A2(E(_E6/* sWhv */).a,_Ep/* sWjt */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_Er/* sWjC */)){
                                    return E(_Ej/* sWjp */);
                                  }else{
                                    return E(_Eh/* sWjo */);
                                  }
                                });
                              };
                              return new T1(0,_Eq/* sWjH */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ea/* sWhT */, _En/* sWjI */)));
                        },
                        _Ei/* sWiI */ = function(_Es/* sWjj */){
                          return new F(function(){return _Ef/* sWiJ */(E(_Es/* sWjj */).b);});
                        },
                        _Ee/* sWiG */ = function(_Et/* sWiU */){
                          var _Eu/* sWiV */ = new T(function(){
                            return B(_Ee/* sWiG */(_Et/* sWiU */));
                          }),
                          _Ev/* sWiW */ = new T(function(){
                            return B(A2(_D5/* sWfM */,_Et/* sWiU */, _Ei/* sWiI */));
                          }),
                          _Ew/* sWjc */ = function(_Ex/* sWiX */){
                            var _Ey/* sWiY */ = E(_Ex/* sWiX */);
                            if(!_Ey/* sWiY */._){
                              return E(_Eu/* sWiV */);
                            }else{
                              var _Ez/* sWjb */ = function(_/* EXTERNAL */){
                                var _EA/* sWj6 */ = B(A2(E(_E6/* sWhv */).a,_Ey/* sWiY */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_EA/* sWj6 */)){
                                    return E(_Eu/* sWiV */);
                                  }else{
                                    return E(_Ev/* sWiW */);
                                  }
                                });
                              };
                              return new T1(0,_Ez/* sWjb */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ea/* sWhT */, _Ew/* sWjc */)));
                        },
                        _EB/* sWiK */ = function(_EC/* sWjL */){
                          var _ED/* sWjM */ = new T(function(){
                            return B(A2(_D7/* sWfP */,_EC/* sWjL */, _El/* sWiF */));
                          }),
                          _EE/* sWjN */ = new T(function(){
                            return B(A2(_D3/* sWfJ */,_EC/* sWjL */, _EF/* sWiE */));
                          }),
                          _EG/* sWjO */ = new T(function(){
                            return B(_EB/* sWiK */(_EC/* sWjL */));
                          }),
                          _EH/* sWjP */ = new T(function(){
                            return B(A2(_Db/* sWfV */,_EC/* sWjL */, _Ei/* sWiI */));
                          }),
                          _EI/* sWk6 */ = function(_EJ/* sWjQ */){
                            var _EK/* sWjR */ = E(_EJ/* sWjQ */);
                            if(!_EK/* sWjR */._){
                              return (!E(_EK/* sWjR */.a)) ? E(_EH/* sWjP */) : E(_EG/* sWjO */);
                            }else{
                              var _EL/* sWk5 */ = function(_/* EXTERNAL */){
                                var _EM/* sWk0 */ = B(A2(E(_E6/* sWhv */).a,_EK/* sWjR */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_EM/* sWk0 */)){
                                    return E(_EE/* sWjN */);
                                  }else{
                                    return E(_ED/* sWjM */);
                                  }
                                });
                              };
                              return new T1(0,_EL/* sWk5 */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ea/* sWhT */, _EI/* sWk6 */)));
                        },
                        _El/* sWiF */ = function(_EN/* sWiQ */){
                          return new F(function(){return _EB/* sWiK */(E(_EN/* sWiQ */).b);});
                        },
                        _EO/* sWiL */ = function(_EP/* sWk9 */){
                          var _EQ/* sWka */ = new T(function(){
                            return B(A2(_D5/* sWfM */,_EP/* sWk9 */, _El/* sWiF */));
                          }),
                          _ER/* sWkb */ = new T(function(){
                            return B(A2(_D7/* sWfP */,_EP/* sWk9 */, _EF/* sWiE */));
                          }),
                          _ES/* sWkc */ = new T(function(){
                            return B(_EO/* sWiL */(_EP/* sWk9 */));
                          }),
                          _ET/* sWkd */ = new T(function(){
                            return B(A2(_D9/* sWfS */,_EP/* sWk9 */, _Ec/* sWiH */));
                          }),
                          _EU/* sWku */ = function(_EV/* sWke */){
                            var _EW/* sWkf */ = E(_EV/* sWke */);
                            if(!_EW/* sWkf */._){
                              return (!E(_EW/* sWkf */.a)) ? E(_ET/* sWkd */) : E(_ES/* sWkc */);
                            }else{
                              var _EX/* sWkt */ = function(_/* EXTERNAL */){
                                var _EY/* sWko */ = B(A2(E(_E6/* sWhv */).a,_EW/* sWkf */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_EY/* sWko */)){
                                    return E(_ER/* sWkb */);
                                  }else{
                                    return E(_EQ/* sWka */);
                                  }
                                });
                              };
                              return new T1(0,_EX/* sWkt */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ea/* sWhT */, _EU/* sWku */)));
                        },
                        _EF/* sWiE */ = function(_EZ/* sWiM */){
                          return new F(function(){return _EO/* sWiL */(E(_EZ/* sWiM */).b);});
                        };
                        return B(_Ee/* sWiG */(_D2/* sWfI */));
                      }),
                      _F0/* sWiD */ = new T(function(){
                        var _F1/* sWiC */ = function(_F2/* sWis */){
                          var _F3/* sWit */ = E(_F2/* sWis */);
                          return new F(function(){return A1(_CX/* sWfE */,new T2(0,new T(function(){
                            return new T3(0,E(_F3/* sWit */.a),_E3/* sWhn */,E(_D1/* sWfH */));
                          }),_F3/* sWit */.b));});
                        },
                        _F4/* sWir */ = function(_F5/* sWhV */, _F6/* sWhW */, _F7/* sWhX */){
                          var _F8/* sWhY */ = new T(function(){
                            return E(E(_F5/* sWhV */).d);
                          }),
                          _F9/* sWi4 */ = new T(function(){
                            return E(E(_F8/* sWhY */).a);
                          }),
                          _Fa/* sWio */ = new T(function(){
                            var _Fb/* sWi8 */ = E(_F5/* sWhV */);
                            return new T4(0,E(_Fb/* sWi8 */.a),_Fb/* sWi8 */.b,E(_Fb/* sWi8 */.c),E(new T2(0,new T(function(){
                              return E(_F9/* sWi4 */)+1|0;
                            }),new T(function(){
                              return B(_BH/* Data.IntMap.Strict.$winsert */(E(_F9/* sWi4 */), _Ea/* sWhT */, E(_F8/* sWhY */).b));
                            }))));
                          });
                          return new F(function(){return A1(_F7/* sWhX */,new T2(0,new T2(0,_F9/* sWi4 */,_Fa/* sWio */),_F6/* sWhW */));});
                        };
                        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _D2/* sWfI */, _F4/* sWir */, _D2/* sWfI */, _F1/* sWiC */]));
                      });
                      return new T1(1,new T2(1,_F0/* sWiD */,new T2(1,_Eb/* sWkx */,_6/* GHC.Types.[] */)));
                    };
                    return new T1(0,_E8/* sWkB */);
                  };
                  return new T1(0,_Dw/* sWkD */);
                };
                return new T1(0,_Dt/* sWkF */);
              };
              return new T1(0,_Dq/* sWkH */);
            };
            return new T1(0,_Dn/* sWkJ */);
          };
          return new T1(0,_Dk/* sWkL */);
        };
        return new T1(0,_Dh/* sWkN */);
      };
      return new F(function(){return A1(_CV/* sWfD */,_CY/* sWkO */);});
    };
    return E(_CW/* sWkP */);
  };
  return E(_CT/* sWkQ */);
},
_Fc/* consView */ = function(_Fd/* s7Dm */, _Fe/* s7Dn */, _Ff/* s7Do */, _Fg/* s7Dp */){
  var _Fh/* s7Dq */ = new T(function(){
    var _Fi/* s7DL */ = new T(function(){
      var _Fj/* s7Dx */ = B(_rr/* Core.Render.Internal.fill1 */(_Ac/* Motion.Main.lvl12 */, new T(function(){
        var _Fk/* s7Ds */ = B(_xZ/* Core.Shape.Internal.$wtext */(_Ad/* Motion.Main.lvl13 */, new T1(0,_Ff/* s7Do */), _yG/* Core.Shape.Internal.LeftAlign */, _yD/* Core.Shape.Internal.BottomBase */, _Aj/* Motion.Main.lvl16 */, _Am/* Motion.Main.lvl19 */, _Aq/* Motion.Main.lvl22 */));
        return new T3(0,_Fk/* s7Ds */.a,_Fk/* s7Ds */.b,_Fk/* s7Ds */.c);
      }))),
      _Fl/* s7DA */ = new T(function(){
        return B(_rr/* Core.Render.Internal.fill1 */(_At/* Motion.Main.lvl24 */, new T(function(){
          var _Fm/* s7DC */ = B(_xZ/* Core.Shape.Internal.$wtext */(_Ad/* Motion.Main.lvl13 */, new T1(0,_Fg/* s7Dp */), _yG/* Core.Shape.Internal.LeftAlign */, _yH/* Core.Shape.Internal.TopBase */, _Aj/* Motion.Main.lvl16 */, _Aw/* Motion.Main.lvl27 */, _AA/* Motion.Main.lvl30 */));
          return new T3(0,_Fm/* s7DC */.a,_Fm/* s7DC */.b,_Fm/* s7DC */.c);
        })));
      });
      return new T2(0,E(_Fj/* s7Dx */.a),E(new T2(2,_Fj/* s7Dx */.b,new T1(1,function(_Fn/* s7DH */){
        return E(_Fl/* s7DA */);
      }))));
    });
    return B(_xh/* Core.Render.Internal.$wshadowed */(_yJ/* Motion.Main.lvl4 */, _AJ/* Motion.Main.lvl5 */, _AO/* Motion.Main.lvl8 */, _A9/* Motion.Main.lvl10 */, _Fi/* s7DL */));
  }),
  _Fo/* s7DM */ = function(_Fp/* s7DN */){
    return E(_Fh/* s7Dq */);
  },
  _Fq/* s7DP */ = new T(function(){
    return B(A1(_Fe/* s7Dn */,_Fd/* s7Dm */));
  }),
  _Fr/* s7EC */ = function(_Fs/* s7DQ */){
    var _Ft/* s7DR */ = new T(function(){
      return B(A1(_Fq/* s7DP */,_Fs/* s7DQ */));
    }),
    _Fu/* s7EB */ = function(_Fv/* s7DS */){
      var _Fw/* s7EA */ = function(_Fx/* s7DT */){
        var _Fy/* s7DU */ = E(_Fx/* s7DT */),
        _Fz/* s7DX */ = E(_Fy/* s7DU */.a),
        _FA/* s7E0 */ = new T(function(){
          var _FB/* s7E3 */ = B(_zO/* Core.Render.Internal.clip */(_yM/* Motion.Main.shape */, new T(function(){
            return B(_rn/* Control.Monad.Skeleton.bone */(new T3(7,_AM/* Motion.Main.lvl7 */,_Fz/* s7DX */.a,_7/* GHC.Tuple.() */)));
          })));
          return new T2(0,E(_FB/* s7E3 */.a),E(new T2(2,_FB/* s7E3 */.b,new T1(1,_Fo/* s7DM */))));
        }),
        _FC/* s7Ez */ = function(_/* EXTERNAL */){
          var _FD/* s7E8 */ = nMV/* EXTERNAL */(_AH/* Motion.Main.lvl35 */);
          return new T(function(){
            var _FE/* s7Ec */ = new T(function(){
              return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Ax/* Motion.Main.lvl3 */, _A6/* Core.Ease.linear */, _FD/* s7E8 */, _An/* Motion.Main.lvl2 */, _A2/* Core.Ease.easeTo1 */));
            }),
            _FF/* s7Ed */ = new T(function(){
              return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Ax/* Motion.Main.lvl3 */, _A6/* Core.Ease.linear */, _FD/* s7E8 */, _AB/* Motion.Main.lvl31 */, _A2/* Core.Ease.easeTo1 */));
            }),
            _FG/* s7Ex */ = function(_FH/* s7Eo */){
              var _FI/* s7Ep */ = new T(function(){
                return B(_z9/* Core.UI.button */(_FE/* s7Ec */, _FF/* s7Ed */, _yR/* Motion.Main.a23 */, _FH/* s7Eo */));
              }),
              _FJ/* s7Ew */ = function(_FK/* s7Eq */, _FL/* s7Er */){
                return new T1(1,new T2(1,new T(function(){
                  return B(A2(_FI/* s7Ep */,_FK/* s7Eq */, _FL/* s7Er */));
                }),new T2(1,new T(function(){
                  return B(A2(_Fz/* s7DX */.b,_FK/* s7Eq */, _AC/* Motion.Main.lvl32 */));
                }),_6/* GHC.Types.[] */)));
              };
              return E(_FJ/* s7Ew */);
            },
            _FM/* s7En */ = new T(function(){
              var _FN/* s7Eg */ = B(_xh/* Core.Render.Internal.$wshadowed */(_yJ/* Motion.Main.lvl4 */, _AJ/* Motion.Main.lvl5 */, new T2(2,new T3(0,_Ax/* Motion.Main.lvl3 */,_A6/* Core.Ease.linear */,_FD/* s7E8 */),_2E/* GHC.Base.id */), _yV/* Core.Render.Internal.black */, _yQ/* Motion.Main.a17 */));
              return new T2(0,E(_FN/* s7Eg */.a),E(new T2(2,_FN/* s7Eg */.b,new T1(1,function(_FO/* s7Ej */){
                return E(_FA/* s7E0 */);
              }))));
            });
            return B(A(_CG/* Core.View.makeView */,[_yE/* GHC.Base.Just */, _yM/* Motion.Main.shape */, _FM/* s7En */, _FG/* s7Ex */, _Fy/* s7DU */.b, _Fv/* s7DS */]));
          });
        };
        return new T1(0,_FC/* s7Ez */);
      };
      return new F(function(){return A1(_Ft/* s7DR */,_Fw/* s7EA */);});
    };
    return E(_Fu/* s7EB */);
  };
  return E(_Fr/* s7EC */);
},
_FP/* lvl36 */ = new T4(0,_yJ/* Motion.Main.lvl4 */,_Ap/* Motion.Main.lvl21 */,_Ab/* Motion.Main.lvl11 */,_Ab/* Motion.Main.lvl11 */),
_FQ/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bounce"));
}),
_FR/* lvl38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Velocity & Acceleration"));
}),
_FS/* lvl39 */ = new T(function(){
  return B(_Fc/* Motion.Main.consView */(_FP/* Motion.Main.lvl36 */, _wO/* Motion.Bounce.bounceMot1 */, _FQ/* Motion.Main.lvl37 */, _FR/* Motion.Main.lvl38 */));
}),
_FT/* negateDouble */ = function(_FU/* s18yz */){
  return  -E(_FU/* s18yz */);
},
_FV/* $fAffineRender1 */ = function(_FW/* sFdS */, _FX/* sFdT */, _FY/* sFdU */, _FZ/* sFdV */){
  var _G0/* sFeZ */ = new T(function(){
    var _G1/* sFeX */ = new T(function(){
      var _G2/* sFeU */ = new T(function(){
        var _G3/* sFer */ = E(_FY/* sFdU */);
        switch(_G3/* sFer */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_G3/* sFer */.a);
            }));
            break;
          case 1:
            var _G4/* sFeD */ = function(_/* EXTERNAL */){
              var _G5/* sFez */ = B(A1(_G3/* sFer */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_FT/* GHC.Float.negateDouble */(_G5/* sFez */));
              });
            };
            return new T1(1,_G4/* sFeD */);
            break;
          case 2:
            return new T2(2,_G3/* sFer */.a,function(_G6/* sFeG */){
              return  -B(A1(_G3/* sFer */.b,_G6/* sFeG */));
            });
            break;
          default:
            var _G7/* sFeT */ = function(_G8/* sFeN */, _/* EXTERNAL */){
              var _G9/* sFeP */ = B(A2(_G3/* sFer */.b,_G8/* sFeN */, _/* EXTERNAL */));
              return new T(function(){
                return B(_FT/* GHC.Float.negateDouble */(_G9/* sFeP */));
              });
            };
            return new T2(3,_G3/* sFer */.a,_G7/* sFeT */);
        }
      }),
      _Ga/* sFeq */ = new T(function(){
        var _Gb/* sFdX */ = E(_FX/* sFdT */);
        switch(_Gb/* sFdX */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_Gb/* sFdX */.a);
            }));
            break;
          case 1:
            var _Gc/* sFe9 */ = function(_/* EXTERNAL */){
              var _Gd/* sFe5 */ = B(A1(_Gb/* sFdX */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_FT/* GHC.Float.negateDouble */(_Gd/* sFe5 */));
              });
            };
            return new T1(1,_Gc/* sFe9 */);
            break;
          case 2:
            return new T2(2,_Gb/* sFdX */.a,function(_Ge/* sFec */){
              return  -B(A1(_Gb/* sFdX */.b,_Ge/* sFec */));
            });
            break;
          default:
            var _Gf/* sFep */ = function(_Gg/* sFej */, _/* EXTERNAL */){
              var _Gh/* sFel */ = B(A2(_Gb/* sFdX */.b,_Gg/* sFej */, _/* EXTERNAL */));
              return new T(function(){
                return B(_FT/* GHC.Float.negateDouble */(_Gh/* sFel */));
              });
            };
            return new T2(3,_Gb/* sFdX */.a,_Gf/* sFep */);
        }
      });
      return B(_rn/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_Ga/* sFeq */,_G2/* sFeU */),_FZ/* sFdV */,_7/* GHC.Tuple.() */)));
    });
    return B(_rn/* Control.Monad.Skeleton.bone */(new T3(7,_FW/* sFdS */,_G1/* sFeX */,_7/* GHC.Tuple.() */)));
  });
  return new F(function(){return _rn/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_FX/* sFdT */,_FY/* sFdU */),_G0/* sFeZ */,_7/* GHC.Tuple.() */));});
},
_Gi/* lvl */ = 0,
_Gj/* lvl1 */ = 40,
_Gk/* lvl2 */ = 0.9999999999999998,
_Gl/* lvl3 */ = new T4(0,_Gi/* Motion.Grow.lvl */,_Gi/* Motion.Grow.lvl */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_Gm/* lvl4 */ = new T2(0,_Gi/* Motion.Grow.lvl */,_Gl/* Motion.Grow.lvl3 */),
_Gn/* lvl5 */ = new T2(0,_Gm/* Motion.Grow.lvl4 */,_6/* GHC.Types.[] */),
_Go/* $wa1 */ = function(_Gp/* s64X */, _Gq/* s64Y */, _Gr/* s64Z */){
  return function(_/* EXTERNAL */){
    var _Gs/* s651 */ = nMV/* EXTERNAL */(_Gn/* Motion.Grow.lvl5 */);
    return new T(function(){
      var _Gt/* s654 */ = function(_Gu/* s655 */, _Gv/* s656 */){
        return 1-B(A1(_Gu/* s655 */,new T(function(){
          var _Gw/* s659 */ = E(_Gv/* s656 */)/0.3-_Gp/* s64X *//7*2.3333333333333335;
          if(1>_Gw/* s659 */){
            if(0>_Gw/* s659 */){
              return E(_Gk/* Motion.Grow.lvl2 */);
            }else{
              var _Gx/* s65i */ = 1-_Gw/* s659 */;
              return _Gx/* s65i */*_Gx/* s65i */*(2.70158*_Gx/* s65i */-1.70158);
            }
          }else{
            return E(_Gi/* Motion.Grow.lvl */);
          }
        })));
      },
      _Gy/* s65v */ = new T3(0,_Gj/* Motion.Grow.lvl1 */,function(_Gz/* s65r */, _GA/* s65s */){
        return new F(function(){return _Gt/* s654 */(_Gz/* s65r */, _GA/* s65s */);});
      },_Gs/* s651 */),
      _GB/* s65w */ = E(_Gp/* s64X */);
      if(_GB/* s65w */==7){
        return B(A1(_Gr/* s64Z */,new T2(0,new T2(1,_Gy/* s65v */,_6/* GHC.Types.[] */),_Gq/* s64Y */)));
      }else{
        return new T1(0,B(_Go/* Motion.Grow.$wa1 */(_GB/* s65w */+1|0, _Gq/* s64Y */, function(_GC/* s65y */){
          var _GD/* s65z */ = E(_GC/* s65y */);
          return new F(function(){return A1(_Gr/* s64Z */,new T2(0,new T2(1,_Gy/* s65v */,_GD/* s65z */.a),_GD/* s65z */.b));});
        })));
      }
    });
  };
},
_GE/* $wcenterRect */ = function(_GF/* stCR */, _GG/* stCS */, _GH/* stCT */, _GI/* stCU */){
  var _GJ/* stF0 */ = function(_GK/* stDN */, _GL/* stDO */, _GM/* stDP */, _/* EXTERNAL */){
    var _GN/* stEZ */ = function(_GO/* stDR */, _GP/* stDS */, _GQ/* stDT */, _/* EXTERNAL */){
      var _GR/* stEY */ = function(_GS/* stDV */){
        var _GT/* stDW */ = new T(function(){
          return E(_GS/* stDV */)/2;
        }),
        _GU/* stEX */ = function(_GV/* stE0 */, _GW/* stE1 */, _GX/* stE2 */, _/* EXTERNAL */){
          var _GY/* stE4 */ = E(_GK/* stDN */),
          _GZ/* stE6 */ = E(_GT/* stDW */),
          _H0/* stE8 */ = _GY/* stE4 */+_GZ/* stE6 */,
          _H1/* stEe */ = _GY/* stE4 */-_GZ/* stE6 */,
          _H2/* stEh */ = E(_GO/* stDR */),
          _H3/* stEl */ = E(_GV/* stE0 */)/2,
          _H4/* stEp */ = _H2/* stEh */+_H3/* stEl */,
          _H5/* stEs */ = _H2/* stEh */-_H3/* stEl */,
          _H6/* stEv */ = E(_GW/* stE1 */),
          _H7/* stEz */ = E(_GX/* stE2 */),
          _H8/* stEC */ = __app4/* EXTERNAL */(E(_kp/* Core.Shape.Internal.bezier_f2 */), _H1/* stEe */, _H5/* stEs */, _H6/* stEv */, _H7/* stEz */),
          _H9/* stEF */ = E(_kq/* Core.Shape.Internal.line_f1 */),
          _Ha/* stEI */ = __app4/* EXTERNAL */(_H9/* stEF */, _H0/* stE8 */, _H2/* stEh */-_H3/* stEl */, _H6/* stEv */, _H7/* stEz */),
          _Hb/* stEM */ = __app4/* EXTERNAL */(_H9/* stEF */, _H0/* stE8 */, _H4/* stEp */, _H6/* stEv */, _H7/* stEz */),
          _Hc/* stEQ */ = __app4/* EXTERNAL */(_H9/* stEF */, _GY/* stE4 */-_GZ/* stE6 */, _H4/* stEp */, _H6/* stEv */, _H7/* stEz */),
          _Hd/* stEU */ = __app4/* EXTERNAL */(_H9/* stEF */, _H1/* stEe */, _H5/* stEs */, _H6/* stEv */, _H7/* stEz */);
          return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        };
        return function(_gd/* _fa_1 */, _ge/* _fa_2 */, _He/* _fa_3 */){
          return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_GI/* stCU */, _GU/* stEX */, _gd/* _fa_1 */, _ge/* _fa_2 */, _He/* _fa_3 */);});
        };
      };
      return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_GH/* stCT */, _GR/* stEY */, _GP/* stDS */, _GQ/* stDT */, _/* EXTERNAL */);});
    };
    return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_GG/* stCS */, _GN/* stEZ */, _GL/* stDO */, _GM/* stDP */, _/* EXTERNAL */);});
  },
  _Hf/* stDM */ = function(_Hg/* stCV */, _/* EXTERNAL */){
    var _Hh/* stCX */ = E(_Hg/* stCV */),
    _Hi/* stDL */ = function(_Hj/* stD0 */, _/* EXTERNAL */){
      var _Hk/* stDK */ = function(_Hl/* stD2 */, _/* EXTERNAL */){
        var _Hm/* stDJ */ = function(_Hn/* stD4 */, _/* EXTERNAL */){
          var _Ho/* stDI */ = function(_Hp/* stD6 */, _/* EXTERNAL */){
            return new T(function(){
              var _Hq/* stDc */ = function(_Hr/* stDd */){
                if(_Hr/* stDd */>=E(_Hn/* stD4 */)/2){
                  return false;
                }else{
                  var _Hs/* stDn */ = E(_Hh/* stCX */.b)-E(_Hl/* stD2 */);
                  return (_Hs/* stDn */==0) ? 0<E(_Hp/* stD6 */)/2 : (_Hs/* stDn */<=0) ?  -_Hs/* stDn */<E(_Hp/* stD6 */)/2 : _Hs/* stDn */<E(_Hp/* stD6 */)/2;
                }
              },
              _Ht/* stDD */ = E(_Hh/* stCX */.a)-E(_Hj/* stD0 */);
              if(!_Ht/* stDD */){
                return B(_Hq/* stDc */(0));
              }else{
                if(_Ht/* stDD */<=0){
                  return B(_Hq/* stDc */( -_Ht/* stDD */));
                }else{
                  return B(_Hq/* stDc */(_Ht/* stDD */));
                }
              }
            });
          };
          return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_GI/* stCU */, _Ho/* stDI */, _/* EXTERNAL */);});
        };
        return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_GH/* stCT */, _Hm/* stDJ */, _/* EXTERNAL */);});
      };
      return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_GG/* stCS */, _Hk/* stDK */, _/* EXTERNAL */);});
    };
    return new F(function(){return _kd/* Core.Shape.Internal.$fAffineShape3 */(_GF/* stCR */, _Hi/* stDL */, _/* EXTERNAL */);});
  };
  return new T3(0,_Hf/* stDM */,function(_le/* B3 */, _lf/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _k0/* Core.Shape.Internal.$fAffineShape2 */(_GF/* stCR */, _GJ/* stF0 */, _le/* B3 */, _lf/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_Hu/* a2 */ = 20,
_Hv/* a3 */ = new T1(0,_/* EXTERNAL */),
_Hw/* a4 */ = new T1(0,_6/* GHC.Types.[] */),
_Hx/* a5 */ = new T2(0,E(_Hw/* Motion.Grow.a4 */),E(_Hv/* Motion.Grow.a3 */)),
_Hy/* ds */ = 1,
_Hz/* a */ = function(_HA/* s64U */, _HB/* s64V */){
  return new F(function(){return A1(_HB/* s64V */,new T2(0,_7/* GHC.Tuple.() */,_HA/* s64U */));});
},
_HC/* go */ = function(_HD/* s65L */){
  var _HE/* s65M */ = E(_HD/* s65L */);
  if(!_HE/* s65M */._){
    return E(_Hz/* Motion.Grow.a */);
  }else{
    var _HF/* s65P */ = new T(function(){
      var _HG/* s65Q */ = E(_HE/* s65M */.a);
      return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _HG/* s65Q */.a, _HG/* s65Q */.b, _HG/* s65Q */.c, _Hy/* Motion.Grow.ds */, _A2/* Core.Ease.easeTo1 */));
    }),
    _HH/* s65U */ = new T(function(){
      return B(_HC/* Motion.Grow.go */(_HE/* s65M */.b));
    }),
    _HI/* s664 */ = function(_HJ/* s65V */){
      var _HK/* s65W */ = new T(function(){
        return B(A1(_HF/* s65P */,_HJ/* s65V */));
      }),
      _HL/* s663 */ = function(_HM/* s65X */){
        return new F(function(){return A1(_HK/* s65W */,function(_HN/* s65Y */){
          return new F(function(){return A2(_HH/* s65U */,E(_HN/* s65Y */).b, _HM/* s65X */);});
        });});
      };
      return E(_HL/* s663 */);
    };
    return E(_HI/* s664 */);
  }
},
_HO/* go1 */ = function(_HP/* s665 */){
  var _HQ/* s666 */ = E(_HP/* s665 */);
  if(!_HQ/* s666 */._){
    return E(_Hz/* Motion.Grow.a */);
  }else{
    var _HR/* s669 */ = new T(function(){
      var _HS/* s66a */ = E(_HQ/* s666 */.a),
      _HT/* s66p */ = function(_HU/* s66e */){
        var _HV/* s66f */ = new T(function(){
          return B(A1(_HS/* s66a */.b,_HU/* s66e */));
        }),
        _HW/* s66o */ = function(_HX/* s66g */){
          return 1-B(A1(_HV/* s66f */,new T(function(){
            return 1-E(_HX/* s66g */);
          })));
        };
        return E(_HW/* s66o */);
      };
      return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _HS/* s66a */.a, _HT/* s66p */, _HS/* s66a */.c, _Gi/* Motion.Grow.lvl */, _A2/* Core.Ease.easeTo1 */));
    }),
    _HY/* s66q */ = new T(function(){
      return B(_HO/* Motion.Grow.go1 */(_HQ/* s666 */.b));
    }),
    _HZ/* s66A */ = function(_I0/* s66r */){
      var _I1/* s66s */ = new T(function(){
        return B(A1(_HR/* s669 */,_I0/* s66r */));
      }),
      _I2/* s66z */ = function(_I3/* s66t */){
        return new F(function(){return A1(_I1/* s66s */,function(_I4/* s66u */){
          return new F(function(){return A2(_HY/* s66q */,E(_I4/* s66u */).b, _I3/* s66t */);});
        });});
      };
      return E(_I2/* s66z */);
    };
    return E(_HZ/* s66A */);
  }
},
_I5/* eftInt */ = function(_I6/* smpW */, _I7/* smpX */){
  if(_I6/* smpW */<=_I7/* smpX */){
    var _I8/* smq0 */ = function(_I9/* smq1 */){
      return new T2(1,_I9/* smq1 */,new T(function(){
        if(_I9/* smq1 */!=_I7/* smpX */){
          return B(_I8/* smq0 */(_I9/* smq1 */+1|0));
        }else{
          return __Z/* EXTERNAL */;
        }
      }));
    };
    return new F(function(){return _I8/* smq0 */(_I6/* smpW */);});
  }else{
    return __Z/* EXTERNAL */;
  }
},
_Ia/* iforM1 */ = new T(function(){
  return B(_I5/* GHC.Enum.eftInt */(0, 2147483647));
}),
_Ib/* lvl10 */ = 3,
_Ic/* lvl6 */ = new T1(0,_Gj/* Motion.Grow.lvl1 */),
_Id/* lvl7 */ = new T1(0,_Hu/* Motion.Grow.a2 */),
_Ie/* lvl8 */ = -20,
_If/* lvl9 */ = 60,
_Ig/* morph */ = function(_Ih/* skYW */){
  return new T2(2,_Ih/* skYW */,_2E/* GHC.Base.id */);
},
_Ii/* $wa */ = function(_Ij/* s66B */, _Ik/* s66C */, _Il/* s66D */){
  var _Im/* s66E */ = function(_In/* s66F */, _Io/* s66G */){
    var _Ip/* s66H */ = E(_In/* s66F */);
    if(!_Ip/* s66H */._){
      return E(_Hx/* Motion.Grow.a5 */);
    }else{
      var _Iq/* s66I */ = _Ip/* s66H */.a,
      _Ir/* s66K */ = E(_Io/* s66G */);
      if(!_Ir/* s66K */._){
        return E(_Hx/* Motion.Grow.a5 */);
      }else{
        var _Is/* s66L */ = _Ir/* s66K */.a,
        _It/* s66N */ = new T(function(){
          var _Iu/* s66O */ = E(_Iq/* s66I */);
          if(_Iu/* s66O */>=4){
            if(_Iu/* s66O */<=4){
              return E(_Hy/* Motion.Grow.ds */);
            }else{
              return _Iu/* s66O */-4|0;
            }
          }else{
            return 4-_Iu/* s66O */|0;
          }
        }),
        _Iv/* s66Y */ = new T(function(){
          var _Iw/* s671 */ = E(_Iq/* s66I */)-2|0;
          if(1>_Iw/* s671 */){
            return E(_Hy/* Motion.Grow.ds */);
          }else{
            if(3>_Iw/* s671 */){
              return _Iw/* s671 */;
            }else{
              return E(_Ib/* Motion.Grow.lvl10 */);
            }
          }
        }),
        _Ix/* s67G */ = new T(function(){
          var _Iy/* s67F */ = new T(function(){
            var _Iz/* s67B */ = B(_GE/* Core.Shape.Internal.$wcenterRect */(new T(function(){
              return B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, B(_s6/* Core.Ease.opLift */(_Ag/* GHC.Float.timesDouble */, new T1(0,_Iv/* s66Y */), _Ic/* Motion.Grow.lvl6 */)), _Id/* Motion.Grow.lvl7 */));
            }), new T(function(){
              return B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, B(_s6/* Core.Ease.opLift */(_Ag/* GHC.Float.timesDouble */, new T1(0,_It/* s66N */), _Ic/* Motion.Grow.lvl6 */)), _Id/* Motion.Grow.lvl7 */));
            }), _Ic/* Motion.Grow.lvl6 */, _Ic/* Motion.Grow.lvl6 */));
            return new T3(0,_Iz/* s67B */.a,_Iz/* s67B */.b,_Iz/* s67B */.c);
          });
          return B(_rr/* Core.Render.Internal.fill1 */(_Ij/* s66B */, _Iy/* s67F */));
        }),
        _IA/* s67u */ = new T(function(){
          return B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, B(_s6/* Core.Ease.opLift */(_Ag/* GHC.Float.timesDouble */, new T1(0,_It/* s66N */), _Ic/* Motion.Grow.lvl6 */)), _Id/* Motion.Grow.lvl7 */)), new T1(0,new T(function(){
            var _IB/* s67m */ = E(_Iq/* s66I */);
            if(_IB/* s67m */>=4){
              if(_IB/* s67m */<=4){
                return E(_Gi/* Motion.Grow.lvl */);
              }else{
                return E(_Ie/* Motion.Grow.lvl8 */);
              }
            }else{
              return E(_Hu/* Motion.Grow.a2 */);
            }
          }))));
        }),
        _IC/* s67i */ = new T(function(){
          return B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, B(_s6/* Core.Ease.opLift */(_Ag/* GHC.Float.timesDouble */, new T1(0,_Iv/* s66Y */), _Ic/* Motion.Grow.lvl6 */)), _Id/* Motion.Grow.lvl7 */)), new T1(0,new T(function(){
            switch(E(_Iq/* s66I */)){
              case 4:
                return E(_Ie/* Motion.Grow.lvl8 */);
                break;
              case 5:
                return E(_Ie/* Motion.Grow.lvl8 */);
                break;
              default:
                return E(_Gi/* Motion.Grow.lvl */);
            }
          }))));
        }),
        _ID/* s67H */ = B(_FV/* Core.Render.Internal.$fAffineRender1 */(new T2(0,new T(function(){
          return B(_Ig/* Core.Ease.morph */(_Is/* s66L */));
        }),new T(function(){
          return B(_Ig/* Core.Ease.morph */(_Is/* s66L */));
        })), _IC/* s67i */, _IA/* s67u */, _Ix/* s67G */)),
        _IE/* s67K */ = new T(function(){
          return B(_Im/* s66E */(_Ip/* s66H */.b, _Ir/* s66K */.b));
        }),
        _IF/* s67V */ = function(_IG/* s67L */){
          var _IH/* s67M */ = E(_IE/* s67K */);
          return new T2(0,E(_IH/* s67M */.a),E(new T2(2,_IH/* s67M */.b,new T1(1,function(_II/* s67P */){
            return new T2(0,E(new T1(0,new T2(1,_IG/* s67L */,_II/* s67P */))),E(_Hv/* Motion.Grow.a3 */));
          }))));
        };
        return new T2(0,E(_ID/* s67H */.a),E(new T2(2,_ID/* s67H */.b,new T1(1,_IF/* s67V */))));
      }
    }
  },
  _IJ/* s68x */ = function(_IK/* s67Y */){
    var _IL/* s67Z */ = E(_IK/* s67Y */),
    _IM/* s680 */ = _IL/* s67Z */.a,
    _IN/* s682 */ = new T(function(){
      return B(_HO/* Motion.Grow.go1 */(_IM/* s680 */));
    }),
    _IO/* s683 */ = new T(function(){
      return B(_HC/* Motion.Grow.go */(_IM/* s680 */));
    }),
    _IP/* s684 */ = function(_IQ/* s685 */){
      var _IR/* s686 */ = new T(function(){
        return B(A1(_IO/* s683 */,_IQ/* s685 */));
      }),
      _IS/* s68s */ = function(_IT/* s687 */){
        var _IU/* s688 */ = function(_IV/* s689 */){
          return new F(function(){return A2(_IP/* s684 */,E(_IV/* s689 */).b, _IT/* s687 */);});
        },
        _IW/* s68d */ = function(_IX/* s68e */){
          return new F(function(){return _tl/* Core.World.Internal.sleep1 */(_If/* Motion.Grow.lvl9 */, E(_IX/* s68e */).b, _IU/* s688 */);});
        },
        _IY/* s68i */ = function(_IZ/* s68j */){
          return new F(function(){return A2(_IN/* s682 */,E(_IZ/* s68j */).b, _IW/* s68d */);});
        };
        return new F(function(){return A1(_IR/* s686 */,function(_J0/* s68n */){
          return new F(function(){return _tl/* Core.World.Internal.sleep1 */(_If/* Motion.Grow.lvl9 */, E(_J0/* s68n */).b, _IY/* s68i */);});
        });});
      };
      return E(_IS/* s68s */);
    },
    _J1/* s68u */ = new T(function(){
      return B(_rf/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
        return B(_Im/* s66E */(_Ia/* Core.Util.iforM1 */, _IM/* s680 */));
      })));
    });
    return new F(function(){return A1(_Il/* s66D */,new T2(0,new T2(0,_J1/* s68u */,_IP/* s684 */),_IL/* s67Z */.b));});
  };
  return new F(function(){return _Go/* Motion.Grow.$wa1 */(0, _Ik/* s66C */, _IJ/* s68x */);});
},
_J2/* growMot1 */ = function(_J3/* s68y */, _J4/* s68z */, _J5/* s68A */){
  return new T1(0,B(_Ii/* Motion.Grow.$wa */(_J3/* s68y */, _J4/* s68z */, _J5/* s68A */)));
},
_J6/* lvl40 */ = 0.8,
_J7/* lvl41 */ = new T1(0,_J6/* Motion.Main.lvl40 */),
_J8/* lvl42 */ = new T4(0,_Ap/* Motion.Main.lvl21 */,_J7/* Motion.Main.lvl41 */,_yJ/* Motion.Main.lvl4 */,_Ab/* Motion.Main.lvl11 */),
_J9/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Grow"));
}),
_Ja/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sequential easeOutBack"));
}),
_Jb/* lvl45 */ = new T(function(){
  return B(_Fc/* Motion.Main.consView */(_J8/* Motion.Main.lvl42 */, _J2/* Motion.Grow.growMot1 */, _J9/* Motion.Main.lvl43 */, _Ja/* Motion.Main.lvl44 */));
}),
_Jc/* lvl46 */ = new T4(0,_Ab/* Motion.Main.lvl11 */,_A8/* Motion.Main.lvl9 */,_yJ/* Motion.Main.lvl4 */,_Ab/* Motion.Main.lvl11 */),
_Jd/* lvl47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Speed"));
}),
_Je/* lvl48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uniform Distr & Exponential Distr"));
}),
_Jf/* speedMot1 */ = function(_Jg/* sRjo */, _Jh/* sRjp */){
  return new F(function(){return A1(_Jh/* sRjp */,new T2(0,_7/* GHC.Tuple.() */,_Jg/* sRjo */));});
},
_Ji/* speedMot14 */ = 0,
_Jj/* speedMot13 */ = new T1(0,_Ji/* Motion.Speed.speedMot14 */),
_Jk/* speedMot12 */ = new T2(0,_Jj/* Motion.Speed.speedMot13 */,_Jj/* Motion.Speed.speedMot13 */),
_Jl/* intToInt64# */ = function(_Jm/* sf6 */){
  var _Jn/* sf8 */ = hs_intToInt64/* EXTERNAL */(_Jm/* sf6 */);
  return E(_Jn/* sf8 */);
},
_Jo/* integerToInt64 */ = function(_Jp/* s1S1 */){
  var _Jq/* s1S2 */ = E(_Jp/* s1S1 */);
  if(!_Jq/* s1S2 */._){
    return new F(function(){return _Jl/* GHC.IntWord64.intToInt64# */(_Jq/* s1S2 */.a);});
  }else{
    return new F(function(){return I_toInt64/* EXTERNAL */(_Jq/* s1S2 */.a);});
  }
},
_Jr/* $cfromInteger3 */ = function(_Js/* s2dWF */){
  return new F(function(){return _Jo/* GHC.Integer.Type.integerToInt64 */(_Js/* s2dWF */);});
},
_Jt/* $fNumInt64_$c* */ = function(_Ju/* s2dXh */, _Jv/* s2dXi */){
  return new F(function(){return hs_timesInt64/* EXTERNAL */(E(_Ju/* s2dXh */), E(_Jv/* s2dXi */));});
},
_Jw/* $fNumInt64_$c+ */ = function(_Jx/* s2dXB */, _Jy/* s2dXC */){
  return new F(function(){return hs_plusInt64/* EXTERNAL */(E(_Jx/* s2dXB */), E(_Jy/* s2dXC */));});
},
_Jz/* $fNumInt64_$c- */ = function(_JA/* s2dXr */, _JB/* s2dXs */){
  return new F(function(){return hs_minusInt64/* EXTERNAL */(E(_JA/* s2dXr */), E(_JB/* s2dXs */));});
},
_JC/* $w$cabs */ = function(_JD/* s2dWW */){
  var _JE/* s2dWY */ = hs_geInt64/* EXTERNAL */(_JD/* s2dWW */, new Long/* EXTERNAL */(0, 0));
  if(!_JE/* s2dWY */){
    var _JF/* s2dX3 */ = hs_negateInt64/* EXTERNAL */(_JD/* s2dWW */);
    return E(_JF/* s2dX3 */);
  }else{
    return E(_JD/* s2dWW */);
  }
},
_JG/* $fNumInt64_$cabs */ = function(_JH/* s2dX6 */){
  return new F(function(){return _JC/* GHC.Int.$w$cabs */(E(_JH/* s2dX6 */));});
},
_JI/* $fNumInt64_$cnegate */ = function(_JJ/* s2dXa */){
  return new F(function(){return hs_negateInt64/* EXTERNAL */(E(_JJ/* s2dXa */));});
},
_JK/* $w$csignum */ = function(_JL/* s2dWH */){
  var _JM/* s2dWJ */ = hs_gtInt64/* EXTERNAL */(_JL/* s2dWH */, new Long/* EXTERNAL */(0, 0));
  if(!_JM/* s2dWJ */){
    var _JN/* s2dWO */ = hs_eqInt64/* EXTERNAL */(_JL/* s2dWH */, new Long/* EXTERNAL */(0, 0));
    if(!_JN/* s2dWO */){
      return new F(function(){return new Long/* EXTERNAL */(4294967295, -1);});
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return new F(function(){return new Long/* EXTERNAL */(1, 0);});
  }
},
_JO/* $fNumInt64_$csignum */ = function(_JP/* s2dWS */){
  return new F(function(){return _JK/* GHC.Int.$w$csignum */(E(_JP/* s2dWS */));});
},
_JQ/* $fNumInt64 */ = {_:0,a:_Jw/* GHC.Int.$fNumInt64_$c+ */,b:_Jz/* GHC.Int.$fNumInt64_$c- */,c:_Jt/* GHC.Int.$fNumInt64_$c* */,d:_JI/* GHC.Int.$fNumInt64_$cnegate */,e:_JG/* GHC.Int.$fNumInt64_$cabs */,f:_JO/* GHC.Int.$fNumInt64_$csignum */,g:_Jr/* GHC.Int.$cfromInteger3 */},
_JR/* lvl */ = new T1(0,0),
_JS/* orInteger */ = function(_JT/* s1KS */, _JU/* s1KT */){
  while(1){
    var _JV/* s1KU */ = E(_JT/* s1KS */);
    if(!_JV/* s1KU */._){
      var _JW/* s1KV */ = _JV/* s1KU */.a,
      _JX/* s1KW */ = E(_JU/* s1KT */);
      if(!_JX/* s1KW */._){
        return new T1(0,(_JW/* s1KV */>>>0|_JX/* s1KW */.a>>>0)>>>0&4294967295);
      }else{
        _JT/* s1KS */ = new T1(1,I_fromInt/* EXTERNAL */(_JW/* s1KV */));
        _JU/* s1KT */ = _JX/* s1KW */;
        continue;
      }
    }else{
      var _JY/* s1L7 */ = E(_JU/* s1KT */);
      if(!_JY/* s1L7 */._){
        _JT/* s1KS */ = _JV/* s1KU */;
        _JU/* s1KT */ = new T1(1,I_fromInt/* EXTERNAL */(_JY/* s1L7 */.a));
        continue;
      }else{
        return new T1(1,I_or/* EXTERNAL */(_JV/* s1KU */.a, _JY/* s1L7 */.a));
      }
    }
  }
},
_JZ/* shiftLInteger */ = function(_K0/* s1Jk */, _K1/* s1Jl */){
  while(1){
    var _K2/* s1Jm */ = E(_K0/* s1Jk */);
    if(!_K2/* s1Jm */._){
      _K0/* s1Jk */ = new T1(1,I_fromInt/* EXTERNAL */(_K2/* s1Jm */.a));
      continue;
    }else{
      return new T1(1,I_shiftLeft/* EXTERNAL */(_K2/* s1Jm */.a, _K1/* s1Jl */));
    }
  }
},
_K3/* mkInteger_f */ = function(_K4/* s1S6 */){
  var _K5/* s1S7 */ = E(_K4/* s1S6 */);
  if(!_K5/* s1S7 */._){
    return E(_JR/* GHC.Integer.Type.lvl */);
  }else{
    return new F(function(){return _JS/* GHC.Integer.Type.orInteger */(new T1(0,E(_K5/* s1S7 */.a)), B(_JZ/* GHC.Integer.Type.shiftLInteger */(B(_K3/* GHC.Integer.Type.mkInteger_f */(_K5/* s1S7 */.b)), 31)));});
  }
},
_K6/* log2I1 */ = new T1(0,1),
_K7/* lvl2 */ = new T1(0,2147483647),
_K8/* plusInteger */ = function(_K9/* s1Qe */, _Ka/* s1Qf */){
  while(1){
    var _Kb/* s1Qg */ = E(_K9/* s1Qe */);
    if(!_Kb/* s1Qg */._){
      var _Kc/* s1Qh */ = _Kb/* s1Qg */.a,
      _Kd/* s1Qi */ = E(_Ka/* s1Qf */);
      if(!_Kd/* s1Qi */._){
        var _Ke/* s1Qj */ = _Kd/* s1Qi */.a,
        _Kf/* s1Qk */ = addC/* EXTERNAL */(_Kc/* s1Qh */, _Ke/* s1Qj */);
        if(!E(_Kf/* s1Qk */.b)){
          return new T1(0,_Kf/* s1Qk */.a);
        }else{
          _K9/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_Kc/* s1Qh */));
          _Ka/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_Ke/* s1Qj */));
          continue;
        }
      }else{
        _K9/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_Kc/* s1Qh */));
        _Ka/* s1Qf */ = _Kd/* s1Qi */;
        continue;
      }
    }else{
      var _Kg/* s1Qz */ = E(_Ka/* s1Qf */);
      if(!_Kg/* s1Qz */._){
        _K9/* s1Qe */ = _Kb/* s1Qg */;
        _Ka/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_Kg/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_Kb/* s1Qg */.a, _Kg/* s1Qz */.a));
      }
    }
  }
},
_Kh/* lvl3 */ = new T(function(){
  return B(_K8/* GHC.Integer.Type.plusInteger */(_K7/* GHC.Integer.Type.lvl2 */, _K6/* GHC.Integer.Type.log2I1 */));
}),
_Ki/* negateInteger */ = function(_Kj/* s1QH */){
  var _Kk/* s1QI */ = E(_Kj/* s1QH */);
  if(!_Kk/* s1QI */._){
    var _Kl/* s1QK */ = E(_Kk/* s1QI */.a);
    return (_Kl/* s1QK */==(-2147483648)) ? E(_Kh/* GHC.Integer.Type.lvl3 */) : new T1(0, -_Kl/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_Kk/* s1QI */.a));
  }
},
_Km/* mkInteger */ = function(_Kn/* s1Sf */, _Ko/* s1Sg */){
  if(!E(_Kn/* s1Sf */)){
    return new F(function(){return _Ki/* GHC.Integer.Type.negateInteger */(B(_K3/* GHC.Integer.Type.mkInteger_f */(_Ko/* s1Sg */)));});
  }else{
    return new F(function(){return _K3/* GHC.Integer.Type.mkInteger_f */(_Ko/* s1Sg */);});
  }
},
_Kp/* sfn3 */ = 2147483647,
_Kq/* sfn4 */ = 2147483647,
_Kr/* sfn5 */ = 1,
_Ks/* sfn6 */ = new T2(1,_Kr/* sfn5 */,_6/* GHC.Types.[] */),
_Kt/* sfn7 */ = new T2(1,_Kq/* sfn4 */,_Ks/* sfn6 */),
_Ku/* sfn8 */ = new T2(1,_Kp/* sfn3 */,_Kt/* sfn7 */),
_Kv/* $fRandomCLLong3 */ = new T(function(){
  return B(_Km/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _Ku/* sfn8 */));
}),
_Kw/* sfn9 */ = 0,
_Kx/* sfna */ = 0,
_Ky/* sfnb */ = 2,
_Kz/* sfnc */ = new T2(1,_Ky/* sfnb */,_6/* GHC.Types.[] */),
_KA/* sfnd */ = new T2(1,_Kx/* sfna */,_Kz/* sfnc */),
_KB/* sfne */ = new T2(1,_Kw/* sfn9 */,_KA/* sfnd */),
_KC/* $fRandomCLLong4 */ = new T(function(){
  return B(_Km/* GHC.Integer.Type.mkInteger */(_av/* GHC.Types.False */, _KB/* sfne */));
}),
_KD/* $fRandomDouble4 */ = new Long/* EXTERNAL */(2, 0),
_KE/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_KF/* $fRandomDouble5 */ = new T(function(){
  return B(err/* EXTERNAL */(_KE/* System.Random.lvl1 */));
}),
_KG/* $fRandomDouble6 */ = new Long/* EXTERNAL */(1, 0),
_KH/* $fBoundedInt64_$cmaxBound */ = new Long/* EXTERNAL */(4294967295, 2147483647),
_KI/* $fBoundedInt64_$cminBound */ = new Long/* EXTERNAL */(0, -2147483648),
_KJ/* $fBoundedInt64 */ = new T2(0,_KI/* GHC.Int.$fBoundedInt64_$cminBound */,_KH/* GHC.Int.$fBoundedInt64_$cmaxBound */),
_KK/* $fEnumRatio1 */ = new T1(0,1),
_KL/* $p1Integral */ = function(_KM/* sveb */){
  return E(E(_KM/* sveb */).a);
},
_KN/* $p1Real */ = function(_KO/* svfM */){
  return E(E(_KO/* svfM */).a);
},
_KP/* fromInteger */ = function(_KQ/* s6Gq */){
  return E(E(_KQ/* s6Gq */).g);
},
_KR/* gtInteger */ = function(_KS/* s1G4 */, _KT/* s1G5 */){
  var _KU/* s1G6 */ = E(_KS/* s1G4 */);
  if(!_KU/* s1G6 */._){
    var _KV/* s1G7 */ = _KU/* s1G6 */.a,
    _KW/* s1G8 */ = E(_KT/* s1G5 */);
    return (_KW/* s1G8 */._==0) ? _KV/* s1G7 */>_KW/* s1G8 */.a : I_compareInt/* EXTERNAL */(_KW/* s1G8 */.a, _KV/* s1G7 */)<0;
  }else{
    var _KX/* s1Gf */ = _KU/* s1G6 */.a,
    _KY/* s1Gg */ = E(_KT/* s1G5 */);
    return (_KY/* s1Gg */._==0) ? I_compareInt/* EXTERNAL */(_KX/* s1Gf */, _KY/* s1Gg */.a)>0 : I_compare/* EXTERNAL */(_KX/* s1Gf */, _KY/* s1Gg */.a)>0;
  }
},
_KZ/* maxBound */ = function(_L0/* smmz */){
  return E(E(_L0/* smmz */).b);
},
_L1/* toInteger */ = function(_L2/* svfB */){
  return E(E(_L2/* svfB */).i);
},
_L3/* integralEnumFrom */ = function(_L4/* svkx */, _L5/* svky */, _L6/* svkz */){
  var _L7/* svkC */ = new T(function(){
    return B(_KP/* GHC.Num.fromInteger */(new T(function(){
      return B(_KN/* GHC.Real.$p1Real */(new T(function(){
        return B(_KL/* GHC.Real.$p1Integral */(_L4/* svkx */));
      })));
    })));
  }),
  _L8/* svkE */ = new T(function(){
    return B(_KZ/* GHC.Enum.maxBound */(_L5/* svky */));
  }),
  _L9/* svkF */ = function(_La/* svkG */){
    return (!B(_KR/* GHC.Integer.Type.gtInteger */(_La/* svkG */, B(A2(_L1/* GHC.Real.toInteger */,_L4/* svkx */, _L8/* svkE */))))) ? new T2(1,new T(function(){
      return B(A1(_L7/* svkC */,_La/* svkG */));
    }),new T(function(){
      return B(_L9/* svkF */(B(_K8/* GHC.Integer.Type.plusInteger */(_La/* svkG */, _KK/* GHC.Real.$fEnumRatio1 */))));
    })) : __Z/* EXTERNAL */;
  };
  return new F(function(){return _L9/* svkF */(B(A2(_L1/* GHC.Real.toInteger */,_L4/* svkx */, _L6/* svkz */)));});
},
_Lb/* $fEnumInt64_$cenumFrom */ = function(_Lc/* B1 */){
  return new F(function(){return _L3/* GHC.Real.integralEnumFrom */(_Ld/* GHC.Int.$fIntegralInt64 */, _KJ/* GHC.Int.$fBoundedInt64 */, _Lc/* B1 */);});
},
_Le/* $fEnumInteger1 */ = new T1(0,0),
_Lf/* geInteger */ = function(_Lg/* s1Fo */, _Lh/* s1Fp */){
  var _Li/* s1Fq */ = E(_Lg/* s1Fo */);
  if(!_Li/* s1Fq */._){
    var _Lj/* s1Fr */ = _Li/* s1Fq */.a,
    _Lk/* s1Fs */ = E(_Lh/* s1Fp */);
    return (_Lk/* s1Fs */._==0) ? _Lj/* s1Fr */>=_Lk/* s1Fs */.a : I_compareInt/* EXTERNAL */(_Lk/* s1Fs */.a, _Lj/* s1Fr */)<=0;
  }else{
    var _Ll/* s1Fz */ = _Li/* s1Fq */.a,
    _Lm/* s1FA */ = E(_Lh/* s1Fp */);
    return (_Lm/* s1FA */._==0) ? I_compareInt/* EXTERNAL */(_Ll/* s1Fz */, _Lm/* s1FA */.a)>=0 : I_compare/* EXTERNAL */(_Ll/* s1Fz */, _Lm/* s1FA */.a)>=0;
  }
},
_Ln/* ltInteger */ = function(_Lo/* s1FJ */, _Lp/* s1FK */){
  var _Lq/* s1FL */ = E(_Lo/* s1FJ */);
  if(!_Lq/* s1FL */._){
    var _Lr/* s1FM */ = _Lq/* s1FL */.a,
    _Ls/* s1FN */ = E(_Lp/* s1FK */);
    return (_Ls/* s1FN */._==0) ? _Lr/* s1FM */<_Ls/* s1FN */.a : I_compareInt/* EXTERNAL */(_Ls/* s1FN */.a, _Lr/* s1FM */)>0;
  }else{
    var _Lt/* s1FU */ = _Lq/* s1FL */.a,
    _Lu/* s1FV */ = E(_Lp/* s1FK */);
    return (_Lu/* s1FV */._==0) ? I_compareInt/* EXTERNAL */(_Lt/* s1FU */, _Lu/* s1FV */.a)<0 : I_compare/* EXTERNAL */(_Lt/* s1FU */, _Lu/* s1FV */.a)<0;
  }
},
_Lv/* up_fb */ = function(_Lw/* smnV */, _Lx/* smnW */, _Ly/* smnX */, _Lz/* smnY */, _LA/* smnZ */){
  var _LB/* smo0 */ = function(_LC/* smo1 */){
    if(!B(_KR/* GHC.Integer.Type.gtInteger */(_LC/* smo1 */, _LA/* smnZ */))){
      return new F(function(){return A2(_Lw/* smnV */,_LC/* smo1 */, new T(function(){
        return B(_LB/* smo0 */(B(_K8/* GHC.Integer.Type.plusInteger */(_LC/* smo1 */, _Lz/* smnY */))));
      }));});
    }else{
      return E(_Lx/* smnW */);
    }
  };
  return new F(function(){return _LB/* smo0 */(_Ly/* smnX */);});
},
_LD/* enumDeltaToIntegerFB */ = function(_LE/* smK3 */, _LF/* smK4 */, _LG/* smK5 */, _LH/* smK6 */, _LI/* smK7 */){
  if(!B(_Lf/* GHC.Integer.Type.geInteger */(_LH/* smK6 */, _Le/* GHC.Enum.$fEnumInteger1 */))){
    var _LJ/* smK9 */ = function(_LK/* smKa */){
      if(!B(_Ln/* GHC.Integer.Type.ltInteger */(_LK/* smKa */, _LI/* smK7 */))){
        return new F(function(){return A2(_LE/* smK3 */,_LK/* smKa */, new T(function(){
          return B(_LJ/* smK9 */(B(_K8/* GHC.Integer.Type.plusInteger */(_LK/* smKa */, _LH/* smK6 */))));
        }));});
      }else{
        return E(_LF/* smK4 */);
      }
    };
    return new F(function(){return _LJ/* smK9 */(_LG/* smK5 */);});
  }else{
    return new F(function(){return _Lv/* GHC.Enum.up_fb */(_LE/* smK3 */, _LF/* smK4 */, _LG/* smK5 */, _LH/* smK6 */, _LI/* smK7 */);});
  }
},
_LL/* minBound */ = function(_LM/* smmv */){
  return E(E(_LM/* smmv */).a);
},
_LN/* minusInteger */ = function(_LO/* s1P0 */, _LP/* s1P1 */){
  while(1){
    var _LQ/* s1P2 */ = E(_LO/* s1P0 */);
    if(!_LQ/* s1P2 */._){
      var _LR/* s1P3 */ = _LQ/* s1P2 */.a,
      _LS/* s1P4 */ = E(_LP/* s1P1 */);
      if(!_LS/* s1P4 */._){
        var _LT/* s1P5 */ = _LS/* s1P4 */.a,
        _LU/* s1P6 */ = subC/* EXTERNAL */(_LR/* s1P3 */, _LT/* s1P5 */);
        if(!E(_LU/* s1P6 */.b)){
          return new T1(0,_LU/* s1P6 */.a);
        }else{
          _LO/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_LR/* s1P3 */));
          _LP/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_LT/* s1P5 */));
          continue;
        }
      }else{
        _LO/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_LR/* s1P3 */));
        _LP/* s1P1 */ = _LS/* s1P4 */;
        continue;
      }
    }else{
      var _LV/* s1Pl */ = E(_LP/* s1P1 */);
      if(!_LV/* s1Pl */._){
        _LO/* s1P0 */ = _LQ/* s1P2 */;
        _LP/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_LV/* s1Pl */.a));
        continue;
      }else{
        return new T1(1,I_sub/* EXTERNAL */(_LQ/* s1P2 */.a, _LV/* s1Pl */.a));
      }
    }
  }
},
_LW/* integralEnumFromThen */ = function(_LX/* svk6 */, _LY/* svk7 */, _LZ/* svk8 */, _M0/* svk9 */){
  var _M1/* svka */ = B(A2(_L1/* GHC.Real.toInteger */,_LX/* svk6 */, _M0/* svk9 */)),
  _M2/* svkb */ = B(A2(_L1/* GHC.Real.toInteger */,_LX/* svk6 */, _LZ/* svk8 */));
  if(!B(_Lf/* GHC.Integer.Type.geInteger */(_M1/* svka */, _M2/* svkb */))){
    var _M3/* svkf */ = new T(function(){
      return B(_KP/* GHC.Num.fromInteger */(new T(function(){
        return B(_KN/* GHC.Real.$p1Real */(new T(function(){
          return B(_KL/* GHC.Real.$p1Integral */(_LX/* svk6 */));
        })));
      })));
    }),
    _M4/* svkj */ = function(_M5/* svkg */, _M6/* svkh */){
      return new T2(1,new T(function(){
        return B(A1(_M3/* svkf */,_M5/* svkg */));
      }),_M6/* svkh */);
    };
    return new F(function(){return _LD/* GHC.Enum.enumDeltaToIntegerFB */(_M4/* svkj */, _6/* GHC.Types.[] */, _M2/* svkb */, B(_LN/* GHC.Integer.Type.minusInteger */(_M1/* svka */, _M2/* svkb */)), B(A2(_L1/* GHC.Real.toInteger */,_LX/* svk6 */, new T(function(){
      return B(_LL/* GHC.Enum.minBound */(_LY/* svk7 */));
    }))));});
  }else{
    var _M7/* svkp */ = new T(function(){
      return B(_KP/* GHC.Num.fromInteger */(new T(function(){
        return B(_KN/* GHC.Real.$p1Real */(new T(function(){
          return B(_KL/* GHC.Real.$p1Integral */(_LX/* svk6 */));
        })));
      })));
    }),
    _M8/* svkt */ = function(_M9/* svkq */, _Ma/* svkr */){
      return new T2(1,new T(function(){
        return B(A1(_M7/* svkp */,_M9/* svkq */));
      }),_Ma/* svkr */);
    };
    return new F(function(){return _LD/* GHC.Enum.enumDeltaToIntegerFB */(_M8/* svkt */, _6/* GHC.Types.[] */, _M2/* svkb */, B(_LN/* GHC.Integer.Type.minusInteger */(_M1/* svka */, _M2/* svkb */)), B(A2(_L1/* GHC.Real.toInteger */,_LX/* svk6 */, new T(function(){
      return B(_KZ/* GHC.Enum.maxBound */(_LY/* svk7 */));
    }))));});
  }
},
_Mb/* $fEnumInt64_$cenumFromThen */ = function(_Mc/* B2 */, _Lc/* B1 */){
  return new F(function(){return _LW/* GHC.Real.integralEnumFromThen */(_Ld/* GHC.Int.$fIntegralInt64 */, _KJ/* GHC.Int.$fBoundedInt64 */, _Mc/* B2 */, _Lc/* B1 */);});
},
_Md/* integralEnumFromThenTo */ = function(_Me/* svjD */, _Mf/* svjE */, _Mg/* svjF */, _Mh/* svjG */){
  var _Mi/* svjH */ = B(A2(_L1/* GHC.Real.toInteger */,_Me/* svjD */, _Mf/* svjE */)),
  _Mj/* svjK */ = new T(function(){
    return B(_KP/* GHC.Num.fromInteger */(new T(function(){
      return B(_KN/* GHC.Real.$p1Real */(new T(function(){
        return B(_KL/* GHC.Real.$p1Integral */(_Me/* svjD */));
      })));
    })));
  }),
  _Mk/* svjO */ = function(_Ml/* svjL */, _Mm/* svjM */){
    return new T2(1,new T(function(){
      return B(A1(_Mj/* svjK */,_Ml/* svjL */));
    }),_Mm/* svjM */);
  };
  return new F(function(){return _LD/* GHC.Enum.enumDeltaToIntegerFB */(_Mk/* svjO */, _6/* GHC.Types.[] */, _Mi/* svjH */, B(_LN/* GHC.Integer.Type.minusInteger */(B(A2(_L1/* GHC.Real.toInteger */,_Me/* svjD */, _Mg/* svjF */)), _Mi/* svjH */)), B(A2(_L1/* GHC.Real.toInteger */,_Me/* svjD */, _Mh/* svjG */)));});
},
_Mn/* $fEnumInt64_$cenumFromThenTo */ = function(_Mo/* B3 */, _Mc/* B2 */, _Lc/* B1 */){
  return new F(function(){return _Md/* GHC.Real.integralEnumFromThenTo */(_Ld/* GHC.Int.$fIntegralInt64 */, _Mo/* B3 */, _Mc/* B2 */, _Lc/* B1 */);});
},
_Mp/* integralEnumFromTo */ = function(_Mq/* svjS */, _Mr/* svjT */, _Ms/* svjU */){
  var _Mt/* svjX */ = new T(function(){
    return B(_KP/* GHC.Num.fromInteger */(new T(function(){
      return B(_KN/* GHC.Real.$p1Real */(new T(function(){
        return B(_KL/* GHC.Real.$p1Integral */(_Mq/* svjS */));
      })));
    })));
  }),
  _Mu/* svjZ */ = function(_Mv/* svk0 */){
    return (!B(_KR/* GHC.Integer.Type.gtInteger */(_Mv/* svk0 */, B(A2(_L1/* GHC.Real.toInteger */,_Mq/* svjS */, _Ms/* svjU */))))) ? new T2(1,new T(function(){
      return B(A1(_Mt/* svjX */,_Mv/* svk0 */));
    }),new T(function(){
      return B(_Mu/* svjZ */(B(_K8/* GHC.Integer.Type.plusInteger */(_Mv/* svk0 */, _KK/* GHC.Real.$fEnumRatio1 */))));
    })) : __Z/* EXTERNAL */;
  };
  return new F(function(){return _Mu/* svjZ */(B(A2(_L1/* GHC.Real.toInteger */,_Mq/* svjS */, _Mr/* svjT */)));});
},
_Mw/* $fEnumInt64_$cenumFromTo */ = function(_Mc/* B2 */, _Lc/* B1 */){
  return new F(function(){return _Mp/* GHC.Real.integralEnumFromTo */(_Ld/* GHC.Int.$fIntegralInt64 */, _Mc/* B2 */, _Lc/* B1 */);});
},
_Mx/* $fEnumInt6 */ = new T(function(){
  return hs_intToInt64/* EXTERNAL */(2147483647);
}),
_My/* smallInteger */ = function(_Mz/* B1 */){
  return new T1(0,_Mz/* B1 */);
},
_MA/* int64ToInteger */ = function(_MB/* s1RA */){
  var _MC/* s1RC */ = hs_intToInt64/* EXTERNAL */(2147483647),
  _MD/* s1RG */ = hs_leInt64/* EXTERNAL */(_MB/* s1RA */, _MC/* s1RC */);
  if(!_MD/* s1RG */){
    return new T1(1,I_fromInt64/* EXTERNAL */(_MB/* s1RA */));
  }else{
    var _ME/* s1RN */ = hs_intToInt64/* EXTERNAL */(-2147483648),
    _MF/* s1RR */ = hs_geInt64/* EXTERNAL */(_MB/* s1RA */, _ME/* s1RN */);
    if(!_MF/* s1RR */){
      return new T1(1,I_fromInt64/* EXTERNAL */(_MB/* s1RA */));
    }else{
      var _MG/* s1RY */ = hs_int64ToInt/* EXTERNAL */(_MB/* s1RA */);
      return new F(function(){return _My/* GHC.Integer.Type.smallInteger */(_MG/* s1RY */);});
    }
  }
},
_MH/* $fIntegralInt64_$ctoInteger */ = function(_MI/* s2dYm */){
  return new F(function(){return _MA/* GHC.Integer.Type.int64ToInteger */(E(_MI/* s2dYm */));});
},
_MJ/* integerToJSString */ = function(_MK/* s1Iv */){
  while(1){
    var _ML/* s1Iw */ = E(_MK/* s1Iv */);
    if(!_ML/* s1Iw */._){
      _MK/* s1Iv */ = new T1(1,I_fromInt/* EXTERNAL */(_ML/* s1Iw */.a));
      continue;
    }else{
      return new F(function(){return I_toString/* EXTERNAL */(_ML/* s1Iw */.a);});
    }
  }
},
_MM/* integerToString */ = function(_MN/* sfbi */, _MO/* sfbj */){
  return new F(function(){return _2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_MJ/* GHC.Integer.Type.integerToJSString */(_MN/* sfbi */))), _MO/* sfbj */);});
},
_MP/* shows9 */ = new T1(0,0),
_MQ/* $w$cshowsPrec1 */ = function(_MR/* sfcx */, _MS/* sfcy */, _MT/* sfcz */){
  if(_MR/* sfcx */<=6){
    return new F(function(){return _MM/* GHC.Show.integerToString */(_MS/* sfcy */, _MT/* sfcz */);});
  }else{
    if(!B(_Ln/* GHC.Integer.Type.ltInteger */(_MS/* sfcy */, _MP/* GHC.Show.shows9 */))){
      return new F(function(){return _MM/* GHC.Show.integerToString */(_MS/* sfcy */, _MT/* sfcz */);});
    }else{
      return new T2(1,_3c/* GHC.Show.shows8 */,new T(function(){
        return B(_2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_MJ/* GHC.Integer.Type.integerToJSString */(_MS/* sfcy */))), new T2(1,_3b/* GHC.Show.shows7 */,_MT/* sfcz */)));
      }));
    }
  }
},
_MU/* $fShowInt64_$cshow */ = function(_MV/* s2dYy */){
  return new F(function(){return _MQ/* GHC.Show.$w$cshowsPrec1 */(0, B(_MH/* GHC.Int.$fIntegralInt64_$ctoInteger */(_MV/* s2dYy */)), _6/* GHC.Types.[] */);});
},
_MW/* $fShowInt3 */ = function(_MX/* s2dYA */, _MY/* s2dYB */){
  return new F(function(){return _MQ/* GHC.Show.$w$cshowsPrec1 */(0, B(_MA/* GHC.Integer.Type.int64ToInteger */(E(_MX/* s2dYA */))), _MY/* s2dYB */);});
},
_MZ/* $fShowInt64_$cshowList */ = function(_N0/* s2dYF */, _N1/* s2dYG */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_MW/* GHC.Int.$fShowInt3 */, _N0/* s2dYF */, _N1/* s2dYG */);});
},
_N2/* $fShowInt64_$cshowsPrec */ = function(_N3/* s2dYp */, _N4/* s2dYq */){
  var _N5/* s2dYr */ = new T(function(){
    return B(_MA/* GHC.Integer.Type.int64ToInteger */(E(_N4/* s2dYq */)));
  });
  return function(_N6/* s2dYu */){
    return new F(function(){return _MQ/* GHC.Show.$w$cshowsPrec1 */(E(_N3/* s2dYp */), _N5/* s2dYr */, _N6/* s2dYu */);});
  };
},
_N7/* $fShowInt64 */ = new T3(0,_N2/* GHC.Int.$fShowInt64_$cshowsPrec */,_MU/* GHC.Int.$fShowInt64_$cshow */,_MZ/* GHC.Int.$fShowInt64_$cshowList */),
_N8/* lvl */ = new T2(1,_3b/* GHC.Show.shows7 */,_6/* GHC.Types.[] */),
_N9/* $fShow(,)1 */ = function(_Na/* sfg4 */, _Nb/* sfg5 */, _Nc/* sfg6 */){
  return new F(function(){return A1(_Na/* sfg4 */,new T2(1,_23/* GHC.Show.showList__1 */,new T(function(){
    return B(A1(_Nb/* sfg5 */,_Nc/* sfg6 */));
  })));});
},
_Nd/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_Ne/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_Nf/* errorEmptyList */ = function(_Ng/* s9t7 */){
  return new F(function(){return err/* EXTERNAL */(B(_2/* GHC.Base.++ */(_Ne/* GHC.List.prel_list_str */, new T(function(){
    return B(_2/* GHC.Base.++ */(_Ng/* s9t7 */, _Nd/* GHC.List.lvl */));
  },1))));});
},
_Nh/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("foldr1"));
}),
_Ni/* lvl8 */ = new T(function(){
  return B(_Nf/* GHC.List.errorEmptyList */(_Nh/* GHC.List.lvl7 */));
}),
_Nj/* foldr1 */ = function(_Nk/* s9Ah */, _Nl/* s9Ai */){
  var _Nm/* s9Aj */ = E(_Nl/* s9Ai */);
  if(!_Nm/* s9Aj */._){
    return E(_Ni/* GHC.List.lvl8 */);
  }else{
    var _Nn/* s9Ak */ = _Nm/* s9Aj */.a,
    _No/* s9Am */ = E(_Nm/* s9Aj */.b);
    if(!_No/* s9Am */._){
      return E(_Nn/* s9Ak */);
    }else{
      return new F(function(){return A2(_Nk/* s9Ah */,_Nn/* s9Ak */, new T(function(){
        return B(_Nj/* GHC.List.foldr1 */(_Nk/* s9Ah */, _No/* s9Am */));
      }));});
    }
  }
},
_Np/* lvl14 */ = function(_Nq/* smEb */){
  return new F(function(){return _3d/* GHC.Show.$wshowSignedInt */(0, -2147483648, _Nq/* smEb */);});
},
_Nr/* lvl15 */ = function(_Ns/* smEc */){
  return new F(function(){return _3d/* GHC.Show.$wshowSignedInt */(0, 2147483647, _Ns/* smEc */);});
},
_Nt/* lvl16 */ = new T2(1,_Nr/* GHC.Enum.lvl15 */,_6/* GHC.Types.[] */),
_Nu/* lvl17 */ = new T2(1,_Np/* GHC.Enum.lvl14 */,_Nt/* GHC.Enum.lvl16 */),
_Nv/* lvl18 */ = new T(function(){
  return B(_Nj/* GHC.List.foldr1 */(_N9/* GHC.Show.$fShow(,)1 */, _Nu/* GHC.Enum.lvl17 */));
}),
_Nw/* lvl19 */ = new T(function(){
  return B(A1(_Nv/* GHC.Enum.lvl18 */,_N8/* GHC.Enum.lvl */));
}),
_Nx/* lvl20 */ = new T2(1,_3c/* GHC.Show.shows8 */,_Nw/* GHC.Enum.lvl19 */),
_Ny/* lvl21 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */(") is outside of Int\'s bounds ", _Nx/* GHC.Enum.lvl20 */));
}),
_Nz/* show */ = function(_NA/* sfb3 */){
  return E(E(_NA/* sfb3 */).b);
},
_NB/* lvl22 */ = function(_NC/* smEd */, _ND/* smEe */, _NE/* smEf */){
  var _NF/* smEj */ = new T(function(){
    var _NG/* smEi */ = new T(function(){
      return B(unAppCStr/* EXTERNAL */("}: value (", new T(function(){
        return B(_2/* GHC.Base.++ */(B(A2(_Nz/* GHC.Show.show */,_NE/* smEf */, _ND/* smEe */)), _Ny/* GHC.Enum.lvl21 */));
      })));
    },1);
    return B(_2/* GHC.Base.++ */(_NC/* smEd */, _NG/* smEi */));
  });
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.fromEnum{", _NF/* smEj */)));});
},
_NH/* fromEnumError */ = function(_NI/* smEl */, _NJ/* smEm */, _NK/* smEn */){
  return new F(function(){return _NB/* GHC.Enum.lvl22 */(_NJ/* smEm */, _NK/* smEn */, _NI/* smEl */);});
},
_NL/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Int64"));
}),
_NM/* lvl13 */ = function(_NN/* s2dYH */){
  return new F(function(){return _NH/* GHC.Enum.fromEnumError */(_N7/* GHC.Int.$fShowInt64 */, _NL/* GHC.Int.lvl1 */, _NN/* s2dYH */);});
},
_NO/* $fEnumInt7 */ = function(_NP/* s2dYI */){
  return new F(function(){return _NM/* GHC.Int.lvl13 */(_NP/* s2dYI */);});
},
_NQ/* $fEnumInt9 */ = new T(function(){
  return hs_intToInt64/* EXTERNAL */(-2147483648);
}),
_NR/* $w$cfromEnum */ = function(_NS/* s2dYK */){
  var _NT/* s2dYO */ = hs_geInt64/* EXTERNAL */(_NS/* s2dYK */, E(_NQ/* GHC.Int.$fEnumInt9 */));
  if(!_NT/* s2dYO */){
    return new F(function(){return _NO/* GHC.Int.$fEnumInt7 */(_NS/* s2dYK */);});
  }else{
    var _NU/* s2dYW */ = hs_leInt64/* EXTERNAL */(_NS/* s2dYK */, E(_Mx/* GHC.Int.$fEnumInt6 */));
    if(!_NU/* s2dYW */){
      return new F(function(){return _NO/* GHC.Int.$fEnumInt7 */(_NS/* s2dYK */);});
    }else{
      var _NV/* s2dZ2 */ = hs_int64ToInt/* EXTERNAL */(_NS/* s2dYK */);
      return E(_NV/* s2dZ2 */);
    }
  }
},
_NW/* $fEnumInt64_$cfromEnum */ = function(_NX/* s2dZ5 */){
  return new F(function(){return _NR/* GHC.Int.$w$cfromEnum */(E(_NX/* s2dZ5 */));});
},
_NY/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}: tried to take `pred\' of minBound"));
}),
_NZ/* lvl2 */ = function(_O0/* smrD */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.pred{", new T(function(){
    return B(_2/* GHC.Base.++ */(_O0/* smrD */, _NY/* GHC.Enum.lvl1 */));
  }))));});
},
_O1/* predError */ = function(_O2/* B1 */){
  return new F(function(){return _NZ/* GHC.Enum.lvl2 */(_O2/* B1 */);});
},
_O3/* $fEnumInt10 */ = new T(function(){
  return B(_O1/* GHC.Enum.predError */(_NL/* GHC.Int.lvl1 */));
}),
_O4/* $w$cpred */ = function(_O5/* s2dXS */){
  var _O6/* s2dXU */ = hs_neInt64/* EXTERNAL */(_O5/* s2dXS */, new Long/* EXTERNAL */(0, -2147483648));
  if(!_O6/* s2dXU */){
    return E(_O3/* GHC.Int.$fEnumInt10 */);
  }else{
    var _O7/* s2dY0 */ = hs_minusInt64/* EXTERNAL */(_O5/* s2dXS */, new Long/* EXTERNAL */(1, 0));
    return E(_O7/* s2dY0 */);
  }
},
_O8/* $fEnumInt64_$cpred */ = function(_O9/* s2dY3 */){
  return new F(function(){return _O4/* GHC.Int.$w$cpred */(E(_O9/* s2dY3 */));});
},
_Oa/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}: tried to take `succ\' of maxBound"));
}),
_Ob/* lvl4 */ = function(_Oc/* smrG */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.succ{", new T(function(){
    return B(_2/* GHC.Base.++ */(_Oc/* smrG */, _Oa/* GHC.Enum.lvl3 */));
  }))));});
},
_Od/* succError */ = function(_O2/* B1 */){
  return new F(function(){return _Ob/* GHC.Enum.lvl4 */(_O2/* B1 */);});
},
_Oe/* $fEnumInt11 */ = new T(function(){
  return B(_Od/* GHC.Enum.succError */(_NL/* GHC.Int.lvl1 */));
}),
_Of/* $w$csucc */ = function(_Og/* s2dY7 */){
  var _Oh/* s2dY9 */ = hs_neInt64/* EXTERNAL */(_Og/* s2dY7 */, new Long/* EXTERNAL */(4294967295, 2147483647));
  if(!_Oh/* s2dY9 */){
    return E(_Oe/* GHC.Int.$fEnumInt11 */);
  }else{
    var _Oi/* s2dYf */ = hs_plusInt64/* EXTERNAL */(_Og/* s2dY7 */, new Long/* EXTERNAL */(1, 0));
    return E(_Oi/* s2dYf */);
  }
},
_Oj/* $fEnumInt64_$csucc */ = function(_Ok/* s2dYi */){
  return new F(function(){return _Of/* GHC.Int.$w$csucc */(E(_Ok/* s2dYi */));});
},
_Ol/* $fEnumInt64_$ctoEnum */ = function(_Om/* s2dXL */){
  return new F(function(){return hs_intToInt64/* EXTERNAL */(E(_Om/* s2dXL */));});
},
_On/* $fEnumInt64 */ = new T(function(){
  return {_:0,a:_Oj/* GHC.Int.$fEnumInt64_$csucc */,b:_O8/* GHC.Int.$fEnumInt64_$cpred */,c:_Ol/* GHC.Int.$fEnumInt64_$ctoEnum */,d:_NW/* GHC.Int.$fEnumInt64_$cfromEnum */,e:_Lb/* GHC.Int.$fEnumInt64_$cenumFrom */,f:_Mb/* GHC.Int.$fEnumInt64_$cenumFromThen */,g:_Mw/* GHC.Int.$fEnumInt64_$cenumFromTo */,h:_Mn/* GHC.Int.$fEnumInt64_$cenumFromThenTo */};
}),
_Oo/* minusInt64# */ = function(_Op/* sdC */, _Oq/* sdD */){
  var _Or/* sdF */ = hs_minusInt64/* EXTERNAL */(_Op/* sdC */, _Oq/* sdD */);
  return E(_Or/* sdF */);
},
_Os/* quotInt64# */ = function(_Ot/* sdk */, _Ou/* sdl */){
  var _Ov/* sdn */ = hs_quotInt64/* EXTERNAL */(_Ot/* sdk */, _Ou/* sdl */);
  return E(_Ov/* sdn */);
},
_Ow/* divInt64# */ = function(_Ox/* s2dwk */, _Oy/* s2dwl */){
  var _Oz/* s2dwn */ = hs_intToInt64/* EXTERNAL */(1),
  _OA/* s2dwp */ = _Oz/* s2dwn */,
  _OB/* s2dwr */ = hs_intToInt64/* EXTERNAL */(0),
  _OC/* s2dwt */ = _OB/* s2dwr */,
  _OD/* s2dwv */ = hs_gtInt64/* EXTERNAL */(_Ox/* s2dwk */, _OC/* s2dwt */),
  _OE/* s2dwy */ = function(_OF/* s2dwz */){
    var _OG/* s2dwB */ = hs_ltInt64/* EXTERNAL */(_Ox/* s2dwk */, _OC/* s2dwt */);
    if(!_OG/* s2dwB */){
      return new F(function(){return _Os/* GHC.IntWord64.quotInt64# */(_Ox/* s2dwk */, _Oy/* s2dwl */);});
    }else{
      var _OH/* s2dwG */ = hs_gtInt64/* EXTERNAL */(_Oy/* s2dwl */, _OC/* s2dwt */);
      if(!_OH/* s2dwG */){
        return new F(function(){return _Os/* GHC.IntWord64.quotInt64# */(_Ox/* s2dwk */, _Oy/* s2dwl */);});
      }else{
        var _OI/* s2dwL */ = hs_plusInt64/* EXTERNAL */(_Ox/* s2dwk */, _OA/* s2dwp */),
        _OJ/* s2dwP */ = hs_quotInt64/* EXTERNAL */(_OI/* s2dwL */, _Oy/* s2dwl */);
        return new F(function(){return _Oo/* GHC.IntWord64.minusInt64# */(_OJ/* s2dwP */, _OA/* s2dwp */);});
      }
    }
  };
  if(!_OD/* s2dwv */){
    return new F(function(){return _OE/* s2dwy */(_/* EXTERNAL */);});
  }else{
    var _OK/* s2dwU */ = hs_ltInt64/* EXTERNAL */(_Oy/* s2dwl */, _OC/* s2dwt */);
    if(!_OK/* s2dwU */){
      return new F(function(){return _OE/* s2dwy */(_/* EXTERNAL */);});
    }else{
      var _OL/* s2dwZ */ = hs_minusInt64/* EXTERNAL */(_Ox/* s2dwk */, _OA/* s2dwp */),
      _OM/* s2dx3 */ = hs_quotInt64/* EXTERNAL */(_OL/* s2dwZ */, _Oy/* s2dwl */);
      return new F(function(){return _Oo/* GHC.IntWord64.minusInt64# */(_OM/* s2dx3 */, _OA/* s2dwp */);});
    }
  }
},
_ON/* $fExceptionArithException_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_OO/* $fExceptionArithException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.Exception"));
}),
_OP/* $fExceptionArithException_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ArithException"));
}),
_OQ/* $fExceptionArithException_wild */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_ON/* GHC.Exception.$fExceptionArithException_ww2 */,_OO/* GHC.Exception.$fExceptionArithException_ww4 */,_OP/* GHC.Exception.$fExceptionArithException_ww5 */),
_OR/* $fExceptionArithException8 */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_OQ/* GHC.Exception.$fExceptionArithException_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_OS/* $fExceptionArithException7 */ = function(_OT/* s2S2z */){
  return E(_OR/* GHC.Exception.$fExceptionArithException8 */);
},
_OU/* $fExceptionArithException_$cfromException */ = function(_OV/* s2S35 */){
  var _OW/* s2S36 */ = E(_OV/* s2S35 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_OW/* s2S36 */.a)), _OS/* GHC.Exception.$fExceptionArithException7 */, _OW/* s2S36 */.b);});
},
_OX/* $fExceptionArithException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ratio has zero denominator"));
}),
_OY/* $fExceptionArithException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("denormal"));
}),
_OZ/* $fExceptionArithException3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("divide by zero"));
}),
_P0/* $fExceptionArithException4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("loss of precision"));
}),
_P1/* $fExceptionArithException5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic underflow"));
}),
_P2/* $fExceptionArithException6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic overflow"));
}),
_P3/* $w$cshowsPrec */ = function(_P4/* s2S3a */, _P5/* s2S3b */){
  switch(E(_P4/* s2S3a */)){
    case 0:
      return new F(function(){return _2/* GHC.Base.++ */(_P2/* GHC.Exception.$fExceptionArithException6 */, _P5/* s2S3b */);});
      break;
    case 1:
      return new F(function(){return _2/* GHC.Base.++ */(_P1/* GHC.Exception.$fExceptionArithException5 */, _P5/* s2S3b */);});
      break;
    case 2:
      return new F(function(){return _2/* GHC.Base.++ */(_P0/* GHC.Exception.$fExceptionArithException4 */, _P5/* s2S3b */);});
      break;
    case 3:
      return new F(function(){return _2/* GHC.Base.++ */(_OZ/* GHC.Exception.$fExceptionArithException3 */, _P5/* s2S3b */);});
      break;
    case 4:
      return new F(function(){return _2/* GHC.Base.++ */(_OY/* GHC.Exception.$fExceptionArithException2 */, _P5/* s2S3b */);});
      break;
    default:
      return new F(function(){return _2/* GHC.Base.++ */(_OX/* GHC.Exception.$fExceptionArithException1 */, _P5/* s2S3b */);});
  }
},
_P6/* $fExceptionArithException_$cshow */ = function(_P7/* s2S3g */){
  return new F(function(){return _P3/* GHC.Exception.$w$cshowsPrec */(_P7/* s2S3g */, _6/* GHC.Types.[] */);});
},
_P8/* $fExceptionArithException_$cshowsPrec */ = function(_P9/* s2S3d */, _Pa/* s2S3e */, _Pb/* s2S3f */){
  return new F(function(){return _P3/* GHC.Exception.$w$cshowsPrec */(_Pa/* s2S3e */, _Pb/* s2S3f */);});
},
_Pc/* $fShowArithException_$cshowList */ = function(_Pd/* s2S3h */, _Pe/* s2S3i */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_P3/* GHC.Exception.$w$cshowsPrec */, _Pd/* s2S3h */, _Pe/* s2S3i */);});
},
_Pf/* $fShowArithException */ = new T3(0,_P8/* GHC.Exception.$fExceptionArithException_$cshowsPrec */,_P6/* GHC.Exception.$fExceptionArithException_$cshow */,_Pc/* GHC.Exception.$fShowArithException_$cshowList */),
_Pg/* $fExceptionArithException */ = new T(function(){
  return new T5(0,_OS/* GHC.Exception.$fExceptionArithException7 */,_Pf/* GHC.Exception.$fShowArithException */,_Ph/* GHC.Exception.$fExceptionArithException_$ctoException */,_OU/* GHC.Exception.$fExceptionArithException_$cfromException */,_P6/* GHC.Exception.$fExceptionArithException_$cshow */);
}),
_Ph/* $fExceptionArithException_$ctoException */ = function(_Pi/* B1 */){
  return new T2(0,_Pg/* GHC.Exception.$fExceptionArithException */,_Pi/* B1 */);
},
_Pj/* DivideByZero */ = 3,
_Pk/* divZeroException */ = new T(function(){
  return B(_Ph/* GHC.Exception.$fExceptionArithException_$ctoException */(_Pj/* GHC.Exception.DivideByZero */));
}),
_Pl/* divZeroError */ = new T(function(){
  return die/* EXTERNAL */(_Pk/* GHC.Exception.divZeroException */);
}),
_Pm/* Overflow */ = 0,
_Pn/* overflowException */ = new T(function(){
  return B(_Ph/* GHC.Exception.$fExceptionArithException_$ctoException */(_Pm/* GHC.Exception.Overflow */));
}),
_Po/* overflowError */ = new T(function(){
  return die/* EXTERNAL */(_Pn/* GHC.Exception.overflowException */);
}),
_Pp/* $w$cdiv2 */ = function(_Pq/* s2e0N */, _Pr/* s2e0O */){
  var _Ps/* s2e0Q */ = hs_eqInt64/* EXTERNAL */(_Pr/* s2e0O */, new Long/* EXTERNAL */(0, 0));
  if(!_Ps/* s2e0Q */){
    var _Pt/* s2e0V */ = hs_eqInt64/* EXTERNAL */(_Pr/* s2e0O */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Pt/* s2e0V */){
      return new F(function(){return _Ow/* GHC.Int.divInt64# */(_Pq/* s2e0N */, _Pr/* s2e0O */);});
    }else{
      var _Pu/* s2e10 */ = hs_eqInt64/* EXTERNAL */(_Pq/* s2e0N */, new Long/* EXTERNAL */(0, -2147483648));
      if(!_Pu/* s2e10 */){
        return new F(function(){return _Ow/* GHC.Int.divInt64# */(_Pq/* s2e0N */, _Pr/* s2e0O */);});
      }else{
        return E(_Po/* GHC.Real.overflowError */);
      }
    }
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_Pv/* $fIntegralInt64_$cdiv */ = function(_Pw/* s2e16 */, _Px/* s2e17 */){
  return new F(function(){return _Pp/* GHC.Int.$w$cdiv2 */(E(_Pw/* s2e16 */), E(_Px/* s2e17 */));});
},
_Py/* $fIntegralInt1 */ = new Long/* EXTERNAL */(0, 0),
_Pz/* plusInt64# */ = function(_PA/* sdw */, _PB/* sdx */){
  var _PC/* sdz */ = hs_plusInt64/* EXTERNAL */(_PA/* sdw */, _PB/* sdx */);
  return E(_PC/* sdz */);
},
_PD/* modInt64# */ = function(_PE/* s2dvH */, _PF/* s2dvI */){
  var _PG/* s2dvK */ = hs_remInt64/* EXTERNAL */(_PE/* s2dvH */, _PF/* s2dvI */),
  _PH/* s2dvM */ = _PG/* s2dvK */,
  _PI/* s2dvO */ = hs_intToInt64/* EXTERNAL */(0),
  _PJ/* s2dvQ */ = _PI/* s2dvO */,
  _PK/* s2dvS */ = hs_gtInt64/* EXTERNAL */(_PE/* s2dvH */, _PJ/* s2dvQ */),
  _PL/* s2dvV */ = function(_PM/* s2dvW */){
    var _PN/* s2dvY */ = hs_neInt64/* EXTERNAL */(_PH/* s2dvM */, _PJ/* s2dvQ */);
    if(!_PN/* s2dvY */){
      return E(_PJ/* s2dvQ */);
    }else{
      return new F(function(){return _Pz/* GHC.IntWord64.plusInt64# */(_PH/* s2dvM */, _PF/* s2dvI */);});
    }
  },
  _PO/* s2dw2 */ = function(_PP/* s2dw3 */){
    var _PQ/* s2dw5 */ = hs_ltInt64/* EXTERNAL */(_PE/* s2dvH */, _PJ/* s2dvQ */);
    if(!_PQ/* s2dw5 */){
      return E(_PH/* s2dvM */);
    }else{
      var _PR/* s2dwa */ = hs_gtInt64/* EXTERNAL */(_PF/* s2dvI */, _PJ/* s2dvQ */);
      if(!_PR/* s2dwa */){
        return E(_PH/* s2dvM */);
      }else{
        return new F(function(){return _PL/* s2dvV */(_/* EXTERNAL */);});
      }
    }
  };
  if(!_PK/* s2dvS */){
    return new F(function(){return _PO/* s2dw2 */(_/* EXTERNAL */);});
  }else{
    var _PS/* s2dwg */ = hs_ltInt64/* EXTERNAL */(_PF/* s2dvI */, _PJ/* s2dvQ */);
    if(!_PS/* s2dwg */){
      return new F(function(){return _PO/* s2dw2 */(_/* EXTERNAL */);});
    }else{
      return new F(function(){return _PL/* s2dvV */(_/* EXTERNAL */);});
    }
  }
},
_PT/* $w$cdivMod2 */ = function(_PU/* s2dZ9 */, _PV/* s2dZa */){
  var _PW/* s2dZc */ = hs_eqInt64/* EXTERNAL */(_PV/* s2dZa */, new Long/* EXTERNAL */(0, 0));
  if(!_PW/* s2dZc */){
    var _PX/* s2dZh */ = hs_eqInt64/* EXTERNAL */(_PV/* s2dZa */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_PX/* s2dZh */){
      return new T2(0,new T(function(){
        return B(_Ow/* GHC.Int.divInt64# */(_PU/* s2dZ9 */, _PV/* s2dZa */));
      }),new T(function(){
        return B(_PD/* GHC.Int.modInt64# */(_PU/* s2dZ9 */, _PV/* s2dZa */));
      }));
    }else{
      var _PY/* s2dZq */ = hs_eqInt64/* EXTERNAL */(_PU/* s2dZ9 */, new Long/* EXTERNAL */(0, -2147483648));
      return (!_PY/* s2dZq */) ? new T2(0,new T(function(){
        return B(_Ow/* GHC.Int.divInt64# */(_PU/* s2dZ9 */, _PV/* s2dZa */));
      }),new T(function(){
        return B(_PD/* GHC.Int.modInt64# */(_PU/* s2dZ9 */, _PV/* s2dZa */));
      })) : new T2(0,_Po/* GHC.Real.overflowError */,_Py/* GHC.Int.$fIntegralInt1 */);
    }
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_PZ/* $fIntegralInt64_$cdivMod */ = function(_Q0/* s2dZz */, _Q1/* s2dZA */){
  var _Q2/* s2dZF */ = B(_PT/* GHC.Int.$w$cdivMod2 */(E(_Q0/* s2dZz */), E(_Q1/* s2dZA */)));
  return new T2(0,_Q2/* s2dZF */.a,_Q2/* s2dZF */.b);
},
_Q3/* $w$cmod */ = function(_Q4/* s2e0t */, _Q5/* s2e0u */){
  var _Q6/* s2e0w */ = hs_eqInt64/* EXTERNAL */(_Q5/* s2e0u */, new Long/* EXTERNAL */(0, 0));
  if(!_Q6/* s2e0w */){
    var _Q7/* s2e0B */ = hs_eqInt64/* EXTERNAL */(_Q5/* s2e0u */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Q7/* s2e0B */){
      return new F(function(){return _PD/* GHC.Int.modInt64# */(_Q4/* s2e0t */, _Q5/* s2e0u */);});
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_Q8/* $fIntegralInt64_$cmod */ = function(_Q9/* s2e0G */, _Qa/* s2e0H */){
  return new F(function(){return _Q3/* GHC.Int.$w$cmod */(E(_Q9/* s2e0G */), E(_Qa/* s2e0H */));});
},
_Qb/* $w$cquot */ = function(_Qc/* s2e1B */, _Qd/* s2e1C */){
  var _Qe/* s2e1E */ = hs_eqInt64/* EXTERNAL */(_Qd/* s2e1C */, new Long/* EXTERNAL */(0, 0));
  if(!_Qe/* s2e1E */){
    var _Qf/* s2e1J */ = hs_eqInt64/* EXTERNAL */(_Qd/* s2e1C */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Qf/* s2e1J */){
      var _Qg/* s2e1O */ = hs_quotInt64/* EXTERNAL */(_Qc/* s2e1B */, _Qd/* s2e1C */);
      return E(_Qg/* s2e1O */);
    }else{
      var _Qh/* s2e1S */ = hs_eqInt64/* EXTERNAL */(_Qc/* s2e1B */, new Long/* EXTERNAL */(0, -2147483648));
      if(!_Qh/* s2e1S */){
        var _Qi/* s2e1X */ = hs_quotInt64/* EXTERNAL */(_Qc/* s2e1B */, _Qd/* s2e1C */);
        return E(_Qi/* s2e1X */);
      }else{
        return E(_Po/* GHC.Real.overflowError */);
      }
    }
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_Qj/* $fIntegralInt64_$cquot */ = function(_Qk/* s2e22 */, _Ql/* s2e23 */){
  return new F(function(){return _Qb/* GHC.Int.$w$cquot */(E(_Qk/* s2e22 */), E(_Ql/* s2e23 */));});
},
_Qm/* $w$cquotRem */ = function(_Qn/* s2dZI */, _Qo/* s2dZJ */){
  var _Qp/* s2dZL */ = hs_eqInt64/* EXTERNAL */(_Qo/* s2dZJ */, new Long/* EXTERNAL */(0, 0));
  if(!_Qp/* s2dZL */){
    var _Qq/* s2dZQ */ = hs_eqInt64/* EXTERNAL */(_Qo/* s2dZJ */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Qq/* s2dZQ */){
      return new T2(0,new T(function(){
        return hs_quotInt64/* EXTERNAL */(_Qn/* s2dZI */, _Qo/* s2dZJ */);
      }),new T(function(){
        return hs_remInt64/* EXTERNAL */(_Qn/* s2dZI */, _Qo/* s2dZJ */);
      }));
    }else{
      var _Qr/* s2e05 */ = hs_eqInt64/* EXTERNAL */(_Qn/* s2dZI */, new Long/* EXTERNAL */(0, -2147483648));
      return (!_Qr/* s2e05 */) ? new T2(0,new T(function(){
        return hs_quotInt64/* EXTERNAL */(_Qn/* s2dZI */, _Qo/* s2dZJ */);
      }),new T(function(){
        return hs_remInt64/* EXTERNAL */(_Qn/* s2dZI */, _Qo/* s2dZJ */);
      })) : new T2(0,_Po/* GHC.Real.overflowError */,_Py/* GHC.Int.$fIntegralInt1 */);
    }
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_Qs/* $fIntegralInt64_$cquotRem */ = function(_Qt/* s2e0k */, _Qu/* s2e0l */){
  var _Qv/* s2e0q */ = B(_Qm/* GHC.Int.$w$cquotRem */(E(_Qt/* s2e0k */), E(_Qu/* s2e0l */)));
  return new T2(0,_Qv/* s2e0q */.a,_Qv/* s2e0q */.b);
},
_Qw/* $w$crem */ = function(_Qx/* s2e1d */, _Qy/* s2e1e */){
  var _Qz/* s2e1g */ = hs_eqInt64/* EXTERNAL */(_Qy/* s2e1e */, new Long/* EXTERNAL */(0, 0));
  if(!_Qz/* s2e1g */){
    var _QA/* s2e1l */ = hs_eqInt64/* EXTERNAL */(_Qy/* s2e1e */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_QA/* s2e1l */){
      var _QB/* s2e1q */ = hs_remInt64/* EXTERNAL */(_Qx/* s2e1d */, _Qy/* s2e1e */);
      return E(_QB/* s2e1q */);
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_QC/* $fIntegralInt64_$crem */ = function(_QD/* s2e1u */, _QE/* s2e1v */){
  return new F(function(){return _Qw/* GHC.Int.$w$crem */(E(_QD/* s2e1u */), E(_QE/* s2e1v */));});
},
_QF/* $fBitsInt64_$c/= */ = function(_QG/* s2dV3 */, _QH/* s2dV4 */){
  return new F(function(){return hs_neInt64/* EXTERNAL */(E(_QG/* s2dV3 */), E(_QH/* s2dV4 */));});
},
_QI/* $fEqInt64_$c== */ = function(_QJ/* s2dVd */, _QK/* s2dVe */){
  return new F(function(){return hs_eqInt64/* EXTERNAL */(E(_QJ/* s2dVd */), E(_QK/* s2dVe */));});
},
_QL/* $fEqInt64 */ = new T2(0,_QI/* GHC.Int.$fEqInt64_$c== */,_QF/* GHC.Int.$fBitsInt64_$c/= */),
_QM/* $fOrdInt64_$c< */ = function(_QN/* s2dWd */, _QO/* s2dWe */){
  return new F(function(){return hs_ltInt64/* EXTERNAL */(E(_QN/* s2dWd */), E(_QO/* s2dWe */));});
},
_QP/* $fOrdInt64_$c<= */ = function(_QQ/* s2dW3 */, _QR/* s2dW4 */){
  return new F(function(){return hs_leInt64/* EXTERNAL */(E(_QQ/* s2dW3 */), E(_QR/* s2dW4 */));});
},
_QS/* $fOrdInt64_$c> */ = function(_QT/* s2dVT */, _QU/* s2dVU */){
  return new F(function(){return hs_gtInt64/* EXTERNAL */(E(_QT/* s2dVT */), E(_QU/* s2dVU */));});
},
_QV/* $fOrdInt64_$c>= */ = function(_QW/* s2dVJ */, _QX/* s2dVK */){
  return new F(function(){return hs_geInt64/* EXTERNAL */(E(_QW/* s2dVJ */), E(_QX/* s2dVK */));});
},
_QY/* $w$ccompare */ = function(_QZ/* s2dWn */, _R0/* s2dWo */){
  var _R1/* s2dWq */ = hs_eqInt64/* EXTERNAL */(_QZ/* s2dWn */, _R0/* s2dWo */);
  if(!_R1/* s2dWq */){
    var _R2/* s2dWv */ = hs_leInt64/* EXTERNAL */(_QZ/* s2dWn */, _R0/* s2dWo */);
    return (!_R2/* s2dWv */) ? 2 : 0;
  }else{
    return 1;
  }
},
_R3/* $fOrdInt64_$ccompare */ = function(_R4/* s2dWz */, _R5/* s2dWA */){
  return new F(function(){return _QY/* GHC.Int.$w$ccompare */(E(_R4/* s2dWz */), E(_R5/* s2dWA */));});
},
_R6/* $fOrdInt64_$cmax */ = function(_R7/* s2dVy */, _R8/* s2dVz */){
  var _R9/* s2dVA */ = E(_R7/* s2dVy */),
  _Ra/* s2dVC */ = E(_R8/* s2dVz */),
  _Rb/* s2dVF */ = hs_leInt64/* EXTERNAL */(_R9/* s2dVA */, _Ra/* s2dVC */);
  return (!_Rb/* s2dVF */) ? E(_R9/* s2dVA */) : E(_Ra/* s2dVC */);
},
_Rc/* $fOrdInt64_$cmin */ = function(_Rd/* s2dVn */, _Re/* s2dVo */){
  var _Rf/* s2dVp */ = E(_Rd/* s2dVn */),
  _Rg/* s2dVr */ = E(_Re/* s2dVo */),
  _Rh/* s2dVu */ = hs_leInt64/* EXTERNAL */(_Rf/* s2dVp */, _Rg/* s2dVr */);
  return (!_Rh/* s2dVu */) ? E(_Rg/* s2dVr */) : E(_Rf/* s2dVp */);
},
_Ri/* $fOrdInt64 */ = {_:0,a:_QL/* GHC.Int.$fEqInt64 */,b:_R3/* GHC.Int.$fOrdInt64_$ccompare */,c:_QM/* GHC.Int.$fOrdInt64_$c< */,d:_QP/* GHC.Int.$fOrdInt64_$c<= */,e:_QS/* GHC.Int.$fOrdInt64_$c> */,f:_QV/* GHC.Int.$fOrdInt64_$c>= */,g:_R6/* GHC.Int.$fOrdInt64_$cmax */,h:_Rc/* GHC.Int.$fOrdInt64_$cmin */},
_Rj/* $fRealInt1 */ = new T1(0,1),
_Rk/* eqInteger */ = function(_Rl/* s1H2 */, _Rm/* s1H3 */){
  var _Rn/* s1H4 */ = E(_Rl/* s1H2 */);
  if(!_Rn/* s1H4 */._){
    var _Ro/* s1H5 */ = _Rn/* s1H4 */.a,
    _Rp/* s1H6 */ = E(_Rm/* s1H3 */);
    return (_Rp/* s1H6 */._==0) ? _Ro/* s1H5 */==_Rp/* s1H6 */.a : (I_compareInt/* EXTERNAL */(_Rp/* s1H6 */.a, _Ro/* s1H5 */)==0) ? true : false;
  }else{
    var _Rq/* s1Hc */ = _Rn/* s1H4 */.a,
    _Rr/* s1Hd */ = E(_Rm/* s1H3 */);
    return (_Rr/* s1Hd */._==0) ? (I_compareInt/* EXTERNAL */(_Rq/* s1Hc */, _Rr/* s1Hd */.a)==0) ? true : false : (I_compare/* EXTERNAL */(_Rq/* s1Hc */, _Rr/* s1Hd */.a)==0) ? true : false;
  }
},
_Rs/* even1 */ = new T1(0,0),
_Rt/* remInteger */ = function(_Ru/* s1NY */, _Rv/* s1NZ */){
  while(1){
    var _Rw/* s1O0 */ = E(_Ru/* s1NY */);
    if(!_Rw/* s1O0 */._){
      var _Rx/* s1O2 */ = E(_Rw/* s1O0 */.a);
      if(_Rx/* s1O2 */==(-2147483648)){
        _Ru/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _Ry/* s1O3 */ = E(_Rv/* s1NZ */);
        if(!_Ry/* s1O3 */._){
          return new T1(0,_Rx/* s1O2 */%_Ry/* s1O3 */.a);
        }else{
          _Ru/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(_Rx/* s1O2 */));
          _Rv/* s1NZ */ = _Ry/* s1O3 */;
          continue;
        }
      }
    }else{
      var _Rz/* s1Od */ = _Rw/* s1O0 */.a,
      _RA/* s1Oe */ = E(_Rv/* s1NZ */);
      return (_RA/* s1Oe */._==0) ? new T1(1,I_rem/* EXTERNAL */(_Rz/* s1Od */, I_fromInt/* EXTERNAL */(_RA/* s1Oe */.a))) : new T1(1,I_rem/* EXTERNAL */(_Rz/* s1Od */, _RA/* s1Oe */.a));
    }
  }
},
_RB/* $fIntegralInteger_$crem */ = function(_RC/* svus */, _RD/* svut */){
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_RD/* svut */, _Rs/* GHC.Real.even1 */))){
    return new F(function(){return _Rt/* GHC.Integer.Type.remInteger */(_RC/* svus */, _RD/* svut */);});
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_RE/* $fEnumRatio_gcd' */ = function(_RF/* svuv */, _RG/* svuw */){
  while(1){
    if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_RG/* svuw */, _Rs/* GHC.Real.even1 */))){
      var _RH/*  svuv */ = _RG/* svuw */,
      _RI/*  svuw */ = B(_RB/* GHC.Real.$fIntegralInteger_$crem */(_RF/* svuv */, _RG/* svuw */));
      _RF/* svuv */ = _RH/*  svuv */;
      _RG/* svuw */ = _RI/*  svuw */;
      continue;
    }else{
      return E(_RF/* svuv */);
    }
  }
},
_RJ/* absInteger */ = function(_RK/* s1QP */){
  var _RL/* s1QQ */ = E(_RK/* s1QP */);
  if(!_RL/* s1QQ */._){
    var _RM/* s1QS */ = E(_RL/* s1QQ */.a);
    return (_RM/* s1QS */==(-2147483648)) ? E(_Kh/* GHC.Integer.Type.lvl3 */) : (_RM/* s1QS */<0) ? new T1(0, -_RM/* s1QS */) : E(_RL/* s1QQ */);
  }else{
    var _RN/* s1QW */ = _RL/* s1QQ */.a;
    return (I_compareInt/* EXTERNAL */(_RN/* s1QW */, 0)>=0) ? E(_RL/* s1QQ */) : new T1(1,I_negate/* EXTERNAL */(_RN/* s1QW */));
  }
},
_RO/* quotInteger */ = function(_RP/* s1On */, _RQ/* s1Oo */){
  while(1){
    var _RR/* s1Op */ = E(_RP/* s1On */);
    if(!_RR/* s1Op */._){
      var _RS/* s1Or */ = E(_RR/* s1Op */.a);
      if(_RS/* s1Or */==(-2147483648)){
        _RP/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _RT/* s1Os */ = E(_RQ/* s1Oo */);
        if(!_RT/* s1Os */._){
          return new T1(0,quot/* EXTERNAL */(_RS/* s1Or */, _RT/* s1Os */.a));
        }else{
          _RP/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(_RS/* s1Or */));
          _RQ/* s1Oo */ = _RT/* s1Os */;
          continue;
        }
      }
    }else{
      var _RU/* s1OC */ = _RR/* s1Op */.a,
      _RV/* s1OD */ = E(_RQ/* s1Oo */);
      return (_RV/* s1OD */._==0) ? new T1(0,I_toInt/* EXTERNAL */(I_quot/* EXTERNAL */(_RU/* s1OC */, I_fromInt/* EXTERNAL */(_RV/* s1OD */.a)))) : new T1(1,I_quot/* EXTERNAL */(_RU/* s1OC */, _RV/* s1OD */.a));
    }
  }
},
_RW/* RatioZeroDenominator */ = 5,
_RX/* ratioZeroDenomException */ = new T(function(){
  return B(_Ph/* GHC.Exception.$fExceptionArithException_$ctoException */(_RW/* GHC.Exception.RatioZeroDenominator */));
}),
_RY/* ratioZeroDenominatorError */ = new T(function(){
  return die/* EXTERNAL */(_RX/* GHC.Exception.ratioZeroDenomException */);
}),
_RZ/* $w$sreduce */ = function(_S0/* svvD */, _S1/* svvE */){
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_S1/* svvE */, _Rs/* GHC.Real.even1 */))){
    var _S2/* svvG */ = B(_RE/* GHC.Real.$fEnumRatio_gcd' */(B(_RJ/* GHC.Integer.Type.absInteger */(_S0/* svvD */)), B(_RJ/* GHC.Integer.Type.absInteger */(_S1/* svvE */))));
    return (!B(_Rk/* GHC.Integer.Type.eqInteger */(_S2/* svvG */, _Rs/* GHC.Real.even1 */))) ? new T2(0,B(_RO/* GHC.Integer.Type.quotInteger */(_S0/* svvD */, _S2/* svvG */)),B(_RO/* GHC.Integer.Type.quotInteger */(_S1/* svvE */, _S2/* svvG */))) : E(_Pl/* GHC.Real.divZeroError */);
  }else{
    return E(_RY/* GHC.Real.ratioZeroDenominatorError */);
  }
},
_S3/* timesInteger */ = function(_S4/* s1PN */, _S5/* s1PO */){
  while(1){
    var _S6/* s1PP */ = E(_S4/* s1PN */);
    if(!_S6/* s1PP */._){
      var _S7/* s1PQ */ = _S6/* s1PP */.a,
      _S8/* s1PR */ = E(_S5/* s1PO */);
      if(!_S8/* s1PR */._){
        var _S9/* s1PS */ = _S8/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_S7/* s1PQ */, _S9/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_S7/* s1PQ */, _S9/* s1PS */)|0);
        }else{
          _S4/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_S7/* s1PQ */));
          _S5/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_S9/* s1PS */));
          continue;
        }
      }else{
        _S4/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_S7/* s1PQ */));
        _S5/* s1PO */ = _S8/* s1PR */;
        continue;
      }
    }else{
      var _Sa/* s1Q6 */ = E(_S5/* s1PO */);
      if(!_Sa/* s1Q6 */._){
        _S4/* s1PN */ = _S6/* s1PP */;
        _S5/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Sa/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_S6/* s1PP */.a, _Sa/* s1Q6 */.a));
      }
    }
  }
},
_Sb/* $fRealInt64_$ctoRational */ = function(_Sc/* s2e6O */){
  var _Sd/* s2e6T */ = B(_RZ/* GHC.Real.$w$sreduce */(B(_S3/* GHC.Integer.Type.timesInteger */(B(_MA/* GHC.Integer.Type.int64ToInteger */(E(_Sc/* s2e6O */))), _Rj/* GHC.Int.$fRealInt1 */)), _Rj/* GHC.Int.$fRealInt1 */));
  return new T2(0,E(_Sd/* s2e6T */.a),E(_Sd/* s2e6T */.b));
},
_Se/* $fRealInt64 */ = new T3(0,_JQ/* GHC.Int.$fNumInt64 */,_Ri/* GHC.Int.$fOrdInt64 */,_Sb/* GHC.Int.$fRealInt64_$ctoRational */),
_Ld/* $fIntegralInt64 */ = new T(function(){
  return {_:0,a:_Se/* GHC.Int.$fRealInt64 */,b:_On/* GHC.Int.$fEnumInt64 */,c:_Qj/* GHC.Int.$fIntegralInt64_$cquot */,d:_QC/* GHC.Int.$fIntegralInt64_$crem */,e:_Pv/* GHC.Int.$fIntegralInt64_$cdiv */,f:_Q8/* GHC.Int.$fIntegralInt64_$cmod */,g:_Qs/* GHC.Int.$fIntegralInt64_$cquotRem */,h:_PZ/* GHC.Int.$fIntegralInt64_$cdivMod */,i:_MH/* GHC.Int.$fIntegralInt64_$ctoInteger */};
}),
_Sf/* $p1Ord */ = function(_Sg/* scBR */){
  return E(E(_Sg/* scBR */).a);
},
_Sh/* $p2Real */ = function(_Si/* svfR */){
  return E(E(_Si/* svfR */).b);
},
_Sj/* == */ = function(_Sk/* scBJ */){
  return E(E(_Sk/* scBJ */).a);
},
_Sl/* even2 */ = new T1(0,2),
_Sm/* rem */ = function(_Sn/* sveI */){
  return E(E(_Sn/* sveI */).d);
},
_So/* even */ = function(_Sp/* svre */, _Sq/* svrf */){
  var _Sr/* svrg */ = B(_KL/* GHC.Real.$p1Integral */(_Sp/* svre */)),
  _Ss/* svrh */ = new T(function(){
    return B(_KN/* GHC.Real.$p1Real */(_Sr/* svrg */));
  }),
  _St/* svrl */ = new T(function(){
    return B(A3(_Sm/* GHC.Real.rem */,_Sp/* svre */, _Sq/* svrf */, new T(function(){
      return B(A2(_KP/* GHC.Num.fromInteger */,_Ss/* svrh */, _Sl/* GHC.Real.even2 */));
    })));
  });
  return new F(function(){return A3(_Sj/* GHC.Classes.== */,B(_Sf/* GHC.Classes.$p1Ord */(B(_Sh/* GHC.Real.$p2Real */(_Sr/* svrg */)))), _St/* svrl */, new T(function(){
    return B(A2(_KP/* GHC.Num.fromInteger */,_Ss/* svrh */, _Rs/* GHC.Real.even1 */));
  }));});
},
_Su/* $wg1 */ = function(_Sv/*  sfnl */, _Sw/*  sfnm */, _Sx/*  sfnn */){
  while(1){
    var _Sy/*  $wg1 */ = B((function(_Sz/* sfnl */, _SA/* sfnm */, _SB/* sfnn */){
      if(!B(_So/* GHC.Real.even */(_Ld/* GHC.Int.$fIntegralInt64 */, _SA/* sfnm */))){
        var _SC/* sfnr */ = hs_eqInt64/* EXTERNAL */(_SA/* sfnm */, new Long/* EXTERNAL */(1, 0));
        if(!_SC/* sfnr */){
          var _SD/* sfnw */ = hs_minusInt64/* EXTERNAL */(_SA/* sfnm */, new Long/* EXTERNAL */(1, 0));
          _Sv/*  sfnl */ = new T(function(){
            return B(_Jt/* GHC.Int.$fNumInt64_$c* */(_Sz/* sfnl */, _Sz/* sfnl */));
          });
          _Sw/*  sfnm */ = B(_Qb/* GHC.Int.$w$cquot */(_SD/* sfnw */, new Long/* EXTERNAL */(2, 0)));
          _Sx/*  sfnn */ = new T(function(){
            return B(_Jt/* GHC.Int.$fNumInt64_$c* */(_Sz/* sfnl */, _SB/* sfnn */));
          },1);
          return __continue/* EXTERNAL */;
        }else{
          var _SE/* sfnH */ = hs_timesInt64/* EXTERNAL */(E(_Sz/* sfnl */), E(_SB/* sfnn */));
          return E(_SE/* sfnH */);
        }
      }else{
        var _SF/*   sfnm */ = B(_Qb/* GHC.Int.$w$cquot */(_SA/* sfnm */, new Long/* EXTERNAL */(2, 0))),
        _SG/*   sfnn */ = _SB/* sfnn */;
        _Sv/*  sfnl */ = new T(function(){
          return B(_Jt/* GHC.Int.$fNumInt64_$c* */(_Sz/* sfnl */, _Sz/* sfnl */));
        });
        _Sw/*  sfnm */ = _SF/*   sfnm */;
        _Sx/*  sfnn */ = _SG/*   sfnn */;
        return __continue/* EXTERNAL */;
      }
    })(_Sv/*  sfnl */, _Sw/*  sfnm */, _Sx/*  sfnn */));
    if(_Sy/*  $wg1 */!=__continue/* EXTERNAL */){
      return _Sy/*  $wg1 */;
    }
  }
},
_SH/* $wf1 */ = function(_SI/*  sfnM */, _SJ/*  sfnN */){
  while(1){
    var _SK/*  $wf1 */ = B((function(_SL/* sfnM */, _SM/* sfnN */){
      if(!B(_So/* GHC.Real.even */(_Ld/* GHC.Int.$fIntegralInt64 */, _SM/* sfnN */))){
        var _SN/* sfnR */ = hs_eqInt64/* EXTERNAL */(_SM/* sfnN */, new Long/* EXTERNAL */(1, 0));
        if(!_SN/* sfnR */){
          var _SO/* sfnW */ = hs_minusInt64/* EXTERNAL */(_SM/* sfnN */, new Long/* EXTERNAL */(1, 0));
          return new F(function(){return _Su/* System.Random.$wg1 */(new T(function(){
            return B(_Jt/* GHC.Int.$fNumInt64_$c* */(_SL/* sfnM */, _SL/* sfnM */));
          }), B(_Qb/* GHC.Int.$w$cquot */(_SO/* sfnW */, new Long/* EXTERNAL */(2, 0))), _SL/* sfnM */);});
        }else{
          return E(_SL/* sfnM */);
        }
      }else{
        var _SP/*   sfnN */ = B(_Qb/* GHC.Int.$w$cquot */(_SM/* sfnN */, new Long/* EXTERNAL */(2, 0)));
        _SI/*  sfnM */ = new T(function(){
          return B(_Jt/* GHC.Int.$fNumInt64_$c* */(_SL/* sfnM */, _SL/* sfnM */));
        });
        _SJ/*  sfnN */ = _SP/*   sfnN */;
        return __continue/* EXTERNAL */;
      }
    })(_SI/*  sfnM */, _SJ/*  sfnN */));
    if(_SK/*  $wf1 */!=__continue/* EXTERNAL */){
      return _SK/*  $wf1 */;
    }
  }
},
_SQ/* $w$s^ */ = function(_SR/* sfoq */, _SS/* sfor */){
  var _ST/* sfot */ = hs_ltInt64/* EXTERNAL */(_SS/* sfor */, new Long/* EXTERNAL */(0, 0));
  if(!_ST/* sfot */){
    var _SU/* sfoy */ = hs_eqInt64/* EXTERNAL */(_SS/* sfor */, new Long/* EXTERNAL */(0, 0));
    if(!_SU/* sfoy */){
      return new F(function(){return _SH/* System.Random.$wf1 */(_SR/* sfoq */, _SS/* sfor */);});
    }else{
      return E(_KG/* System.Random.$fRandomDouble6 */);
    }
  }else{
    return E(_KF/* System.Random.$fRandomDouble5 */);
  }
},
_SV/* $fRandomDouble_twoto53 */ = new T(function(){
  return B(_SQ/* System.Random.$w$s^ */(_KD/* System.Random.$fRandomDouble4 */, new Long/* EXTERNAL */(53, 0)));
}),
_SW/* doubleFromInteger */ = function(_SX/* s1M0 */){
  var _SY/* s1M1 */ = E(_SX/* s1M0 */);
  if(!_SY/* s1M1 */._){
    return _SY/* s1M1 */.a;
  }else{
    return new F(function(){return I_toNumber/* EXTERNAL */(_SY/* s1M1 */.a);});
  }
},
_SZ/* $fRandomDouble3 */ = new T(function(){
  return B(_SW/* GHC.Integer.Type.doubleFromInteger */(B(_MA/* GHC.Integer.Type.int64ToInteger */(E(_SV/* System.Random.$fRandomDouble_twoto53 */)))));
}),
_T0/* $fRandomDouble7 */ = new T(function(){
  return hs_minusInt64/* EXTERNAL */(E(_SV/* System.Random.$fRandomDouble_twoto53 */), new Long/* EXTERNAL */(1, 0));
}),
_T1/* $w$c.&. */ = function(_T2/* s2e5n */, _T3/* s2e5o */){
  var _T4/* s2e5q */ = hs_int64ToWord64/* EXTERNAL */(_T3/* s2e5o */),
  _T5/* s2e5u */ = hs_int64ToWord64/* EXTERNAL */(_T2/* s2e5n */),
  _T6/* s2e5y */ = hs_and64/* EXTERNAL */(_T5/* s2e5u */, _T4/* s2e5q */),
  _T7/* s2e5C */ = hs_word64ToInt64/* EXTERNAL */(_T6/* s2e5y */);
  return E(_T7/* s2e5C */);
},
_T8/* $fRandomBool3 */ = new T1(0,1),
_T9/* $WStdGen */ = function(_Ta/* sfmR */, _Tb/* sfmS */){
  return new T2(0,E(_Ta/* sfmR */),E(_Tb/* sfmS */));
},
_Tc/* $w$cnext */ = function(_Td/* sfqJ */, _Te/* sfqK */){
  var _Tf/* sfqL */ = quot/* EXTERNAL */(_Te/* sfqK */, 52774),
  _Tg/* sfqM */ = (imul/* EXTERNAL */(40692, _Te/* sfqK */-(imul/* EXTERNAL */(_Tf/* sfqL */, 52774)|0)|0)|0)-(imul/* EXTERNAL */(_Tf/* sfqL */, 3791)|0)|0,
  _Th/* sfqR */ = new T(function(){
    if(_Tg/* sfqM */>=0){
      return _Tg/* sfqM */;
    }else{
      return _Tg/* sfqM */+2147483399|0;
    }
  }),
  _Ti/* sfqV */ = quot/* EXTERNAL */(_Td/* sfqJ */, 53668),
  _Tj/* sfqW */ = (imul/* EXTERNAL */(40014, _Td/* sfqJ */-(imul/* EXTERNAL */(_Ti/* sfqV */, 53668)|0)|0)|0)-(imul/* EXTERNAL */(_Ti/* sfqV */, 12211)|0)|0,
  _Tk/* sfr1 */ = new T(function(){
    if(_Tj/* sfqW */>=0){
      return _Tj/* sfqW */;
    }else{
      return _Tj/* sfqW */+2147483563|0;
    }
  });
  return new T2(0,new T(function(){
    var _Tl/* sfr9 */ = E(_Tk/* sfr1 */)-E(_Th/* sfqR */)|0;
    if(_Tl/* sfr9 */>=1){
      return _Tl/* sfr9 */;
    }else{
      return _Tl/* sfr9 */+2147483562|0;
    }
  }),new T(function(){
    return B(_T9/* System.Random.$WStdGen */(_Tk/* sfr1 */, _Th/* sfqR */));
  }));
},
_Tm/* b */ = new T1(0,2147483562),
_Tn/* getStdRandom4 */ = new T1(0,0),
_To/* lvl5 */ = new T1(0,1000),
_Tp/* modInt# */ = function(_Tq/* scEd */, _Tr/* scEe */){
  var _Ts/* scEf */ = _Tq/* scEd */%_Tr/* scEe */;
  if(_Tq/* scEd */<=0){
    if(_Tq/* scEd */>=0){
      return E(_Ts/* scEf */);
    }else{
      if(_Tr/* scEe */<=0){
        return E(_Ts/* scEf */);
      }else{
        var _Tt/* scEm */ = E(_Ts/* scEf */);
        return (_Tt/* scEm */==0) ? 0 : _Tt/* scEm */+_Tr/* scEe */|0;
      }
    }
  }else{
    if(_Tr/* scEe */>=0){
      if(_Tq/* scEd */>=0){
        return E(_Ts/* scEf */);
      }else{
        if(_Tr/* scEe */<=0){
          return E(_Ts/* scEf */);
        }else{
          var _Tu/* scEt */ = E(_Ts/* scEf */);
          return (_Tu/* scEt */==0) ? 0 : _Tu/* scEt */+_Tr/* scEe */|0;
        }
      }
    }else{
      var _Tv/* scEu */ = E(_Ts/* scEf */);
      return (_Tv/* scEu */==0) ? 0 : _Tv/* scEu */+_Tr/* scEe */|0;
    }
  }
},
_Tw/* modInteger */ = function(_Tx/* s1Na */, _Ty/* s1Nb */){
  while(1){
    var _Tz/* s1Nc */ = E(_Tx/* s1Na */);
    if(!_Tz/* s1Nc */._){
      var _TA/* s1Ne */ = E(_Tz/* s1Nc */.a);
      if(_TA/* s1Ne */==(-2147483648)){
        _Tx/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _TB/* s1Nf */ = E(_Ty/* s1Nb */);
        if(!_TB/* s1Nf */._){
          return new T1(0,B(_Tp/* GHC.Classes.modInt# */(_TA/* s1Ne */, _TB/* s1Nf */.a)));
        }else{
          _Tx/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(_TA/* s1Ne */));
          _Ty/* s1Nb */ = _TB/* s1Nf */;
          continue;
        }
      }
    }else{
      var _TC/* s1Np */ = _Tz/* s1Nc */.a,
      _TD/* s1Nq */ = E(_Ty/* s1Nb */);
      return (_TD/* s1Nq */._==0) ? new T1(1,I_mod/* EXTERNAL */(_TC/* s1Np */, I_fromInt/* EXTERNAL */(_TD/* s1Nq */.a))) : new T1(1,I_mod/* EXTERNAL */(_TC/* s1Np */, _TD/* s1Nq */.a));
    }
  }
},
_TE/* $w$srandomIvalInteger */ = function(_TF/*  sfs7 */, _TG/*  sfs8 */, _TH/*  sfs9 */, _TI/*  sfsa */){
  while(1){
    var _TJ/*  $w$srandomIvalInteger */ = B((function(_TK/* sfs7 */, _TL/* sfs8 */, _TM/* sfs9 */, _TN/* sfsa */){
      if(!B(_KR/* GHC.Integer.Type.gtInteger */(_TL/* sfs8 */, _TM/* sfs9 */))){
        var _TO/* sfsc */ = B(_K8/* GHC.Integer.Type.plusInteger */(B(_LN/* GHC.Integer.Type.minusInteger */(_TM/* sfs9 */, _TL/* sfs8 */)), _T8/* System.Random.$fRandomBool3 */)),
        _TP/* sfsf */ = function(_TQ/* sfsg */, _TR/* sfsh */, _TS/* sfsi */){
          while(1){
            if(!B(_Lf/* GHC.Integer.Type.geInteger */(_TQ/* sfsg */, B(_S3/* GHC.Integer.Type.timesInteger */(_TO/* sfsc */, _To/* System.Random.lvl5 */))))){
              var _TT/* sfsk */ = E(_TS/* sfsi */),
              _TU/* sfsn */ = B(_Tc/* System.Random.$w$cnext */(_TT/* sfsk */.a, _TT/* sfsk */.b)),
              _TV/*  sfsg */ = B(_S3/* GHC.Integer.Type.timesInteger */(_TQ/* sfsg */, _Tm/* System.Random.b */)),
              _TW/*  sfsh */ = B(_K8/* GHC.Integer.Type.plusInteger */(B(_S3/* GHC.Integer.Type.timesInteger */(_TR/* sfsh */, _Tm/* System.Random.b */)), B(_LN/* GHC.Integer.Type.minusInteger */(B(_My/* GHC.Integer.Type.smallInteger */(E(_TU/* sfsn */.a))), _T8/* System.Random.$fRandomBool3 */))));
              _TQ/* sfsg */ = _TV/*  sfsg */;
              _TR/* sfsh */ = _TW/*  sfsh */;
              _TS/* sfsi */ = _TU/* sfsn */.b;
              continue;
            }else{
              return new T2(0,_TR/* sfsh */,_TS/* sfsi */);
            }
          }
        },
        _TX/* sfsx */ = B(_TP/* sfsf */(_T8/* System.Random.$fRandomBool3 */, _Tn/* System.Random.getStdRandom4 */, _TN/* sfsa */)),
        _TY/* sfsE */ = new T(function(){
          return B(A2(_KP/* GHC.Num.fromInteger */,_TK/* sfs7 */, new T(function(){
            if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_TO/* sfsc */, _Tn/* System.Random.getStdRandom4 */))){
              return B(_K8/* GHC.Integer.Type.plusInteger */(_TL/* sfs8 */, B(_Tw/* GHC.Integer.Type.modInteger */(_TX/* sfsx */.a, _TO/* sfsc */))));
            }else{
              return E(_Pl/* GHC.Real.divZeroError */);
            }
          })));
        });
        return new T2(0,_TY/* sfsE */,_TX/* sfsx */.b);
      }else{
        var _TZ/*   sfs7 */ = _TK/* sfs7 */,
        _U0/*   sfs8 */ = _TM/* sfs9 */,
        _U1/*   sfs9 */ = _TL/* sfs8 */,
        _U2/*   sfsa */ = _TN/* sfsa */;
        _TF/*  sfs7 */ = _TZ/*   sfs7 */;
        _TG/*  sfs8 */ = _U0/*   sfs8 */;
        _TH/*  sfs9 */ = _U1/*   sfs9 */;
        _TI/*  sfsa */ = _U2/*   sfsa */;
        return __continue/* EXTERNAL */;
      }
    })(_TF/*  sfs7 */, _TG/*  sfs8 */, _TH/*  sfs9 */, _TI/*  sfsa */));
    if(_TJ/*  $w$srandomIvalInteger */!=__continue/* EXTERNAL */){
      return _TJ/*  $w$srandomIvalInteger */;
    }
  }
},
_U3/* $w$s$crandom */ = function(_U4/* sfSt */){
  var _U5/* sfSu */ = B(_TE/* System.Random.$w$srandomIvalInteger */(_JQ/* GHC.Int.$fNumInt64 */, _KC/* System.Random.$fRandomCLLong4 */, _Kv/* System.Random.$fRandomCLLong3 */, _U4/* sfSt */));
  return new T2(0,new T(function(){
    return B(_SW/* GHC.Integer.Type.doubleFromInteger */(B(_MA/* GHC.Integer.Type.int64ToInteger */(B(_T1/* GHC.Int.$w$c.&. */(E(_T0/* System.Random.$fRandomDouble7 */), E(_U5/* sfSu */.a)))))))/E(_SZ/* System.Random.$fRandomDouble3 */);
  }),_U5/* sfSu */.b);
},
_U6/* $w$srandomRFloating2 */ = function(_U7/*  sfSX */, _U8/*  sfSY */, _U9/*  sfSZ */){
  while(1){
    var _Ua/*  $w$srandomRFloating2 */ = B((function(_Ub/* sfSX */, _Uc/* sfSY */, _Ud/* sfSZ */){
      if(_Ub/* sfSX */<=_Uc/* sfSY */){
        var _Ue/* sfT2 */ = new T(function(){
          var _Uf/* sfT3 */ = B(_U3/* System.Random.$w$s$crandom */(_Ud/* sfSZ */));
          return new T2(0,_Uf/* sfT3 */.a,_Uf/* sfT3 */.b);
        });
        return new T2(0,new T(function(){
          var _Ug/* sfT9 */ = E(E(_Ue/* sfT2 */).a);
          return 0.5*_Ub/* sfSX */+_Ug/* sfT9 */*(0.5*_Uc/* sfSY */-0.5*_Ub/* sfSX */)+0.5*_Ub/* sfSX */+_Ug/* sfT9 */*(0.5*_Uc/* sfSY */-0.5*_Ub/* sfSX */);
        }),new T(function(){
          return E(E(_Ue/* sfT2 */).b);
        }));
      }else{
        var _Uh/*   sfSX */ = _Uc/* sfSY */,
        _Ui/*   sfSY */ = _Ub/* sfSX */,
        _Uj/*   sfSZ */ = _Ud/* sfSZ */;
        _U7/*  sfSX */ = _Uh/*   sfSX */;
        _U8/*  sfSY */ = _Ui/*   sfSY */;
        _U9/*  sfSZ */ = _Uj/*   sfSZ */;
        return __continue/* EXTERNAL */;
      }
    })(_U7/*  sfSX */, _U8/*  sfSY */, _U9/*  sfSZ */));
    if(_Ua/*  $w$srandomRFloating2 */!=__continue/* EXTERNAL */){
      return _Ua/*  $w$srandomRFloating2 */;
    }
  }
},
_Uk/* s6SwZ */ = 1420103680,
_Ul/* s6Sx0 */ = 465,
_Um/* s6Sx1 */ = new T2(1,_Ul/* s6Sx0 */,_6/* GHC.Types.[] */),
_Un/* s6Sx2 */ = new T2(1,_Uk/* s6SwZ */,_Um/* s6Sx1 */),
_Uo/* $fHasResolutionE5 */ = new T(function(){
  return B(_Km/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _Un/* s6Sx2 */));
}),
_Up/* $fBitsInt4 */ = 0,
_Uq/* $w$cdivMod1 */ = function(_Ur/* s2dPw */, _Us/* s2dPx */){
  var _Ut/* s2dPy */ = E(_Us/* s2dPx */);
  if(!_Ut/* s2dPy */){
    return E(_Pl/* GHC.Real.divZeroError */);
  }else{
    var _Uu/* s2dPz */ = function(_Uv/* s2dPA */){
      if(_Ur/* s2dPw */<=0){
        if(_Ur/* s2dPw */>=0){
          var _Uw/* s2dPF */ = quotRemI/* EXTERNAL */(_Ur/* s2dPw */, _Ut/* s2dPy */);
          return new T2(0,_Uw/* s2dPF */.a,_Uw/* s2dPF */.b);
        }else{
          if(_Ut/* s2dPy */<=0){
            var _Ux/* s2dPM */ = quotRemI/* EXTERNAL */(_Ur/* s2dPw */, _Ut/* s2dPy */);
            return new T2(0,_Ux/* s2dPM */.a,_Ux/* s2dPM */.b);
          }else{
            var _Uy/* s2dPS */ = quotRemI/* EXTERNAL */(_Ur/* s2dPw */+1|0, _Ut/* s2dPy */);
            return new T2(0,_Uy/* s2dPS */.a-1|0,(_Uy/* s2dPS */.b+_Ut/* s2dPy */|0)-1|0);
          }
        }
      }else{
        if(_Ut/* s2dPy */>=0){
          if(_Ur/* s2dPw */>=0){
            var _Uz/* s2dQ4 */ = quotRemI/* EXTERNAL */(_Ur/* s2dPw */, _Ut/* s2dPy */);
            return new T2(0,_Uz/* s2dQ4 */.a,_Uz/* s2dQ4 */.b);
          }else{
            if(_Ut/* s2dPy */<=0){
              var _UA/* s2dQb */ = quotRemI/* EXTERNAL */(_Ur/* s2dPw */, _Ut/* s2dPy */);
              return new T2(0,_UA/* s2dQb */.a,_UA/* s2dQb */.b);
            }else{
              var _UB/* s2dQh */ = quotRemI/* EXTERNAL */(_Ur/* s2dPw */+1|0, _Ut/* s2dPy */);
              return new T2(0,_UB/* s2dQh */.a-1|0,(_UB/* s2dQh */.b+_Ut/* s2dPy */|0)-1|0);
            }
          }
        }else{
          var _UC/* s2dQq */ = quotRemI/* EXTERNAL */(_Ur/* s2dPw */-1|0, _Ut/* s2dPy */);
          return new T2(0,_UC/* s2dQq */.a-1|0,(_UC/* s2dQq */.b+_Ut/* s2dPy */|0)+1|0);
        }
      }
    };
    if(E(_Ut/* s2dPy */)==(-1)){
      if(E(_Ur/* s2dPw */)==(-2147483648)){
        return new T2(0,_Po/* GHC.Real.overflowError */,_Up/* GHC.Int.$fBitsInt4 */);
      }else{
        return new F(function(){return _Uu/* s2dPz */(_/* EXTERNAL */);});
      }
    }else{
      return new F(function(){return _Uu/* s2dPz */(_/* EXTERNAL */);});
    }
  }
},
_UD/* lvl1 */ = new T1(0,-1),
_UE/* signumInteger */ = function(_UF/* s1OO */){
  var _UG/* s1OP */ = E(_UF/* s1OO */);
  if(!_UG/* s1OP */._){
    var _UH/* s1OQ */ = _UG/* s1OP */.a;
    return (_UH/* s1OQ */>=0) ? (E(_UH/* s1OQ */)==0) ? E(_JR/* GHC.Integer.Type.lvl */) : E(_K6/* GHC.Integer.Type.log2I1 */) : E(_UD/* GHC.Integer.Type.lvl1 */);
  }else{
    var _UI/* s1OW */ = I_compareInt/* EXTERNAL */(_UG/* s1OP */.a, 0);
    return (_UI/* s1OW */<=0) ? (E(_UI/* s1OW */)==0) ? E(_JR/* GHC.Integer.Type.lvl */) : E(_UD/* GHC.Integer.Type.lvl1 */) : E(_K6/* GHC.Integer.Type.log2I1 */);
  }
},
_UJ/* $w$s$c/ */ = function(_UK/* svwb */, _UL/* svwc */, _UM/* svwd */, _UN/* svwe */){
  var _UO/* svwf */ = B(_S3/* GHC.Integer.Type.timesInteger */(_UL/* svwc */, _UM/* svwd */));
  return new F(function(){return _RZ/* GHC.Real.$w$sreduce */(B(_S3/* GHC.Integer.Type.timesInteger */(B(_S3/* GHC.Integer.Type.timesInteger */(_UK/* svwb */, _UN/* svwe */)), B(_UE/* GHC.Integer.Type.signumInteger */(_UO/* svwf */)))), B(_RJ/* GHC.Integer.Type.absInteger */(_UO/* svwf */)));});
},
_UP/* $fHasResolutionE12_$cresolution */ = function(_UQ/* s6Sx3 */){
  return E(_Uo/* Data.Fixed.$fHasResolutionE5 */);
},
_UR/* $fEnumInteger2 */ = new T1(0,1),
_US/* $wenumDeltaInteger */ = function(_UT/* smJm */, _UU/* smJn */){
  var _UV/* smJo */ = E(_UT/* smJm */);
  return new T2(0,_UV/* smJo */,new T(function(){
    var _UW/* smJq */ = B(_US/* GHC.Enum.$wenumDeltaInteger */(B(_K8/* GHC.Integer.Type.plusInteger */(_UV/* smJo */, _UU/* smJn */)), _UU/* smJn */));
    return new T2(1,_UW/* smJq */.a,_UW/* smJq */.b);
  }));
},
_UX/* $fEnumInteger_$cenumFrom */ = function(_UY/* smJF */){
  var _UZ/* smJG */ = B(_US/* GHC.Enum.$wenumDeltaInteger */(_UY/* smJF */, _UR/* GHC.Enum.$fEnumInteger2 */));
  return new T2(1,_UZ/* smJG */.a,_UZ/* smJG */.b);
},
_V0/* $fEnumInteger_$cenumFromThen */ = function(_V1/* smJJ */, _V2/* smJK */){
  var _V3/* smJM */ = B(_US/* GHC.Enum.$wenumDeltaInteger */(_V1/* smJJ */, new T(function(){
    return B(_LN/* GHC.Integer.Type.minusInteger */(_V2/* smJK */, _V1/* smJJ */));
  })));
  return new T2(1,_V3/* smJM */.a,_V3/* smJM */.b);
},
_V4/* enumDeltaToInteger */ = function(_V5/* smJP */, _V6/* smJQ */, _V7/* smJR */){
  if(!B(_Lf/* GHC.Integer.Type.geInteger */(_V6/* smJQ */, _Le/* GHC.Enum.$fEnumInteger1 */))){
    var _V8/* smJT */ = function(_V9/* smJU */){
      return (!B(_Ln/* GHC.Integer.Type.ltInteger */(_V9/* smJU */, _V7/* smJR */))) ? new T2(1,_V9/* smJU */,new T(function(){
        return B(_V8/* smJT */(B(_K8/* GHC.Integer.Type.plusInteger */(_V9/* smJU */, _V6/* smJQ */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _V8/* smJT */(_V5/* smJP */);});
  }else{
    var _Va/* smJY */ = function(_Vb/* smJZ */){
      return (!B(_KR/* GHC.Integer.Type.gtInteger */(_Vb/* smJZ */, _V7/* smJR */))) ? new T2(1,_Vb/* smJZ */,new T(function(){
        return B(_Va/* smJY */(B(_K8/* GHC.Integer.Type.plusInteger */(_Vb/* smJZ */, _V6/* smJQ */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _Va/* smJY */(_V5/* smJP */);});
  }
},
_Vc/* $fEnumInteger_$cenumFromThenTo */ = function(_Vd/* smKg */, _Ve/* smKh */, _Vf/* smKi */){
  return new F(function(){return _V4/* GHC.Enum.enumDeltaToInteger */(_Vd/* smKg */, B(_LN/* GHC.Integer.Type.minusInteger */(_Ve/* smKh */, _Vd/* smKg */)), _Vf/* smKi */);});
},
_Vg/* $fEnumInteger_$cenumFromTo */ = function(_Vh/* smKe */, _Vi/* smKf */){
  return new F(function(){return _V4/* GHC.Enum.enumDeltaToInteger */(_Vh/* smKe */, _UR/* GHC.Enum.$fEnumInteger2 */, _Vi/* smKf */);});
},
_Vj/* integerToInt */ = function(_Vk/* s1Rv */){
  var _Vl/* s1Rw */ = E(_Vk/* s1Rv */);
  if(!_Vl/* s1Rw */._){
    return E(_Vl/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_Vl/* s1Rw */.a);});
  }
},
_Vm/* $fEnumInteger_$cfromEnum */ = function(_Vn/* smJf */){
  return new F(function(){return _Vj/* GHC.Integer.Type.integerToInt */(_Vn/* smJf */);});
},
_Vo/* $fEnumInteger_$cpred */ = function(_Vp/* smJl */){
  return new F(function(){return _LN/* GHC.Integer.Type.minusInteger */(_Vp/* smJl */, _UR/* GHC.Enum.$fEnumInteger2 */);});
},
_Vq/* $fEnumInteger_$csucc */ = function(_Vr/* smJk */){
  return new F(function(){return _K8/* GHC.Integer.Type.plusInteger */(_Vr/* smJk */, _UR/* GHC.Enum.$fEnumInteger2 */);});
},
_Vs/* $fEnumInteger_$ctoEnum */ = function(_Vt/* smJh */){
  return new F(function(){return _My/* GHC.Integer.Type.smallInteger */(E(_Vt/* smJh */));});
},
_Vu/* $fEnumInteger */ = {_:0,a:_Vq/* GHC.Enum.$fEnumInteger_$csucc */,b:_Vo/* GHC.Enum.$fEnumInteger_$cpred */,c:_Vs/* GHC.Enum.$fEnumInteger_$ctoEnum */,d:_Vm/* GHC.Enum.$fEnumInteger_$cfromEnum */,e:_UX/* GHC.Enum.$fEnumInteger_$cenumFrom */,f:_V0/* GHC.Enum.$fEnumInteger_$cenumFromThen */,g:_Vg/* GHC.Enum.$fEnumInteger_$cenumFromTo */,h:_Vc/* GHC.Enum.$fEnumInteger_$cenumFromThenTo */},
_Vv/* divInt# */ = function(_Vw/* scDT */, _Vx/* scDU */){
  if(_Vw/* scDT */<=0){
    if(_Vw/* scDT */>=0){
      return new F(function(){return quot/* EXTERNAL */(_Vw/* scDT */, _Vx/* scDU */);});
    }else{
      if(_Vx/* scDU */<=0){
        return new F(function(){return quot/* EXTERNAL */(_Vw/* scDT */, _Vx/* scDU */);});
      }else{
        return quot/* EXTERNAL */(_Vw/* scDT */+1|0, _Vx/* scDU */)-1|0;
      }
    }
  }else{
    if(_Vx/* scDU */>=0){
      if(_Vw/* scDT */>=0){
        return new F(function(){return quot/* EXTERNAL */(_Vw/* scDT */, _Vx/* scDU */);});
      }else{
        if(_Vx/* scDU */<=0){
          return new F(function(){return quot/* EXTERNAL */(_Vw/* scDT */, _Vx/* scDU */);});
        }else{
          return quot/* EXTERNAL */(_Vw/* scDT */+1|0, _Vx/* scDU */)-1|0;
        }
      }
    }else{
      return quot/* EXTERNAL */(_Vw/* scDT */-1|0, _Vx/* scDU */)-1|0;
    }
  }
},
_Vy/* divInteger */ = function(_Vz/* s1Nz */, _VA/* s1NA */){
  while(1){
    var _VB/* s1NB */ = E(_Vz/* s1Nz */);
    if(!_VB/* s1NB */._){
      var _VC/* s1ND */ = E(_VB/* s1NB */.a);
      if(_VC/* s1ND */==(-2147483648)){
        _Vz/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _VD/* s1NE */ = E(_VA/* s1NA */);
        if(!_VD/* s1NE */._){
          return new T1(0,B(_Vv/* GHC.Classes.divInt# */(_VC/* s1ND */, _VD/* s1NE */.a)));
        }else{
          _Vz/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(_VC/* s1ND */));
          _VA/* s1NA */ = _VD/* s1NE */;
          continue;
        }
      }
    }else{
      var _VE/* s1NO */ = _VB/* s1NB */.a,
      _VF/* s1NP */ = E(_VA/* s1NA */);
      return (_VF/* s1NP */._==0) ? new T1(1,I_div/* EXTERNAL */(_VE/* s1NO */, I_fromInt/* EXTERNAL */(_VF/* s1NP */.a))) : new T1(1,I_div/* EXTERNAL */(_VE/* s1NO */, _VF/* s1NP */.a));
    }
  }
},
_VG/* $fIntegralInteger_$cdiv */ = function(_VH/* svup */, _VI/* svuq */){
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_VI/* svuq */, _Rs/* GHC.Real.even1 */))){
    return new F(function(){return _Vy/* GHC.Integer.Type.divInteger */(_VH/* svup */, _VI/* svuq */);});
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_VJ/* divModInteger */ = function(_VK/* s1MF */, _VL/* s1MG */){
  while(1){
    var _VM/* s1MH */ = E(_VK/* s1MF */);
    if(!_VM/* s1MH */._){
      var _VN/* s1MJ */ = E(_VM/* s1MH */.a);
      if(_VN/* s1MJ */==(-2147483648)){
        _VK/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _VO/* s1MK */ = E(_VL/* s1MG */);
        if(!_VO/* s1MK */._){
          var _VP/* s1ML */ = _VO/* s1MK */.a;
          return new T2(0,new T1(0,B(_Vv/* GHC.Classes.divInt# */(_VN/* s1MJ */, _VP/* s1ML */))),new T1(0,B(_Tp/* GHC.Classes.modInt# */(_VN/* s1MJ */, _VP/* s1ML */))));
        }else{
          _VK/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(_VN/* s1MJ */));
          _VL/* s1MG */ = _VO/* s1MK */;
          continue;
        }
      }
    }else{
      var _VQ/* s1MY */ = E(_VL/* s1MG */);
      if(!_VQ/* s1MY */._){
        _VK/* s1MF */ = _VM/* s1MH */;
        _VL/* s1MG */ = new T1(1,I_fromInt/* EXTERNAL */(_VQ/* s1MY */.a));
        continue;
      }else{
        var _VR/* s1N5 */ = I_divMod/* EXTERNAL */(_VM/* s1MH */.a, _VQ/* s1MY */.a);
        return new T2(0,new T1(1,_VR/* s1N5 */.a),new T1(1,_VR/* s1N5 */.b));
      }
    }
  }
},
_VS/* $fIntegralInteger_$cdivMod */ = function(_VT/* svua */, _VU/* svub */){
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_VU/* svub */, _Rs/* GHC.Real.even1 */))){
    var _VV/* svud */ = B(_VJ/* GHC.Integer.Type.divModInteger */(_VT/* svua */, _VU/* svub */));
    return new T2(0,_VV/* svud */.a,_VV/* svud */.b);
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_VW/* $fIntegralInteger_$cmod */ = function(_VX/* svum */, _VY/* svun */){
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_VY/* svun */, _Rs/* GHC.Real.even1 */))){
    return new F(function(){return _Tw/* GHC.Integer.Type.modInteger */(_VX/* svum */, _VY/* svun */);});
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_VZ/* $fIntegralInteger_$cquot */ = function(_W0/* svvA */, _W1/* svvB */){
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_W1/* svvB */, _Rs/* GHC.Real.even1 */))){
    return new F(function(){return _RO/* GHC.Integer.Type.quotInteger */(_W0/* svvA */, _W1/* svvB */);});
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_W2/* quotRemInteger */ = function(_W3/* s1Ma */, _W4/* s1Mb */){
  while(1){
    var _W5/* s1Mc */ = E(_W3/* s1Ma */);
    if(!_W5/* s1Mc */._){
      var _W6/* s1Me */ = E(_W5/* s1Mc */.a);
      if(_W6/* s1Me */==(-2147483648)){
        _W3/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _W7/* s1Mf */ = E(_W4/* s1Mb */);
        if(!_W7/* s1Mf */._){
          var _W8/* s1Mg */ = _W7/* s1Mf */.a;
          return new T2(0,new T1(0,quot/* EXTERNAL */(_W6/* s1Me */, _W8/* s1Mg */)),new T1(0,_W6/* s1Me */%_W8/* s1Mg */));
        }else{
          _W3/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(_W6/* s1Me */));
          _W4/* s1Mb */ = _W7/* s1Mf */;
          continue;
        }
      }
    }else{
      var _W9/* s1Mt */ = E(_W4/* s1Mb */);
      if(!_W9/* s1Mt */._){
        _W3/* s1Ma */ = _W5/* s1Mc */;
        _W4/* s1Mb */ = new T1(1,I_fromInt/* EXTERNAL */(_W9/* s1Mt */.a));
        continue;
      }else{
        var _Wa/* s1MA */ = I_quotRem/* EXTERNAL */(_W5/* s1Mc */.a, _W9/* s1Mt */.a);
        return new T2(0,new T1(1,_Wa/* s1MA */.a),new T1(1,_Wa/* s1MA */.b));
      }
    }
  }
},
_Wb/* $fIntegralInteger_$cquotRem */ = function(_Wc/* svug */, _Wd/* svuh */){
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_Wd/* svuh */, _Rs/* GHC.Real.even1 */))){
    var _We/* svuj */ = B(_W2/* GHC.Integer.Type.quotRemInteger */(_Wc/* svug */, _Wd/* svuh */));
    return new T2(0,_We/* svuj */.a,_We/* svuj */.b);
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_Wf/* $fIntegralInteger_$ctoInteger */ = function(_Wg/* svu9 */){
  return E(_Wg/* svu9 */);
},
_Wh/* $fNumInteger_$cfromInteger */ = function(_Wi/* s6HU */){
  return E(_Wi/* s6HU */);
},
_Wj/* $fNumInteger */ = {_:0,a:_K8/* GHC.Integer.Type.plusInteger */,b:_LN/* GHC.Integer.Type.minusInteger */,c:_S3/* GHC.Integer.Type.timesInteger */,d:_Ki/* GHC.Integer.Type.negateInteger */,e:_RJ/* GHC.Integer.Type.absInteger */,f:_UE/* GHC.Integer.Type.signumInteger */,g:_Wh/* GHC.Num.$fNumInteger_$cfromInteger */},
_Wk/* neqInteger */ = function(_Wl/* s1GK */, _Wm/* s1GL */){
  var _Wn/* s1GM */ = E(_Wl/* s1GK */);
  if(!_Wn/* s1GM */._){
    var _Wo/* s1GN */ = _Wn/* s1GM */.a,
    _Wp/* s1GO */ = E(_Wm/* s1GL */);
    return (_Wp/* s1GO */._==0) ? _Wo/* s1GN */!=_Wp/* s1GO */.a : (I_compareInt/* EXTERNAL */(_Wp/* s1GO */.a, _Wo/* s1GN */)==0) ? false : true;
  }else{
    var _Wq/* s1GU */ = _Wn/* s1GM */.a,
    _Wr/* s1GV */ = E(_Wm/* s1GL */);
    return (_Wr/* s1GV */._==0) ? (I_compareInt/* EXTERNAL */(_Wq/* s1GU */, _Wr/* s1GV */.a)==0) ? false : true : (I_compare/* EXTERNAL */(_Wq/* s1GU */, _Wr/* s1GV */.a)==0) ? false : true;
  }
},
_Ws/* $fEqInteger */ = new T2(0,_Rk/* GHC.Integer.Type.eqInteger */,_Wk/* GHC.Integer.Type.neqInteger */),
_Wt/* leInteger */ = function(_Wu/* s1Gp */, _Wv/* s1Gq */){
  var _Ww/* s1Gr */ = E(_Wu/* s1Gp */);
  if(!_Ww/* s1Gr */._){
    var _Wx/* s1Gs */ = _Ww/* s1Gr */.a,
    _Wy/* s1Gt */ = E(_Wv/* s1Gq */);
    return (_Wy/* s1Gt */._==0) ? _Wx/* s1Gs */<=_Wy/* s1Gt */.a : I_compareInt/* EXTERNAL */(_Wy/* s1Gt */.a, _Wx/* s1Gs */)>=0;
  }else{
    var _Wz/* s1GA */ = _Ww/* s1Gr */.a,
    _WA/* s1GB */ = E(_Wv/* s1Gq */);
    return (_WA/* s1GB */._==0) ? I_compareInt/* EXTERNAL */(_Wz/* s1GA */, _WA/* s1GB */.a)<=0 : I_compare/* EXTERNAL */(_Wz/* s1GA */, _WA/* s1GB */.a)<=0;
  }
},
_WB/* $fOrdInteger_$cmax */ = function(_WC/* s1HU */, _WD/* s1HV */){
  return (!B(_Wt/* GHC.Integer.Type.leInteger */(_WC/* s1HU */, _WD/* s1HV */))) ? E(_WC/* s1HU */) : E(_WD/* s1HV */);
},
_WE/* $fOrdInteger_$cmin */ = function(_WF/* s1HR */, _WG/* s1HS */){
  return (!B(_Wt/* GHC.Integer.Type.leInteger */(_WF/* s1HR */, _WG/* s1HS */))) ? E(_WG/* s1HS */) : E(_WF/* s1HR */);
},
_WH/* compareInteger */ = function(_WI/* s1Hk */, _WJ/* s1Hl */){
  var _WK/* s1Hm */ = E(_WI/* s1Hk */);
  if(!_WK/* s1Hm */._){
    var _WL/* s1Hn */ = _WK/* s1Hm */.a,
    _WM/* s1Ho */ = E(_WJ/* s1Hl */);
    if(!_WM/* s1Ho */._){
      var _WN/* s1Hp */ = _WM/* s1Ho */.a;
      return (_WL/* s1Hn */!=_WN/* s1Hp */) ? (_WL/* s1Hn */>_WN/* s1Hp */) ? 2 : 0 : 1;
    }else{
      var _WO/* s1Hw */ = I_compareInt/* EXTERNAL */(_WM/* s1Ho */.a, _WL/* s1Hn */);
      return (_WO/* s1Hw */<=0) ? (_WO/* s1Hw */>=0) ? 1 : 2 : 0;
    }
  }else{
    var _WP/* s1HB */ = _WK/* s1Hm */.a,
    _WQ/* s1HC */ = E(_WJ/* s1Hl */);
    if(!_WQ/* s1HC */._){
      var _WR/* s1HF */ = I_compareInt/* EXTERNAL */(_WP/* s1HB */, _WQ/* s1HC */.a);
      return (_WR/* s1HF */>=0) ? (_WR/* s1HF */<=0) ? 1 : 2 : 0;
    }else{
      var _WS/* s1HM */ = I_compare/* EXTERNAL */(_WP/* s1HB */, _WQ/* s1HC */.a);
      return (_WS/* s1HM */>=0) ? (_WS/* s1HM */<=0) ? 1 : 2 : 0;
    }
  }
},
_WT/* $fOrdInteger */ = {_:0,a:_Ws/* GHC.Integer.Type.$fEqInteger */,b:_WH/* GHC.Integer.Type.compareInteger */,c:_Ln/* GHC.Integer.Type.ltInteger */,d:_Wt/* GHC.Integer.Type.leInteger */,e:_KR/* GHC.Integer.Type.gtInteger */,f:_Lf/* GHC.Integer.Type.geInteger */,g:_WB/* GHC.Integer.Type.$fOrdInteger_$cmax */,h:_WE/* GHC.Integer.Type.$fOrdInteger_$cmin */},
_WU/* $fRealInteger_$s$cfromInteger */ = function(_WV/* svmz */){
  return new T2(0,E(_WV/* svmz */),E(_KK/* GHC.Real.$fEnumRatio1 */));
},
_WW/* $fRealInteger */ = new T3(0,_Wj/* GHC.Num.$fNumInteger */,_WT/* GHC.Integer.Type.$fOrdInteger */,_WU/* GHC.Real.$fRealInteger_$s$cfromInteger */),
_WX/* $fIntegralInteger */ = {_:0,a:_WW/* GHC.Real.$fRealInteger */,b:_Vu/* GHC.Enum.$fEnumInteger */,c:_VZ/* GHC.Real.$fIntegralInteger_$cquot */,d:_RB/* GHC.Real.$fIntegralInteger_$crem */,e:_VG/* GHC.Real.$fIntegralInteger_$cdiv */,f:_VW/* GHC.Real.$fIntegralInteger_$cmod */,g:_Wb/* GHC.Real.$fIntegralInteger_$cquotRem */,h:_VS/* GHC.Real.$fIntegralInteger_$cdivMod */,i:_Wf/* GHC.Real.$fIntegralInteger_$ctoInteger */},
_WY/* $fFractionalFixed1 */ = new T1(0,0),
_WZ/* $fNumFixed5 */ = function(_X0/* s6SxT */, _X1/* s6SxU */, _X2/* s6SxV */){
  var _X3/* s6SxW */ = B(A1(_X0/* s6SxT */,_X1/* s6SxU */));
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_X3/* s6SxW */, _WY/* Data.Fixed.$fFractionalFixed1 */))){
    return new F(function(){return _Vy/* GHC.Integer.Type.divInteger */(B(_S3/* GHC.Integer.Type.timesInteger */(_X1/* s6SxU */, _X2/* s6SxV */)), _X3/* s6SxW */);});
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_X4/* $w$s$cproperFraction */ = function(_X5/* svn0 */, _X6/* svn1 */, _X7/* svn2 */){
  var _X8/* svn3 */ = new T(function(){
    if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_X7/* svn2 */, _Rs/* GHC.Real.even1 */))){
      var _X9/* svn5 */ = B(_W2/* GHC.Integer.Type.quotRemInteger */(_X6/* svn1 */, _X7/* svn2 */));
      return new T2(0,_X9/* svn5 */.a,_X9/* svn5 */.b);
    }else{
      return E(_Pl/* GHC.Real.divZeroError */);
    }
  }),
  _Xa/* svne */ = new T(function(){
    return B(A2(_KP/* GHC.Num.fromInteger */,B(_KN/* GHC.Real.$p1Real */(B(_KL/* GHC.Real.$p1Integral */(_X5/* svn0 */)))), new T(function(){
      return E(E(_X8/* svn3 */).a);
    })));
  });
  return new T2(0,_Xa/* svne */,new T(function(){
    return new T2(0,E(E(_X8/* svn3 */).b),E(_X7/* svn2 */));
  }));
},
_Xb/* - */ = function(_Xc/* s6FH */){
  return E(E(_Xc/* s6FH */).b);
},
_Xd/* $w$s$cfloor */ = function(_Xe/* svJO */, _Xf/* svJP */, _Xg/* svJQ */){
  var _Xh/* svJR */ = B(_X4/* GHC.Real.$w$s$cproperFraction */(_Xe/* svJO */, _Xf/* svJP */, _Xg/* svJQ */)),
  _Xi/* svJS */ = _Xh/* svJR */.a,
  _Xj/* svJU */ = E(_Xh/* svJR */.b);
  if(!B(_Ln/* GHC.Integer.Type.ltInteger */(B(_S3/* GHC.Integer.Type.timesInteger */(_Xj/* svJU */.a, _KK/* GHC.Real.$fEnumRatio1 */)), B(_S3/* GHC.Integer.Type.timesInteger */(_Rs/* GHC.Real.even1 */, _Xj/* svJU */.b))))){
    return E(_Xi/* svJS */);
  }else{
    var _Xk/* svK1 */ = B(_KN/* GHC.Real.$p1Real */(B(_KL/* GHC.Real.$p1Integral */(_Xe/* svJO */))));
    return new F(function(){return A3(_Xb/* GHC.Num.- */,_Xk/* svK1 */, _Xi/* svJS */, new T(function(){
      return B(A2(_KP/* GHC.Num.fromInteger */,_Xk/* svK1 */, _KK/* GHC.Real.$fEnumRatio1 */));
    }));});
  }
},
_Xl/* slaT */ = 479723520,
_Xm/* slaU */ = 40233135,
_Xn/* slaV */ = new T2(1,_Xm/* slaU */,_6/* GHC.Types.[] */),
_Xo/* slaW */ = new T2(1,_Xl/* slaT */,_Xn/* slaV */),
_Xp/* posixDayLength1 */ = new T(function(){
  return B(_Km/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _Xo/* slaW */));
}),
_Xq/* posixSecondsToUTCTime1 */ = new T1(0,40587),
_Xr/* $wposixSecondsToUTCTime */ = function(_Xs/* slaX */){
  var _Xt/* slaY */ = new T(function(){
    var _Xu/* slaZ */ = B(_UJ/* GHC.Real.$w$s$c/ */(_Xs/* slaX */, _KK/* GHC.Real.$fEnumRatio1 */, _Uo/* Data.Fixed.$fHasResolutionE5 */, _KK/* GHC.Real.$fEnumRatio1 */)),
    _Xv/* slb2 */ = B(_UJ/* GHC.Real.$w$s$c/ */(_Xp/* Data.Time.Clock.POSIX.posixDayLength1 */, _KK/* GHC.Real.$fEnumRatio1 */, _Uo/* Data.Fixed.$fHasResolutionE5 */, _KK/* GHC.Real.$fEnumRatio1 */)),
    _Xw/* slb5 */ = B(_UJ/* GHC.Real.$w$s$c/ */(_Xu/* slaZ */.a, _Xu/* slaZ */.b, _Xv/* slb2 */.a, _Xv/* slb2 */.b));
    return B(_Xd/* GHC.Real.$w$s$cfloor */(_WX/* GHC.Real.$fIntegralInteger */, _Xw/* slb5 */.a, _Xw/* slb5 */.b));
  });
  return new T2(0,new T(function(){
    return B(_K8/* GHC.Integer.Type.plusInteger */(_Xq/* Data.Time.Clock.POSIX.posixSecondsToUTCTime1 */, _Xt/* slaY */));
  }),new T(function(){
    return B(_LN/* GHC.Integer.Type.minusInteger */(_Xs/* slaX */, B(_WZ/* Data.Fixed.$fNumFixed5 */(_UP/* Data.Fixed.$fHasResolutionE12_$cresolution */, B(_S3/* GHC.Integer.Type.timesInteger */(_Xt/* slaY */, _Uo/* Data.Fixed.$fHasResolutionE5 */)), _Xp/* Data.Time.Clock.POSIX.posixDayLength1 */))));
  }));
},
_Xx/* getCPUTime2 */ = new T1(0,0),
_Xy/* $wa1 */ = function(_Xz/* s3vS */, _/* EXTERNAL */){
  var _XA/* s3vX */ = __get/* EXTERNAL */(_Xz/* s3vS */, 0),
  _XB/* s3w3 */ = __get/* EXTERNAL */(_Xz/* s3vS */, 1),
  _XC/* s3w7 */ = Number/* EXTERNAL */(_XA/* s3vX */),
  _XD/* s3wb */ = jsTrunc/* EXTERNAL */(_XC/* s3w7 */),
  _XE/* s3wf */ = Number/* EXTERNAL */(_XB/* s3w3 */),
  _XF/* s3wj */ = jsTrunc/* EXTERNAL */(_XE/* s3wf */);
  return new T2(0,_XD/* s3wb */,_XF/* s3wj */);
},
_XG/* getCTimeval_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");
}),
_XH/* slbq */ = 660865024,
_XI/* slbr */ = 465661287,
_XJ/* slbs */ = new T2(1,_XI/* slbr */,_6/* GHC.Types.[] */),
_XK/* slbt */ = new T2(1,_XH/* slbq */,_XJ/* slbs */),
_XL/* getPOSIXTime2 */ = new T(function(){
  return B(_Km/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _XK/* slbt */));
}),
_XM/* getPOSIXTime1 */ = function(_/* EXTERNAL */){
  var _XN/* slby */ = __app0/* EXTERNAL */(E(_XG/* Data.Time.Clock.CTimeval.getCTimeval_f1 */)),
  _XO/* slbB */ = B(_Xy/* Data.Time.Clock.CTimeval.$wa1 */(_XN/* slby */, _/* EXTERNAL */));
  return new T(function(){
    var _XP/* slbE */ = E(_XO/* slbB */);
    if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_XL/* Data.Time.Clock.POSIX.getPOSIXTime2 */, _WY/* Data.Fixed.$fFractionalFixed1 */))){
      return B(_K8/* GHC.Integer.Type.plusInteger */(B(_S3/* GHC.Integer.Type.timesInteger */(B(_My/* GHC.Integer.Type.smallInteger */(E(_XP/* slbE */.a))), _Uo/* Data.Fixed.$fHasResolutionE5 */)), B(_Vy/* GHC.Integer.Type.divInteger */(B(_S3/* GHC.Integer.Type.timesInteger */(B(_S3/* GHC.Integer.Type.timesInteger */(B(_My/* GHC.Integer.Type.smallInteger */(E(_XP/* slbE */.b))), _Uo/* Data.Fixed.$fHasResolutionE5 */)), _Uo/* Data.Fixed.$fHasResolutionE5 */)), _XL/* Data.Time.Clock.POSIX.getPOSIXTime2 */))));
    }else{
      return E(_Pl/* GHC.Real.divZeroError */);
    }
  });
},
_XQ/* getStdRandom3 */ = new T1(0,12345),
_XR/* getStdRandom2 */ = function(_/* EXTERNAL */){
  var _XS/* sfpA */ = B(_XM/* Data.Time.Clock.POSIX.getPOSIXTime1 */(0)),
  _XT/* sfpG */ = B(_UJ/* GHC.Real.$w$s$c/ */(B(_Xr/* Data.Time.Clock.POSIX.$wposixSecondsToUTCTime */(_XS/* sfpA */)).b, _KK/* GHC.Real.$fEnumRatio1 */, _Uo/* Data.Fixed.$fHasResolutionE5 */, _KK/* GHC.Real.$fEnumRatio1 */)),
  _XU/* sfpI */ = _XT/* sfpG */.b;
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_XU/* sfpI */, _Tn/* System.Random.getStdRandom4 */))){
    var _XV/* sfpK */ = B(_W2/* GHC.Integer.Type.quotRemInteger */(_XT/* sfpG */.a, _XU/* sfpI */));
    return new F(function(){return nMV/* EXTERNAL */(new T(function(){
      var _XW/* sfpV */ = B(_Uq/* GHC.Int.$w$cdivMod1 */((B(_Vj/* GHC.Integer.Type.integerToInt */(B(_K8/* GHC.Integer.Type.plusInteger */(B(_K8/* GHC.Integer.Type.plusInteger */(B(_K8/* GHC.Integer.Type.plusInteger */(B(_S3/* GHC.Integer.Type.timesInteger */(_XV/* sfpK */.a, _XQ/* System.Random.getStdRandom3 */)), _XV/* sfpK */.b)), _Xx/* System.CPUTime.getCPUTime2 */)), _Tn/* System.Random.getStdRandom4 */))))>>>0&2147483647)>>>0&4294967295, 2147483562));
      return new T2(0,E(_XW/* sfpV */.b)+1|0,B(_Tp/* GHC.Classes.modInt# */(E(_XW/* sfpV */.a), 2147483398))+1|0);
    }));});
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_XX/* theStdGen */ = new T(function(){
  return B(_44/* GHC.IO.unsafeDupablePerformIO */(_XR/* System.Random.getStdRandom2 */));
}),
_XY/* $fRandomDouble8 */ = function(_XZ/* sfTt */, _/* EXTERNAL */){
  var _Y0/* sfTM */ = mMV/* EXTERNAL */(E(_XX/* System.Random.theStdGen */), function(_Y1/* sfTx */){
    var _Y2/* sfTy */ = E(_XZ/* sfTt */),
    _Y3/* sfTF */ = B(_U6/* System.Random.$w$srandomRFloating2 */(E(_Y2/* sfTy */.a), E(_Y2/* sfTy */.b), _Y1/* sfTx */));
    return new T2(0,E(_Y3/* sfTF */.b),_Y3/* sfTF */.a);
  }),
  _Y4/* sfTQ */ = E(_Y0/* sfTM */);
  return _Y0/* sfTM */;
},
_Y5/* speedMot19 */ = 1,
_Y6/* speedMot18 */ = new T2(0,_Ji/* Motion.Speed.speedMot14 */,_Y5/* Motion.Speed.speedMot19 */),
_Y7/* speedMot17 */ = function(_/* EXTERNAL */){
  return new F(function(){return _XY/* System.Random.$fRandomDouble8 */(_Y6/* Motion.Speed.speedMot18 */, _/* EXTERNAL */);});
},
_Y8/* speedMot16 */ = new T1(1,_Y7/* Motion.Speed.speedMot17 */),
_Y9/* speedMot15 */ = new T(function(){
  return B(_rn/* Control.Monad.Skeleton.bone */(_Y8/* Motion.Speed.speedMot16 */));
}),
_Ya/* speedMot3 */ = 60,
_Yb/* speedMot2 */ = new T1(0,_Ya/* Motion.Speed.speedMot3 */),
_Yc/* speedMot22 */ = 100,
_Yd/* speedMot21 */ = new T1(0,_Yc/* Motion.Speed.speedMot22 */),
_Ye/* speedMot20 */ = new T2(0,_Yd/* Motion.Speed.speedMot21 */,_Yd/* Motion.Speed.speedMot21 */),
_Yf/* speedMot5 */ = -30,
_Yg/* speedMot4 */ = new T1(0,_Yf/* Motion.Speed.speedMot5 */),
_Yh/* speedMot8 */ = new T(function(){
  return  -0;
}),
_Yi/* speedMot7 */ = new T1(0,_Yh/* Motion.Speed.speedMot8 */),
_Yj/* speedMot6 */ = new T2(0,_Yi/* Motion.Speed.speedMot7 */,_Yi/* Motion.Speed.speedMot7 */),
_Yk/* $fFloatingDouble_$cpi */ = 3.141592653589793,
_Yl/* $s$fFloatingValue_$cpi */ = new T1(0,_Yk/* GHC.Float.$fFloatingDouble_$cpi */),
_Ym/* speedMot11 */ = 6,
_Yn/* speedMot10 */ = new T1(0,_Ym/* Motion.Speed.speedMot11 */),
_Yo/* speedMot9 */ = new T(function(){
  return B(_s6/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, _Yl/* Motion.Speed.$s$fFloatingValue_$cpi */, _Yn/* Motion.Speed.speedMot10 */));
}),
_Yp/* speedMot */ = function(_Yq/* sRjs */){
  var _Yr/* sRjt */ = new T(function(){
    var _Ys/* sRkl */ = new T(function(){
      var _Yt/* sRju */ = E(_Y9/* Motion.Speed.speedMot15 */),
      _Yu/* sRjv */ = _Yt/* sRju */.a,
      _Yv/* sRjw */ = _Yt/* sRju */.b,
      _Yw/* sRki */ = function(_Yx/* sRjx */){
        var _Yy/* sRjy */ = new T(function(){
          var _Yz/* sRjB */ = Math.log/* EXTERNAL */(E(_Yx/* sRjx */));
          return Math.sqrt/* EXTERNAL */( -(_Yz/* sRjB */+_Yz/* sRjB */));
        }),
        _YA/* sRkf */ = function(_YB/* sRjF */){
          var _YC/* sRjG */ = new T(function(){
            var _YD/* sRjH */ = E(_Yy/* sRjy */),
            _YE/* sRjJ */ = E(_YB/* sRjF */);
            return _YD/* sRjH */*Math.sin/* EXTERNAL */(6.283185307179586*_YE/* sRjJ */)+_YD/* sRjH */*Math.sin/* EXTERNAL */(6.283185307179586*_YE/* sRjJ */);
          }),
          _YF/* sRkc */ = function(_YG/* sRjT */){
            var _YH/* sRka */ = new T(function(){
              var _YI/* sRk8 */ = new T(function(){
                var _YJ/* sRk6 */ = new T(function(){
                  var _YK/* sRk5 */ = new T(function(){
                    var _YL/* sRk0 */ = new T(function(){
                      return B(_s6/* Core.Ease.opLift */(_th/* GHC.Float.plusDouble */, _Yg/* Motion.Speed.speedMot4 */, new T1(0,new T(function(){
                        return 4/(1-E(_YG/* sRjT */));
                      }))));
                    }),
                    _YM/* sRk1 */ = B(_GE/* Core.Shape.Internal.$wcenterRect */(new T1(0,_YC/* sRjG */), _YL/* sRk0 */, _Yb/* Motion.Speed.speedMot2 */, _Yb/* Motion.Speed.speedMot2 */));
                    return new T3(0,_YM/* sRk1 */.a,_YM/* sRk1 */.b,_YM/* sRk1 */.c);
                  });
                  return B(_rr/* Core.Render.Internal.fill1 */(_Yq/* sRjs */, _YK/* sRk5 */));
                });
                return B(_rn/* Control.Monad.Skeleton.bone */(new T3(5,_Yj/* Motion.Speed.speedMot6 */,_YJ/* sRk6 */,_7/* GHC.Tuple.() */)));
              });
              return B(_rn/* Control.Monad.Skeleton.bone */(new T3(6,_Yo/* Motion.Speed.speedMot9 */,_YI/* sRk8 */,_7/* GHC.Tuple.() */)));
            });
            return new F(function(){return _rn/* Control.Monad.Skeleton.bone */(new T3(5,_Jk/* Motion.Speed.speedMot12 */,_YH/* sRka */,_7/* GHC.Tuple.() */));});
          };
          return new T2(0,E(_Yu/* sRjv */),E(new T2(2,_Yv/* sRjw */,new T1(1,_YF/* sRkc */))));
        };
        return new T2(0,E(_Yu/* sRjv */),E(new T2(2,_Yv/* sRjw */,new T1(1,_YA/* sRkf */))));
      };
      return new T2(0,E(_Yu/* sRjv */),E(new T2(2,_Yv/* sRjw */,new T1(1,_Yw/* sRki */))));
    });
    return B(_rn/* Control.Monad.Skeleton.bone */(new T3(5,_Ye/* Motion.Speed.speedMot20 */,_Ys/* sRkl */,_7/* GHC.Tuple.() */)));
  });
  return function(_YN/* sRko */, _YO/* sRkp */){
    return new F(function(){return A1(_YO/* sRkp */,new T2(0,new T2(0,_Yr/* sRjt */,_Jf/* Motion.Speed.speedMot1 */),_YN/* sRko */));});
  };
},
_YP/* lvl49 */ = new T(function(){
  return B(_Fc/* Motion.Main.consView */(_Jc/* Motion.Main.lvl46 */, _Yp/* Motion.Speed.speedMot */, _Jd/* Motion.Main.lvl47 */, _Je/* Motion.Main.lvl48 */));
}),
_YQ/* $sreplicateM2 */ = function(_YR/* s81j */, _YS/* s81k */){
  var _YT/* s81l */ = E(_YR/* s81j */);
  if(!_YT/* s81l */._){
    return function(_YU/* s81n */){
      return new F(function(){return A1(_YU/* s81n */,new T2(0,_6/* GHC.Types.[] */,_YS/* s81k */));});
    };
  }else{
    var _YV/* s81C */ = function(_YW/* s81r */){
      var _YX/* s81s */ = new T(function(){
        return B(A1(_YT/* s81l */.a,_YW/* s81r */));
      }),
      _YY/* s81B */ = function(_YZ/* s81t */){
        var _Z0/* s81A */ = function(_Z1/* s81u */){
          var _Z2/* s81z */ = new T(function(){
            var _Z3/* s81v */ = E(_Z1/* s81u */);
            return new T2(0,function(_Z4/* B1 */){
              return new T2(1,_Z3/* s81v */.a,_Z4/* B1 */);
            },_Z3/* s81v */.b);
          });
          return new F(function(){return A1(_YZ/* s81t */,_Z2/* s81z */);});
        };
        return new F(function(){return A1(_YX/* s81s */,_Z0/* s81A */);});
      };
      return E(_YY/* s81B */);
    };
    return new F(function(){return _55/* Core.World.Internal.$fApplicativeWorld3 */(_YV/* s81C */, function(_Z4/* B1 */){
      return new F(function(){return _YQ/* Motion.Change.$sreplicateM2 */(_YT/* s81l */.b, _Z4/* B1 */);});
    }, _YS/* s81k */);});
  }
},
_Z5/* $swhen1 */ = new T(function(){
  return B(_qO/* Control.Monad.Skeleton.$w$cpure */(_/* EXTERNAL */, _7/* GHC.Tuple.() */));
}),
_Z6/* $fNumInt_$c* */ = function(_Z7/* s6GP */, _Z8/* s6GQ */){
  return imul/* EXTERNAL */(E(_Z7/* s6GP */), E(_Z8/* s6GQ */))|0;
},
_Z9/* $fNumInt_$c+ */ = function(_Za/* s6H3 */, _Zb/* s6H4 */){
  return E(_Za/* s6H3 */)+E(_Zb/* s6H4 */)|0;
},
_Zc/* $fNumInt_$c- */ = function(_Zd/* s6GW */, _Ze/* s6GX */){
  return E(_Zd/* s6GW */)-E(_Ze/* s6GX */)|0;
},
_Zf/* $fNumInt_$cabs */ = function(_Zg/* s6Hg */){
  var _Zh/* s6Hh */ = E(_Zg/* s6Hg */);
  return (_Zh/* s6Hh */<0) ?  -_Zh/* s6Hh */ : E(_Zh/* s6Hh */);
},
_Zi/* $fNumInt_$cfromInteger */ = function(_Zj/* s6GJ */){
  return new F(function(){return _Vj/* GHC.Integer.Type.integerToInt */(_Zj/* s6GJ */);});
},
_Zk/* $fNumInt_$cnegate */ = function(_Zl/* s6GL */){
  return  -E(_Zl/* s6GL */);
},
_Zm/* $fNumInt1 */ = -1,
_Zn/* $fNumInt2 */ = 0,
_Zo/* $fNumInt3 */ = 1,
_Zp/* $fNumInt_$csignum */ = function(_Zq/* s6Ha */){
  var _Zr/* s6Hb */ = E(_Zq/* s6Ha */);
  return (_Zr/* s6Hb */>=0) ? (E(_Zr/* s6Hb */)==0) ? E(_Zn/* GHC.Num.$fNumInt2 */) : E(_Zo/* GHC.Num.$fNumInt3 */) : E(_Zm/* GHC.Num.$fNumInt1 */);
},
_Zs/* $fNumInt */ = {_:0,a:_Z9/* GHC.Num.$fNumInt_$c+ */,b:_Zc/* GHC.Num.$fNumInt_$c- */,c:_Z6/* GHC.Num.$fNumInt_$c* */,d:_Zk/* GHC.Num.$fNumInt_$cnegate */,e:_Zf/* GHC.Num.$fNumInt_$cabs */,f:_Zp/* GHC.Num.$fNumInt_$csignum */,g:_Zi/* GHC.Num.$fNumInt_$cfromInteger */},
_Zt/* $fRandomBool2 */ = function(_Zu/* sftN */){
  var _Zv/* sftO */ = B(_TE/* System.Random.$w$srandomIvalInteger */(_Zs/* GHC.Num.$fNumInt */, _Tn/* System.Random.getStdRandom4 */, _T8/* System.Random.$fRandomBool3 */, _Zu/* sftN */));
  return new T2(0,E(_Zv/* sftO */.b),new T(function(){
    if(!E(_Zv/* sftO */.a)){
      return false;
    }else{
      return true;
    }
  }));
},
_Zw/* a10 */ = function(_Zx/* s82q */, _Zy/* s82r */, _Zz/* s82s */){
  var _ZA/* s82t */ = E(_Zx/* s82q */);
  if(!_ZA/* s82t */._){
    return new F(function(){return A1(_Zz/* s82s */,new T2(0,_7/* GHC.Tuple.() */,_Zy/* s82r */));});
  }else{
    var _ZB/* s83c */ = function(_/* EXTERNAL */){
      var _ZC/* s82y */ = E(_XX/* System.Random.theStdGen */),
      _ZD/* s82A */ = mMV/* EXTERNAL */(_ZC/* s82y */, _Zt/* System.Random.$fRandomBool2 */);
      return new T(function(){
        var _ZE/* s83a */ = function(_ZF/* s82I */){
          var _ZG/* s82M */ = function(_ZH/* s82N */, _ZI/* s82O */, _ZJ/* s82P */){
            var _ZK/* s82Q */ = E(_ZH/* s82N */);
            if(!_ZK/* s82Q */._){
              return new F(function(){return A1(_ZJ/* s82P */,new T2(0,_7/* GHC.Tuple.() */,_ZI/* s82O */));});
            }else{
              var _ZL/* s839 */ = function(_/* EXTERNAL */){
                var _ZM/* s82V */ = mMV/* EXTERNAL */(_ZC/* s82y */, _Zt/* System.Random.$fRandomBool2 */);
                return new T(function(){
                  return B(A(_jD/* Core.Ease.$wforceTo */,[E(_ZK/* s82Q */.a).c, E(_ZM/* s82V */), _ZI/* s82O */, function(_ZN/* s833 */){
                    return new F(function(){return _ZG/* s82M */(_ZK/* s82Q */.b, E(_ZN/* s833 */).b, _ZJ/* s82P */);});
                  }]));
                });
              };
              return new T1(0,_ZL/* s839 */);
            }
          };
          return new F(function(){return _ZG/* s82M */(_ZA/* s82t */.b, E(_ZF/* s82I */).b, _Zz/* s82s */);});
        };
        return B(A(_jD/* Core.Ease.$wforceTo */,[E(_ZA/* s82t */.a).c, E(_ZD/* s82A */), _Zy/* s82r */, _ZE/* s83a */]));
      });
    };
    return new T1(0,_ZB/* s83c */);
  }
},
_ZO/* a */ = new T1(0,_/* EXTERNAL */),
_ZP/* a1 */ = new T1(0,_7/* GHC.Tuple.() */),
_ZQ/* a2 */ = new T2(0,E(_ZP/* Motion.Change.a1 */),E(_ZO/* Motion.Change.a */)),
_ZR/* lvl */ = new T4(0,_aw/* GHC.Types.True */,_aw/* GHC.Types.True */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_ZS/* lvl1 */ = new T2(0,_aw/* GHC.Types.True */,_ZR/* Motion.Change.lvl */),
_ZT/* lvl2 */ = new T2(0,_ZS/* Motion.Change.lvl1 */,_6/* GHC.Types.[] */),
_ZU/* lvl3 */ = function(_ZV/* s81E */, _ZW/* s81F */){
  var _ZX/* s81O */ = function(_/* EXTERNAL */){
    var _ZY/* s81H */ = nMV/* EXTERNAL */(_ZT/* Motion.Change.lvl2 */);
    return new T(function(){
      return B(A1(_ZW/* s81F */,new T2(0,new T3(0,_jC/* Core.Ease.forceTo_b1 */,_lq/* Core.Ease.easeIn */,_ZY/* s81H */),_ZV/* s81E */)));
    });
  };
  return new T1(0,_ZX/* s81O */);
},
_ZZ/* lvl4 */ = new T2(1,_ZU/* Motion.Change.lvl3 */,_6/* GHC.Types.[] */),
_100/* $wxs */ = function(_101/* s81P */){
  var _102/* s81Q */ = E(_101/* s81P */);
  return (_102/* s81Q */==1) ? E(_ZZ/* Motion.Change.lvl4 */) : new T2(1,_ZU/* Motion.Change.lvl3 */,new T(function(){
    return B(_100/* Motion.Change.$wxs */(_102/* s81Q */-1|0));
  }));
},
_103/* a7 */ = new T(function(){
  return B(_100/* Motion.Change.$wxs */(10));
}),
_104/* dur */ = 10,
_105/* e */ = function(_106/* s81T */, _107/* s81U */){
  return 1-B(A1(_106/* s81T */,new T(function(){
    return Math.pow/* EXTERNAL */(2,  -((1-(1-E(_107/* s81U */)))*10));
  })));
},
_108/* $fRealDouble1 */ = new T1(0,1),
_109/* encodeDoubleInteger */ = function(_10a/* s1LC */, _10b/* s1LD */){
  var _10c/* s1LE */ = E(_10a/* s1LC */);
  return (_10c/* s1LE */._==0) ? _10c/* s1LE */.a*Math.pow/* EXTERNAL */(2, _10b/* s1LD */) : I_toNumber/* EXTERNAL */(_10c/* s1LE */.a)*Math.pow/* EXTERNAL */(2, _10b/* s1LD */);
},
_10d/* rationalToDouble5 */ = new T1(0,0),
_10e/* $w$j1 */ = function(_10f/* s18QG */, _10g/* s18QH */, _10h/* s18QI */){
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_10h/* s18QI */, _10d/* GHC.Float.rationalToDouble5 */))){
    var _10i/* s18QK */ = B(_W2/* GHC.Integer.Type.quotRemInteger */(_10g/* s18QH */, _10h/* s18QI */)),
    _10j/* s18QL */ = _10i/* s18QK */.a;
    switch(B(_WH/* GHC.Integer.Type.compareInteger */(B(_JZ/* GHC.Integer.Type.shiftLInteger */(_10i/* s18QK */.b, 1)), _10h/* s18QI */))){
      case 0:
        return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(_10j/* s18QL */, _10f/* s18QG */);});
        break;
      case 1:
        if(!(B(_Vj/* GHC.Integer.Type.integerToInt */(_10j/* s18QL */))&1)){
          return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(_10j/* s18QL */, _10f/* s18QG */);});
        }else{
          return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(B(_K8/* GHC.Integer.Type.plusInteger */(_10j/* s18QL */, _108/* GHC.Float.$fRealDouble1 */)), _10f/* s18QG */);});
        }
        break;
      default:
        return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(B(_K8/* GHC.Integer.Type.plusInteger */(_10j/* s18QL */, _108/* GHC.Float.$fRealDouble1 */)), _10f/* s18QG */);});
    }
  }else{
    return E(_Pl/* GHC.Real.divZeroError */);
  }
},
_10k/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_10l/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_10m/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_10n/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_10k/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_10l/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_10m/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_10o/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_10n/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_10p/* $fExceptionPatternMatchFail1 */ = function(_10q/* s4nDQ */){
  return E(_10o/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_10r/* $fExceptionPatternMatchFail_$cfromException */ = function(_10s/* s4nE1 */){
  var _10t/* s4nE2 */ = E(_10s/* s4nE1 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_10t/* s4nE2 */.a)), _10p/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _10t/* s4nE2 */.b);});
},
_10u/* $fExceptionPatternMatchFail_$cshow */ = function(_10v/* s4nDT */){
  return E(E(_10v/* s4nDT */).a);
},
_10w/* $fExceptionPatternMatchFail_$ctoException */ = function(_10x/* B1 */){
  return new T2(0,_10y/* Control.Exception.Base.$fExceptionPatternMatchFail */,_10x/* B1 */);
},
_10z/* $fShowPatternMatchFail1 */ = function(_10A/* s4nzz */, _10B/* s4nzA */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_10A/* s4nzz */).a, _10B/* s4nzA */);});
},
_10C/* $fShowPatternMatchFail_$cshowList */ = function(_10D/* s4nDR */, _10E/* s4nDS */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_10z/* Control.Exception.Base.$fShowPatternMatchFail1 */, _10D/* s4nDR */, _10E/* s4nDS */);});
},
_10F/* $fShowPatternMatchFail_$cshowsPrec */ = function(_10G/* s4nDW */, _10H/* s4nDX */, _10I/* s4nDY */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_10H/* s4nDX */).a, _10I/* s4nDY */);});
},
_10J/* $fShowPatternMatchFail */ = new T3(0,_10F/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_10u/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_10C/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_10y/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_10p/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_10J/* Control.Exception.Base.$fShowPatternMatchFail */,_10w/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_10r/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_10u/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_10K/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_10L/* lvl */ = function(_10M/* s2S2g */, _10N/* s2S2h */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_10N/* s2S2h */, _10M/* s2S2g */));
  }));});
},
_10O/* throw1 */ = function(_10P/* B2 */, _Pi/* B1 */){
  return new F(function(){return _10L/* GHC.Exception.lvl */(_10P/* B2 */, _Pi/* B1 */);});
},
_10Q/* $wspan */ = function(_10R/* s9wA */, _10S/* s9wB */){
  var _10T/* s9wC */ = E(_10S/* s9wB */);
  if(!_10T/* s9wC */._){
    return new T2(0,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */);
  }else{
    var _10U/* s9wD */ = _10T/* s9wC */.a;
    if(!B(A1(_10R/* s9wA */,_10U/* s9wD */))){
      return new T2(0,_6/* GHC.Types.[] */,_10T/* s9wC */);
    }else{
      var _10V/* s9wG */ = new T(function(){
        var _10W/* s9wH */ = B(_10Q/* GHC.List.$wspan */(_10R/* s9wA */, _10T/* s9wC */.b));
        return new T2(0,_10W/* s9wH */.a,_10W/* s9wH */.b);
      });
      return new T2(0,new T2(1,_10U/* s9wD */,new T(function(){
        return E(E(_10V/* s9wG */).a);
      })),new T(function(){
        return E(E(_10V/* s9wG */).b);
      }));
    }
  }
},
_10X/* untangle1 */ = 32,
_10Y/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_10Z/* untangle3 */ = function(_110/* s3JKg */){
  return (E(_110/* s3JKg */)==124) ? false : true;
},
_111/* untangle */ = function(_112/* s3JL9 */, _113/* s3JLa */){
  var _114/* s3JLc */ = B(_10Q/* GHC.List.$wspan */(_10Z/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_112/* s3JL9 */)))),
  _115/* s3JLd */ = _114/* s3JLc */.a,
  _116/* s3JLf */ = function(_117/* s3JLg */, _118/* s3JLh */){
    var _119/* s3JLk */ = new T(function(){
      var _11a/* s3JLj */ = new T(function(){
        return B(_2/* GHC.Base.++ */(_113/* s3JLa */, new T(function(){
          return B(_2/* GHC.Base.++ */(_118/* s3JLh */, _10Y/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _11a/* s3JLj */));
    },1);
    return new F(function(){return _2/* GHC.Base.++ */(_117/* s3JLg */, _119/* s3JLk */);});
  },
  _11b/* s3JLl */ = E(_114/* s3JLc */.b);
  if(!_11b/* s3JLl */._){
    return new F(function(){return _116/* s3JLf */(_115/* s3JLd */, _6/* GHC.Types.[] */);});
  }else{
    if(E(_11b/* s3JLl */.a)==124){
      return new F(function(){return _116/* s3JLf */(_115/* s3JLd */, new T2(1,_10X/* GHC.IO.Exception.untangle1 */,_11b/* s3JLl */.b));});
    }else{
      return new F(function(){return _116/* s3JLf */(_115/* s3JLd */, _6/* GHC.Types.[] */);});
    }
  }
},
_11c/* patError */ = function(_11d/* s4nFx */){
  return new F(function(){return _10O/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_111/* GHC.IO.Exception.untangle */(_11d/* s4nFx */, _10K/* Control.Exception.Base.lvl3 */));
  })), _10y/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_11e/* log2I */ = function(_11f/* s1Ju */){
  var _11g/* s1Jv */ = function(_11h/* s1Jw */, _11i/* s1Jx */){
    while(1){
      if(!B(_Ln/* GHC.Integer.Type.ltInteger */(_11h/* s1Jw */, _11f/* s1Ju */))){
        if(!B(_KR/* GHC.Integer.Type.gtInteger */(_11h/* s1Jw */, _11f/* s1Ju */))){
          if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_11h/* s1Jw */, _11f/* s1Ju */))){
            return new F(function(){return _11c/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});
          }else{
            return E(_11i/* s1Jx */);
          }
        }else{
          return _11i/* s1Jx */-1|0;
        }
      }else{
        var _11j/*  s1Jw */ = B(_JZ/* GHC.Integer.Type.shiftLInteger */(_11h/* s1Jw */, 1)),
        _11k/*  s1Jx */ = _11i/* s1Jx */+1|0;
        _11h/* s1Jw */ = _11j/*  s1Jw */;
        _11i/* s1Jx */ = _11k/*  s1Jx */;
        continue;
      }
    }
  };
  return new F(function(){return _11g/* s1Jv */(_K6/* GHC.Integer.Type.log2I1 */, 0);});
},
_11l/* integerLog2# */ = function(_11m/* s1JD */){
  var _11n/* s1JE */ = E(_11m/* s1JD */);
  if(!_11n/* s1JE */._){
    var _11o/* s1JG */ = _11n/* s1JE */.a>>>0;
    if(!_11o/* s1JG */){
      return -1;
    }else{
      var _11p/* s1JH */ = function(_11q/* s1JI */, _11r/* s1JJ */){
        while(1){
          if(_11q/* s1JI */>=_11o/* s1JG */){
            if(_11q/* s1JI */<=_11o/* s1JG */){
              if(_11q/* s1JI */!=_11o/* s1JG */){
                return new F(function(){return _11c/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_11r/* s1JJ */);
              }
            }else{
              return _11r/* s1JJ */-1|0;
            }
          }else{
            var _11s/*  s1JI */ = imul/* EXTERNAL */(_11q/* s1JI */, 2)>>>0,
            _11t/*  s1JJ */ = _11r/* s1JJ */+1|0;
            _11q/* s1JI */ = _11s/*  s1JI */;
            _11r/* s1JJ */ = _11t/*  s1JJ */;
            continue;
          }
        }
      };
      return new F(function(){return _11p/* s1JH */(1, 0);});
    }
  }else{
    return new F(function(){return _11e/* GHC.Integer.Type.log2I */(_11n/* s1JE */);});
  }
},
_11u/* integerLog2IsPowerOf2# */ = function(_11v/* s1JT */){
  var _11w/* s1JU */ = E(_11v/* s1JT */);
  if(!_11w/* s1JU */._){
    var _11x/* s1JW */ = _11w/* s1JU */.a>>>0;
    if(!_11x/* s1JW */){
      return new T2(0,-1,0);
    }else{
      var _11y/* s1JX */ = function(_11z/* s1JY */, _11A/* s1JZ */){
        while(1){
          if(_11z/* s1JY */>=_11x/* s1JW */){
            if(_11z/* s1JY */<=_11x/* s1JW */){
              if(_11z/* s1JY */!=_11x/* s1JW */){
                return new F(function(){return _11c/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_11A/* s1JZ */);
              }
            }else{
              return _11A/* s1JZ */-1|0;
            }
          }else{
            var _11B/*  s1JY */ = imul/* EXTERNAL */(_11z/* s1JY */, 2)>>>0,
            _11C/*  s1JZ */ = _11A/* s1JZ */+1|0;
            _11z/* s1JY */ = _11B/*  s1JY */;
            _11A/* s1JZ */ = _11C/*  s1JZ */;
            continue;
          }
        }
      };
      return new T2(0,B(_11y/* s1JX */(1, 0)),(_11x/* s1JW */&_11x/* s1JW */-1>>>0)>>>0&4294967295);
    }
  }else{
    var _11D/* s1Kc */ = _11w/* s1JU */.a;
    return new T2(0,B(_11l/* GHC.Integer.Type.integerLog2# */(_11w/* s1JU */)),I_compareInt/* EXTERNAL */(I_and/* EXTERNAL */(_11D/* s1Kc */, I_sub/* EXTERNAL */(_11D/* s1Kc */, I_fromInt/* EXTERNAL */(1))), 0));
  }
},
_11E/* andInteger */ = function(_11F/* s1Lf */, _11G/* s1Lg */){
  while(1){
    var _11H/* s1Lh */ = E(_11F/* s1Lf */);
    if(!_11H/* s1Lh */._){
      var _11I/* s1Li */ = _11H/* s1Lh */.a,
      _11J/* s1Lj */ = E(_11G/* s1Lg */);
      if(!_11J/* s1Lj */._){
        return new T1(0,(_11I/* s1Li */>>>0&_11J/* s1Lj */.a>>>0)>>>0&4294967295);
      }else{
        _11F/* s1Lf */ = new T1(1,I_fromInt/* EXTERNAL */(_11I/* s1Li */));
        _11G/* s1Lg */ = _11J/* s1Lj */;
        continue;
      }
    }else{
      var _11K/* s1Lu */ = E(_11G/* s1Lg */);
      if(!_11K/* s1Lu */._){
        _11F/* s1Lf */ = _11H/* s1Lh */;
        _11G/* s1Lg */ = new T1(1,I_fromInt/* EXTERNAL */(_11K/* s1Lu */.a));
        continue;
      }else{
        return new T1(1,I_and/* EXTERNAL */(_11H/* s1Lh */.a, _11K/* s1Lu */.a));
      }
    }
  }
},
_11L/* roundingMode#1 */ = new T1(0,2),
_11M/* roundingMode# */ = function(_11N/* s1Pt */, _11O/* s1Pu */){
  var _11P/* s1Pv */ = E(_11N/* s1Pt */);
  if(!_11P/* s1Pv */._){
    var _11Q/* s1Px */ = (_11P/* s1Pv */.a>>>0&(2<<_11O/* s1Pu */>>>0)-1>>>0)>>>0,
    _11R/* s1PB */ = 1<<_11O/* s1Pu */>>>0;
    return (_11R/* s1PB */<=_11Q/* s1Px */) ? (_11R/* s1PB */>=_11Q/* s1Px */) ? 1 : 2 : 0;
  }else{
    var _11S/* s1PH */ = B(_11E/* GHC.Integer.Type.andInteger */(_11P/* s1Pv */, B(_LN/* GHC.Integer.Type.minusInteger */(B(_JZ/* GHC.Integer.Type.shiftLInteger */(_11L/* GHC.Integer.Type.roundingMode#1 */, _11O/* s1Pu */)), _K6/* GHC.Integer.Type.log2I1 */)))),
    _11T/* s1PK */ = B(_JZ/* GHC.Integer.Type.shiftLInteger */(_K6/* GHC.Integer.Type.log2I1 */, _11O/* s1Pu */));
    return (!B(_KR/* GHC.Integer.Type.gtInteger */(_11T/* s1PK */, _11S/* s1PH */))) ? (!B(_Ln/* GHC.Integer.Type.ltInteger */(_11T/* s1PK */, _11S/* s1PH */))) ? 1 : 2 : 0;
  }
},
_11U/* shiftRInteger */ = function(_11V/* s1Ja */, _11W/* s1Jb */){
  while(1){
    var _11X/* s1Jc */ = E(_11V/* s1Ja */);
    if(!_11X/* s1Jc */._){
      _11V/* s1Ja */ = new T1(1,I_fromInt/* EXTERNAL */(_11X/* s1Jc */.a));
      continue;
    }else{
      return new T1(1,I_shiftRight/* EXTERNAL */(_11X/* s1Jc */.a, _11W/* s1Jb */));
    }
  }
},
_11Y/* $w$sfromRat'' */ = function(_11Z/* s18QU */, _120/* s18QV */, _121/* s18QW */, _122/* s18QX */){
  var _123/* s18QY */ = B(_11u/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_122/* s18QX */)),
  _124/* s18QZ */ = _123/* s18QY */.a;
  if(!E(_123/* s18QY */.b)){
    var _125/* s18Rp */ = B(_11l/* GHC.Integer.Type.integerLog2# */(_121/* s18QW */));
    if(_125/* s18Rp */<((_124/* s18QZ */+_11Z/* s18QU */|0)-1|0)){
      var _126/* s18Ru */ = _124/* s18QZ */+(_11Z/* s18QU */-_120/* s18QV */|0)|0;
      if(_126/* s18Ru */>0){
        if(_126/* s18Ru */>_125/* s18Rp */){
          if(_126/* s18Ru */<=(_125/* s18Rp */+1|0)){
            if(!E(B(_11u/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_121/* s18QW */)).b)){
              return 0;
            }else{
              return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(_108/* GHC.Float.$fRealDouble1 */, _11Z/* s18QU */-_120/* s18QV */|0);});
            }
          }else{
            return 0;
          }
        }else{
          var _127/* s18RI */ = B(_11U/* GHC.Integer.Type.shiftRInteger */(_121/* s18QW */, _126/* s18Ru */));
          switch(B(_11M/* GHC.Integer.Type.roundingMode# */(_121/* s18QW */, _126/* s18Ru */-1|0))){
            case 0:
              return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(_127/* s18RI */, _11Z/* s18QU */-_120/* s18QV */|0);});
              break;
            case 1:
              if(!(B(_Vj/* GHC.Integer.Type.integerToInt */(_127/* s18RI */))&1)){
                return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(_127/* s18RI */, _11Z/* s18QU */-_120/* s18QV */|0);});
              }else{
                return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(B(_K8/* GHC.Integer.Type.plusInteger */(_127/* s18RI */, _108/* GHC.Float.$fRealDouble1 */)), _11Z/* s18QU */-_120/* s18QV */|0);});
              }
              break;
            default:
              return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(B(_K8/* GHC.Integer.Type.plusInteger */(_127/* s18RI */, _108/* GHC.Float.$fRealDouble1 */)), _11Z/* s18QU */-_120/* s18QV */|0);});
          }
        }
      }else{
        return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(_121/* s18QW */, (_11Z/* s18QU */-_120/* s18QV */|0)-_126/* s18Ru */|0);});
      }
    }else{
      if(_125/* s18Rp */>=_120/* s18QV */){
        var _128/* s18RX */ = B(_11U/* GHC.Integer.Type.shiftRInteger */(_121/* s18QW */, (_125/* s18Rp */+1|0)-_120/* s18QV */|0));
        switch(B(_11M/* GHC.Integer.Type.roundingMode# */(_121/* s18QW */, _125/* s18Rp */-_120/* s18QV */|0))){
          case 0:
            return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(_128/* s18RX */, ((_125/* s18Rp */-_124/* s18QZ */|0)+1|0)-_120/* s18QV */|0);});
            break;
          case 2:
            return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(B(_K8/* GHC.Integer.Type.plusInteger */(_128/* s18RX */, _108/* GHC.Float.$fRealDouble1 */)), ((_125/* s18Rp */-_124/* s18QZ */|0)+1|0)-_120/* s18QV */|0);});
            break;
          default:
            if(!(B(_Vj/* GHC.Integer.Type.integerToInt */(_128/* s18RX */))&1)){
              return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(_128/* s18RX */, ((_125/* s18Rp */-_124/* s18QZ */|0)+1|0)-_120/* s18QV */|0);});
            }else{
              return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(B(_K8/* GHC.Integer.Type.plusInteger */(_128/* s18RX */, _108/* GHC.Float.$fRealDouble1 */)), ((_125/* s18Rp */-_124/* s18QZ */|0)+1|0)-_120/* s18QV */|0);});
            }
        }
      }else{
        return new F(function(){return _109/* GHC.Integer.Type.encodeDoubleInteger */(_121/* s18QW */,  -_124/* s18QZ */);});
      }
    }
  }else{
    var _129/* s18R3 */ = B(_11l/* GHC.Integer.Type.integerLog2# */(_121/* s18QW */))-_124/* s18QZ */|0,
    _12a/* s18R4 */ = function(_12b/* s18R5 */){
      var _12c/* s18R6 */ = function(_12d/* s18R7 */, _12e/* s18R8 */){
        if(!B(_Wt/* GHC.Integer.Type.leInteger */(B(_JZ/* GHC.Integer.Type.shiftLInteger */(_12e/* s18R8 */, _120/* s18QV */)), _12d/* s18R7 */))){
          return new F(function(){return _10e/* GHC.Float.$w$j1 */(_12b/* s18R5 */-_120/* s18QV */|0, _12d/* s18R7 */, _12e/* s18R8 */);});
        }else{
          return new F(function(){return _10e/* GHC.Float.$w$j1 */((_12b/* s18R5 */-_120/* s18QV */|0)+1|0, _12d/* s18R7 */, B(_JZ/* GHC.Integer.Type.shiftLInteger */(_12e/* s18R8 */, 1)));});
        }
      };
      if(_12b/* s18R5 */>=_120/* s18QV */){
        if(_12b/* s18R5 */!=_120/* s18QV */){
          return new F(function(){return _12c/* s18R6 */(_121/* s18QW */, new T(function(){
            return B(_JZ/* GHC.Integer.Type.shiftLInteger */(_122/* s18QX */, _12b/* s18R5 */-_120/* s18QV */|0));
          }));});
        }else{
          return new F(function(){return _12c/* s18R6 */(_121/* s18QW */, _122/* s18QX */);});
        }
      }else{
        return new F(function(){return _12c/* s18R6 */(new T(function(){
          return B(_JZ/* GHC.Integer.Type.shiftLInteger */(_121/* s18QW */, _120/* s18QV */-_12b/* s18R5 */|0));
        }), _122/* s18QX */);});
      }
    };
    if(_11Z/* s18QU */>_129/* s18R3 */){
      return new F(function(){return _12a/* s18R4 */(_11Z/* s18QU */);});
    }else{
      return new F(function(){return _12a/* s18R4 */(_129/* s18R3 */);});
    }
  }
},
_12f/* rationalToDouble1 */ = new T(function(){
  return 0/0;
}),
_12g/* rationalToDouble2 */ = new T(function(){
  return -1/0;
}),
_12h/* rationalToDouble3 */ = new T(function(){
  return 1/0;
}),
_12i/* rationalToDouble4 */ = 0,
_12j/* rationalToDouble */ = function(_12k/* s197E */, _12l/* s197F */){
  if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_12l/* s197F */, _10d/* GHC.Float.rationalToDouble5 */))){
    if(!B(_Rk/* GHC.Integer.Type.eqInteger */(_12k/* s197E */, _10d/* GHC.Float.rationalToDouble5 */))){
      if(!B(_Ln/* GHC.Integer.Type.ltInteger */(_12k/* s197E */, _10d/* GHC.Float.rationalToDouble5 */))){
        return new F(function(){return _11Y/* GHC.Float.$w$sfromRat'' */(-1021, 53, _12k/* s197E */, _12l/* s197F */);});
      }else{
        return  -B(_11Y/* GHC.Float.$w$sfromRat'' */(-1021, 53, B(_Ki/* GHC.Integer.Type.negateInteger */(_12k/* s197E */)), _12l/* s197F */));
      }
    }else{
      return E(_12i/* GHC.Float.rationalToDouble4 */);
    }
  }else{
    return (!B(_Rk/* GHC.Integer.Type.eqInteger */(_12k/* s197E */, _10d/* GHC.Float.rationalToDouble5 */))) ? (!B(_Ln/* GHC.Integer.Type.ltInteger */(_12k/* s197E */, _10d/* GHC.Float.rationalToDouble5 */))) ? E(_12h/* GHC.Float.rationalToDouble3 */) : E(_12g/* GHC.Float.rationalToDouble2 */) : E(_12f/* GHC.Float.rationalToDouble1 */);
  }
},
_12m/* $fFractionalDouble_$cfromRational */ = function(_12n/* s197P */){
  var _12o/* s197Q */ = E(_12n/* s197P */);
  return new F(function(){return _12j/* GHC.Float.rationalToDouble */(_12o/* s197Q */.a, _12o/* s197Q */.b);});
},
_12p/* $fFractionalDouble_$crecip */ = function(_12q/* s191m */){
  return 1/E(_12q/* s191m */);
},
_12r/* $fNumDouble_$cabs */ = function(_12s/* s190N */){
  var _12t/* s190O */ = E(_12s/* s190N */),
  _12u/* s190Q */ = E(_12t/* s190O */);
  return (_12u/* s190Q */==0) ? E(_12i/* GHC.Float.rationalToDouble4 */) : (_12u/* s190Q */<=0) ?  -_12u/* s190Q */ : E(_12t/* s190O */);
},
_12v/* $fNumDouble_$cfromInteger */ = function(_12w/* s190E */){
  return new F(function(){return _SW/* GHC.Integer.Type.doubleFromInteger */(_12w/* s190E */);});
},
_12x/* $fNumDouble1 */ = 1,
_12y/* $fNumDouble2 */ = -1,
_12z/* $fNumDouble_$csignum */ = function(_12A/* s190G */){
  var _12B/* s190H */ = E(_12A/* s190G */);
  return (_12B/* s190H */<=0) ? (_12B/* s190H */>=0) ? E(_12B/* s190H */) : E(_12y/* GHC.Float.$fNumDouble2 */) : E(_12x/* GHC.Float.$fNumDouble1 */);
},
_12C/* minusDouble */ = function(_12D/* s18yR */, _12E/* s18yS */){
  return E(_12D/* s18yR */)-E(_12E/* s18yS */);
},
_12F/* $fNumDouble */ = {_:0,a:_th/* GHC.Float.plusDouble */,b:_12C/* GHC.Float.minusDouble */,c:_Ag/* GHC.Float.timesDouble */,d:_FT/* GHC.Float.negateDouble */,e:_12r/* GHC.Float.$fNumDouble_$cabs */,f:_12z/* GHC.Float.$fNumDouble_$csignum */,g:_12v/* GHC.Float.$fNumDouble_$cfromInteger */},
_12G/* $fFractionalDouble */ = new T4(0,_12F/* GHC.Float.$fNumDouble */,_iE/* GHC.Float.divideDouble */,_12p/* GHC.Float.$fFractionalDouble_$crecip */,_12m/* GHC.Float.$fFractionalDouble_$cfromRational */),
_12H/* $fEqDouble_$c/= */ = function(_12I/* scFX */, _12J/* scFY */){
  return (E(_12I/* scFX */)!=E(_12J/* scFY */)) ? true : false;
},
_12K/* $fEqDouble_$c== */ = function(_12L/* scFQ */, _12M/* scFR */){
  return E(_12L/* scFQ */)==E(_12M/* scFR */);
},
_12N/* $fEqDouble */ = new T2(0,_12K/* GHC.Classes.$fEqDouble_$c== */,_12H/* GHC.Classes.$fEqDouble_$c/= */),
_12O/* $fOrdDouble_$c< */ = function(_12P/* scIa */, _12Q/* scIb */){
  return E(_12P/* scIa */)<E(_12Q/* scIb */);
},
_12R/* $fOrdDouble_$c<= */ = function(_12S/* scI3 */, _12T/* scI4 */){
  return E(_12S/* scI3 */)<=E(_12T/* scI4 */);
},
_12U/* $fOrdDouble_$c> */ = function(_12V/* scHW */, _12W/* scHX */){
  return E(_12V/* scHW */)>E(_12W/* scHX */);
},
_12X/* $fOrdDouble_$c>= */ = function(_12Y/* scHP */, _12Z/* scHQ */){
  return E(_12Y/* scHP */)>=E(_12Z/* scHQ */);
},
_130/* $fOrdDouble_$ccompare */ = function(_131/* scIh */, _132/* scIi */){
  var _133/* scIj */ = E(_131/* scIh */),
  _134/* scIl */ = E(_132/* scIi */);
  return (_133/* scIj */>=_134/* scIl */) ? (_133/* scIj */!=_134/* scIl */) ? 2 : 1 : 0;
},
_135/* $fOrdDouble_$cmax */ = function(_136/* scIz */, _137/* scIA */){
  var _138/* scIB */ = E(_136/* scIz */),
  _139/* scID */ = E(_137/* scIA */);
  return (_138/* scIB */>_139/* scID */) ? E(_138/* scIB */) : E(_139/* scID */);
},
_13a/* $fOrdDouble_$cmin */ = function(_13b/* scIr */, _13c/* scIs */){
  var _13d/* scIt */ = E(_13b/* scIr */),
  _13e/* scIv */ = E(_13c/* scIs */);
  return (_13d/* scIt */>_13e/* scIv */) ? E(_13e/* scIv */) : E(_13d/* scIt */);
},
_13f/* $fOrdDouble */ = {_:0,a:_12N/* GHC.Classes.$fEqDouble */,b:_130/* GHC.Classes.$fOrdDouble_$ccompare */,c:_12O/* GHC.Classes.$fOrdDouble_$c< */,d:_12R/* GHC.Classes.$fOrdDouble_$c<= */,e:_12U/* GHC.Classes.$fOrdDouble_$c> */,f:_12X/* GHC.Classes.$fOrdDouble_$c>= */,g:_135/* GHC.Classes.$fOrdDouble_$cmax */,h:_13a/* GHC.Classes.$fOrdDouble_$cmin */},
_13g/* lvl8 */ = -1,
_13h/* $p1Fractional */ = function(_13i/* svdN */){
  return E(E(_13i/* svdN */).a);
},
_13j/* + */ = function(_13k/* s6Fy */){
  return E(E(_13k/* s6Fy */).a);
},
_13l/* $wnumericEnumFrom */ = function(_13m/* svLB */, _13n/* svLC */){
  var _13o/* svLD */ = E(_13n/* svLC */),
  _13p/* svLK */ = new T(function(){
    var _13q/* svLE */ = B(_13h/* GHC.Real.$p1Fractional */(_13m/* svLB */)),
    _13r/* svLH */ = B(_13l/* GHC.Real.$wnumericEnumFrom */(_13m/* svLB */, B(A3(_13j/* GHC.Num.+ */,_13q/* svLE */, _13o/* svLD */, new T(function(){
      return B(A2(_KP/* GHC.Num.fromInteger */,_13q/* svLE */, _KK/* GHC.Real.$fEnumRatio1 */));
    })))));
    return new T2(1,_13r/* svLH */.a,_13r/* svLH */.b);
  });
  return new T2(0,_13o/* svLD */,_13p/* svLK */);
},
_13s/* / */ = function(_13t/* svdT */){
  return E(E(_13t/* svdT */).b);
},
_13u/* <= */ = function(_13v/* scCl */){
  return E(E(_13v/* scCl */).d);
},
_13w/* takeWhile */ = function(_13x/* s9yw */, _13y/* s9yx */){
  var _13z/* s9yy */ = E(_13y/* s9yx */);
  if(!_13z/* s9yy */._){
    return __Z/* EXTERNAL */;
  }else{
    var _13A/* s9yz */ = _13z/* s9yy */.a;
    return (!B(A1(_13x/* s9yw */,_13A/* s9yz */))) ? __Z/* EXTERNAL */ : new T2(1,_13A/* s9yz */,new T(function(){
      return B(_13w/* GHC.List.takeWhile */(_13x/* s9yw */, _13z/* s9yy */.b));
    }));
  }
},
_13B/* numericEnumFromTo */ = function(_13C/* svMm */, _13D/* svMn */, _13E/* svMo */, _13F/* svMp */){
  var _13G/* svMq */ = B(_13l/* GHC.Real.$wnumericEnumFrom */(_13D/* svMn */, _13E/* svMo */)),
  _13H/* svMt */ = new T(function(){
    var _13I/* svMu */ = B(_13h/* GHC.Real.$p1Fractional */(_13D/* svMn */)),
    _13J/* svMx */ = new T(function(){
      return B(A3(_13s/* GHC.Real./ */,_13D/* svMn */, new T(function(){
        return B(A2(_KP/* GHC.Num.fromInteger */,_13I/* svMu */, _KK/* GHC.Real.$fEnumRatio1 */));
      }), new T(function(){
        return B(A2(_KP/* GHC.Num.fromInteger */,_13I/* svMu */, _Sl/* GHC.Real.even2 */));
      })));
    });
    return B(A3(_13j/* GHC.Num.+ */,_13I/* svMu */, _13F/* svMp */, _13J/* svMx */));
  });
  return new F(function(){return _13w/* GHC.List.takeWhile */(function(_13K/* svMy */){
    return new F(function(){return A3(_13u/* GHC.Classes.<= */,_13C/* svMm */, _13K/* svMy */, _13H/* svMt */);});
  }, new T2(1,_13G/* svMq */.a,_13G/* svMq */.b));});
},
_13L/* x */ = 1,
_13M/* lvl9 */ = new T(function(){
  return B(_13B/* GHC.Real.numericEnumFromTo */(_13f/* GHC.Classes.$fOrdDouble */, _12G/* GHC.Float.$fFractionalDouble */, _13g/* Motion.Change.lvl8 */, _13L/* Motion.Change.x */));
}),
_13N/* go */ = function(_13O/* s826 */){
  var _13P/* s827 */ = E(_13O/* s826 */);
  if(!_13P/* s827 */._){
    return __Z/* EXTERNAL */;
  }else{
    var _13Q/* s82a */ = new T(function(){
      return E(_13P/* s827 */.a)*100;
    }),
    _13R/* s82e */ = new T(function(){
      return B(_13N/* Motion.Change.go */(_13P/* s827 */.b));
    }),
    _13S/* s82f */ = function(_13T/* s82g */){
      var _13U/* s82h */ = E(_13T/* s82g */);
      return (_13U/* s82h */._==0) ? E(_13R/* s82e */) : new T2(1,new T2(0,_13Q/* s82a */,new T(function(){
        return E(_13U/* s82h */.a)*100;
      })),new T(function(){
        return B(_13S/* s82f */(_13U/* s82h */.b));
      }));
    };
    return new F(function(){return _13S/* s82f */(_13M/* Motion.Change.lvl9 */);});
  }
},
_13V/* lvl10 */ = new T(function(){
  return B(_13N/* Motion.Change.go */(_13M/* Motion.Change.lvl9 */));
}),
_13W/* lvl11 */ = 1.5,
_13X/* lvl12 */ = 15,
_13Y/* lvl13 */ = 50,
_13Z/* lvl14 */ = 100,
_140/* lvl15 */ = new T4(0,_13L/* Motion.Change.x */,_13L/* Motion.Change.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_141/* lvl16 */ = new T2(0,_13L/* Motion.Change.x */,_140/* Motion.Change.lvl15 */),
_142/* lvl17 */ = new T2(0,_141/* Motion.Change.lvl16 */,_6/* GHC.Types.[] */),
_143/* a8 */ = 100,
_144/* lvl5 */ = new T1(0,_143/* Motion.Change.a8 */),
_145/* lvl6 */ = new T2(0,_144/* Motion.Change.lvl5 */,_144/* Motion.Change.lvl5 */),
_146/* a9 */ = 3,
_147/* lvl7 */ = new T1(0,_146/* Motion.Change.a9 */),
_148/* valueIO1 */ = function(_149/* sl3L */, _/* EXTERNAL */){
  var _14a/* sl3N */ = E(_149/* sl3L */);
  switch(_14a/* sl3N */._){
    case 0:
      return new T1(1,_14a/* sl3N */.a);
    case 1:
      var _14b/* sl3R */ = B(A1(_14a/* sl3N */.a,_/* EXTERNAL */));
      return new T1(1,_14b/* sl3R */);
    case 2:
      var _14c/* sl43 */ = rMV/* EXTERNAL */(E(E(_14a/* sl3N */.a).c)),
      _14d/* sl46 */ = E(_14c/* sl43 */);
      if(!_14d/* sl46 */._){
        var _14e/* sl4a */ = new T(function(){
          return B(A1(_14a/* sl3N */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_14d/* sl46 */.a));
          })));
        });
        return new T1(1,_14e/* sl4a */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
      break;
    default:
      var _14f/* sl4l */ = rMV/* EXTERNAL */(E(E(_14a/* sl3N */.a).c)),
      _14g/* sl4o */ = E(_14f/* sl4l */);
      if(!_14g/* sl4o */._){
        var _14h/* sl4u */ = B(A2(_14a/* sl3N */.b,E(_14g/* sl4o */.a).a, _/* EXTERNAL */));
        return new T1(1,_14h/* sl4u */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
  }
},
_14i/* changeMot1 */ = function(_14j/* s83d */, _14k/* s83e */){
  var _14l/* s83f */ = new T(function(){
    return B(_YQ/* Motion.Change.$sreplicateM2 */(_103/* Motion.Change.a7 */, _14k/* s83e */));
  }),
  _14m/* s83g */ = function(_14n/* s83h */, _14o/* s83i */){
    var _14p/* s83j */ = E(_14n/* s83h */);
    if(!_14p/* s83j */._){
      return E(_ZQ/* Motion.Change.a2 */);
    }else{
      var _14q/* s83m */ = E(_14o/* s83i */);
      if(!_14q/* s83m */._){
        return E(_ZQ/* Motion.Change.a2 */);
      }else{
        var _14r/* s83p */ = E(_14q/* s83m */.a),
        _14s/* s83s */ = new T(function(){
          return B(_Ig/* Core.Ease.morph */(_14p/* s83j */.a));
        }),
        _14t/* s83v */ = B(_rn/* Control.Monad.Skeleton.bone */(new T1(1,function(_/* EXTERNAL */){
          return new F(function(){return _148/* Core.Ease.valueIO1 */(_14s/* s83s */, _/* EXTERNAL */);});
        }))),
        _14u/* s83y */ = new T(function(){
          return B(_14m/* s83g */(_14p/* s83j */.b, _14q/* s83m */.b));
        }),
        _14v/* s83z */ = new T(function(){
          return B(_rr/* Core.Render.Internal.fill1 */(_14j/* s83d */, new T(function(){
            var _14w/* s83C */ = B(_GE/* Core.Shape.Internal.$wcenterRect */(new T1(0,_14r/* s83p */.a), new T1(0,_14r/* s83p */.b), _144/* Motion.Change.lvl5 */, _144/* Motion.Change.lvl5 */));
            return new T3(0,_14w/* s83C */.a,_14w/* s83C */.b,_14w/* s83C */.c);
          })));
        });
        return new T2(0,E(_14t/* s83v */.a),E(new T2(2,new T2(2,_14t/* s83v */.b,new T1(1,function(_14x/* s83H */){
          var _14y/* s83I */ = E(_14x/* s83H */);
          return (_14y/* s83I */._==0) ? E(_Z5/* Motion.Change.$swhen1 */) : (!E(_14y/* s83I */.a)) ? E(_Z5/* Motion.Change.$swhen1 */) : E(_14v/* s83z */);
        })),new T1(1,function(_14z/* s83O */){
          return E(_14u/* s83y */);
        }))));
      }
    }
  },
  _14A/* s85x */ = function(_14B/* s83S */){
    var _14C/* s85w */ = function(_14D/* s83T */){
      var _14E/* s83U */ = E(_14D/* s83T */),
      _14F/* s83V */ = _14E/* s83U */.a,
      _14G/* s85v */ = function(_/* EXTERNAL */){
        var _14H/* s83Y */ = nMV/* EXTERNAL */(_142/* Motion.Change.lvl17 */);
        return new T(function(){
          var _14I/* s842 */ = new T(function(){
            return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _104/* Motion.Change.dur */, _105/* Motion.Change.e */, _14H/* s83Y */, _13L/* Motion.Change.x */, _A2/* Core.Ease.easeTo1 */));
          }),
          _14J/* s843 */ = new T(function(){
            return B(_jD/* Core.Ease.$wforceTo */(_14H/* s83Y */, _13W/* Motion.Change.lvl11 */));
          }),
          _14K/* s844 */ = function(_14L/* s845 */, _14M/* s846 */){
            var _14N/* s847 */ = function(_14O/* s848 */){
              return new F(function(){return _tl/* Core.World.Internal.sleep1 */(_13X/* Motion.Change.lvl12 */, E(_14O/* s848 */).b, _14M/* s846 */);});
            },
            _14P/* s84c */ = function(_14Q/* s84d */){
              return new F(function(){return A2(_14I/* s842 */,E(_14Q/* s84d */).b, _14N/* s847 */);});
            };
            return new F(function(){return _Zw/* Motion.Change.a10 */(_14F/* s83V */, _14L/* s845 */, function(_14R/* s84h */){
              return new F(function(){return A2(_14J/* s843 */,E(_14R/* s84h */).b, _14P/* s84c */);});
            });});
          },
          _14S/* s84m */ = new T(function(){
            var _14T/* s84o */ = function(_14U/* s84p */){
              var _14V/* s84q */ = E(_14U/* s84p */);
              return (_14V/* s84q */==1) ? E(new T2(1,_14K/* s844 */,_6/* GHC.Types.[] */)) : new T2(1,_14K/* s844 */,new T(function(){
                return B(_14T/* s84o */(_14V/* s84q */-1|0));
              }));
            };
            return B(_14T/* s84o */(4));
          }),
          _14W/* s84t */ = function(_14X/* s84u */){
            var _14Y/* s84v */ = new T(function(){
              return B(_YQ/* Motion.Change.$sreplicateM2 */(_14S/* s84m */, _14X/* s84u */));
            }),
            _14Z/* s85g */ = function(_150/* s84w */){
              var _151/* s84x */ = function(_152/* s84y */){
                return new F(function(){return A2(_14W/* s84t */,E(_152/* s84y */).b, _150/* s84w */);});
              },
              _153/* s84C */ = function(_154/* s84D */){
                return new F(function(){return _tl/* Core.World.Internal.sleep1 */(_13Z/* Motion.Change.lvl14 */, E(_154/* s84D */).b, _151/* s84x */);});
              },
              _155/* s84H */ = function(_156/* s84I */){
                return new F(function(){return A2(_14I/* s842 */,E(_156/* s84I */).b, _153/* s84C */);});
              },
              _157/* s84M */ = function(_158/* s84N */){
                return new F(function(){return A2(_14J/* s843 */,E(_158/* s84N */).b, _155/* s84H */);});
              },
              _159/* s84R */ = function(_15a/* s84S */){
                return new F(function(){return _Zw/* Motion.Change.a10 */(_14F/* s83V */, E(_15a/* s84S */).b, _157/* s84M */);});
              },
              _15b/* s84W */ = function(_15c/* s84X */){
                return new F(function(){return _tl/* Core.World.Internal.sleep1 */(_13Y/* Motion.Change.lvl13 */, E(_15c/* s84X */).b, _159/* s84R */);});
              },
              _15d/* s851 */ = function(_15e/* s852 */){
                return new F(function(){return A2(_14I/* s842 */,E(_15e/* s852 */).b, _15b/* s84W */);});
              },
              _15f/* s856 */ = function(_15g/* s857 */){
                return new F(function(){return A2(_14J/* s843 */,E(_15g/* s857 */).b, _15d/* s851 */);});
              };
              return new F(function(){return A1(_14Y/* s84v */,function(_15h/* s85b */){
                return new F(function(){return _Zw/* Motion.Change.a10 */(_14F/* s83V */, E(_15h/* s85b */).b, _15f/* s856 */);});
              });});
            };
            return E(_14Z/* s85g */);
          },
          _15i/* s85r */ = new T(function(){
            var _15j/* s85p */ = new T(function(){
              var _15k/* s85h */ = new T3(0,_104/* Motion.Change.dur */,_105/* Motion.Change.e */,_14H/* s83Y */);
              return B(_rn/* Control.Monad.Skeleton.bone */(new T3(7,new T2(0,new T(function(){
                return B(_s6/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, new T2(2,_15k/* s85h */,_2E/* GHC.Base.id */), _147/* Motion.Change.lvl7 */));
              }),new T(function(){
                return B(_s6/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, new T2(2,_15k/* s85h */,_2E/* GHC.Base.id */), _147/* Motion.Change.lvl7 */));
              })),new T(function(){
                return B(_14m/* s83g */(_14F/* s83V */, _13V/* Motion.Change.lvl10 */));
              }),_7/* GHC.Tuple.() */)));
            });
            return B(_rn/* Control.Monad.Skeleton.bone */(new T3(5,_145/* Motion.Change.lvl6 */,_15j/* s85p */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_14B/* s83S */,new T2(0,new T2(0,_15i/* s85r */,_14W/* s84t */),_14E/* s83U */.b)));
        });
      };
      return new T1(0,_14G/* s85v */);
    };
    return new F(function(){return A1(_14l/* s83f */,_14C/* s85w */);});
  };
  return E(_14A/* s85x */);
},
_15l/* lvl50 */ = 0.1,
_15m/* lvl51 */ = new T1(0,_15l/* Motion.Main.lvl50 */),
_15n/* lvl52 */ = new T4(0,_15m/* Motion.Main.lvl51 */,_J7/* Motion.Main.lvl41 */,_J7/* Motion.Main.lvl41 */,_Ab/* Motion.Main.lvl11 */),
_15o/* lvl53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Change"));
}),
_15p/* lvl54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("easeOutExpo"));
}),
_15q/* lvl55 */ = new T(function(){
  return B(_Fc/* Motion.Main.consView */(_15n/* Motion.Main.lvl52 */, _14i/* Motion.Change.changeMot1 */, _15o/* Motion.Main.lvl53 */, _15p/* Motion.Main.lvl54 */));
}),
_15r/* lvl56 */ = new T4(0,_Ab/* Motion.Main.lvl11 */,_As/* Motion.Main.lvl23 */,_yJ/* Motion.Main.lvl4 */,_Ab/* Motion.Main.lvl11 */),
_15s/* lvl57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Trot"));
}),
_15t/* lvl58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("rotateAt corner easeInCubic & smoothStep scroll"));
}),
_15u/* cubic */ = function(_15v/* slb1 */, _15w/* slb2 */){
  var _15x/* slb3 */ = B(A1(_15v/* slb1 */,_15w/* slb2 */));
  return _15x/* slb3 */*_15x/* slb3 */*_15x/* slb3 */;
},
_15y/* dur */ = 40,
_15z/* $we */ = function(_15A/* s6Uc */, _15B/* s6Ud */){
  if(_15B/* s6Ud */>=0.5){
    var _15C/* s6Ug */ = 2-(_15B/* s6Ud */+_15B/* s6Ud */);
    return 1-B(A1(_15A/* s6Uc */,_15C/* s6Ug */*_15C/* s6Ug */*(3-_15C/* s6Ug */)/2))/2;
  }else{
    var _15D/* s6Uq */ = _15B/* s6Ud */+_15B/* s6Ud */;
    return B(A1(_15A/* s6Uc */,_15D/* s6Uq */*_15D/* s6Uq */*(3-_15D/* s6Uq */)/2))/2;
  }
},
_15E/* e */ = function(_15F/* s6Uy */, _15G/* s6Uz */){
  return new F(function(){return _15z/* Motion.Trot.$we */(_15F/* s6Uy */, E(_15G/* s6Uz */));});
},
_15H/* x */ = 0,
_15I/* lvl */ = new T1(0,_15H/* Motion.Trot.x */),
_15J/* lvl10 */ = -100,
_15K/* lvl11 */ = new T1(0,_15J/* Motion.Trot.lvl10 */),
_15L/* lvl12 */ = -200,
_15M/* lvl13 */ = new T1(0,_15L/* Motion.Trot.lvl12 */),
_15N/* lvl14 */ = new T2(0,_15K/* Motion.Trot.lvl11 */,_15M/* Motion.Trot.lvl13 */),
_15O/* lvl15 */ = new T4(0,_15H/* Motion.Trot.x */,_15H/* Motion.Trot.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_15P/* lvl16 */ = new T2(0,_15H/* Motion.Trot.x */,_15O/* Motion.Trot.lvl15 */),
_15Q/* lvl17 */ = new T2(0,_15P/* Motion.Trot.lvl16 */,_6/* GHC.Types.[] */),
_15R/* a3 */ = 25,
_15S/* lvl3 */ = new T1(0,_15R/* Motion.Trot.a3 */),
_15T/* a4 */ = 125,
_15U/* lvl4 */ = new T1(0,_15T/* Motion.Trot.a4 */),
_15V/* a5 */ = 75,
_15W/* lvl5 */ = new T1(0,_15V/* Motion.Trot.a5 */),
_15X/* lvl6 */ = new T(function(){
  var _15Y/* s6UD */ = B(_kr/* Core.Shape.Internal.$wrect */(_15S/* Motion.Trot.lvl3 */, _15U/* Motion.Trot.lvl4 */, _15W/* Motion.Trot.lvl5 */, _15W/* Motion.Trot.lvl5 */));
  return new T3(0,_15Y/* s6UD */.a,_15Y/* s6UD */.b,_15Y/* s6UD */.c);
}),
_15Z/* lvl7 */ = 1.5707963267948966,
_160/* lvl8 */ = -75,
_161/* a1 */ = 100,
_162/* lvl1 */ = new T1(0,_161/* Motion.Trot.a1 */),
_163/* a2 */ = 200,
_164/* lvl2 */ = new T1(0,_163/* Motion.Trot.a2 */),
_165/* lvl9 */ = new T2(0,_162/* Motion.Trot.lvl1 */,_164/* Motion.Trot.lvl2 */),
_166/* trotMot */ = function(_167/* s6UH */){
  var _168/* s6UI */ = new T(function(){
    return B(_rn/* Control.Monad.Skeleton.bone */(new T3(5,_15N/* Motion.Trot.lvl14 */,new T(function(){
      return B(_rr/* Core.Render.Internal.fill1 */(_167/* s6UH */, _15X/* Motion.Trot.lvl6 */));
    }),_7/* GHC.Tuple.() */)));
  }),
  _169/* s6VR */ = function(_16a/* s6UL */, _16b/* s6UM */){
    var _16c/* s6VQ */ = function(_/* EXTERNAL */){
      var _16d/* s6UO */ = nMV/* EXTERNAL */(_15Q/* Motion.Trot.lvl17 */),
      _16e/* s6UQ */ = _16d/* s6UO */,
      _16f/* s6US */ = new T(function(){
        return B(_jD/* Core.Ease.$wforceTo */(_16e/* s6UQ */, _15H/* Motion.Trot.x */));
      }),
      _16g/* s6UT */ = function(_16h/* s6UU */){
        return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _15y/* Motion.Trot.dur */, _15u/* Core.Ease.cubic */, _16e/* s6UQ */, _15Z/* Motion.Trot.lvl7 */, function(_16i/* s6UV */){
          return E(_16h/* s6UU */);
        });});
      },
      _16j/* s6VO */ = function(_/* EXTERNAL */){
        var _16k/* s6UY */ = nMV/* EXTERNAL */(_15Q/* Motion.Trot.lvl17 */),
        _16l/* s6V0 */ = _16k/* s6UY */;
        return new T(function(){
          var _16m/* s6V2 */ = new T(function(){
            return B(_jD/* Core.Ease.$wforceTo */(_16l/* s6V0 */, _15H/* Motion.Trot.x */));
          }),
          _16n/* s6V3 */ = function(_16o/* s6V4 */){
            return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _15y/* Motion.Trot.dur */, _15E/* Motion.Trot.e */, _16l/* s6V0 */, _160/* Motion.Trot.lvl8 */, function(_16p/* s6V5 */){
              return E(_16o/* s6V4 */);
            });});
          },
          _16q/* s6V7 */ = function(_16r/* s6V8 */){
            var _16s/* s6V9 */ = new T(function(){
              return B(A1(_16f/* s6US */,_16r/* s6V8 */));
            }),
            _16t/* s6Vz */ = function(_16u/* s6Va */){
              var _16v/* s6Vb */ = function(_16w/* s6Vc */){
                return new F(function(){return A2(_16q/* s6V7 */,E(_16w/* s6Vc */).b, _16u/* s6Va */);});
              },
              _16x/* s6Vg */ = function(_16y/* s6Vh */){
                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_16n/* s6V3 */, E(_16y/* s6Vh */).b, _16v/* s6Vb */)));
              },
              _16z/* s6Vn */ = function(_16A/* s6Vo */){
                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_16g/* s6UT */, E(_16A/* s6Vo */).b, _16x/* s6Vg */)));
              };
              return new F(function(){return A1(_16s/* s6V9 */,function(_16B/* s6Vu */){
                return new F(function(){return A2(_16m/* s6V2 */,E(_16B/* s6Vu */).b, _16z/* s6Vn */);});
              });});
            };
            return E(_16t/* s6Vz */);
          },
          _16C/* s6VK */ = new T(function(){
            var _16D/* s6VI */ = new T(function(){
              return B(_rn/* Control.Monad.Skeleton.bone */(new T3(5,_165/* Motion.Trot.lvl9 */,new T(function(){
                return B(_rn/* Control.Monad.Skeleton.bone */(new T3(6,new T2(2,new T3(0,_15y/* Motion.Trot.dur */,_15u/* Core.Ease.cubic */,_16e/* s6UQ */),_2E/* GHC.Base.id */),_168/* s6UI */,_7/* GHC.Tuple.() */)));
              }),_7/* GHC.Tuple.() */)));
            });
            return B(_rn/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,new T2(2,new T3(0,_15y/* Motion.Trot.dur */,_15E/* Motion.Trot.e */,_16l/* s6V0 */),_2E/* GHC.Base.id */),_15I/* Motion.Trot.lvl */),_16D/* s6VI */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_16b/* s6UM */,new T2(0,new T2(0,_16C/* s6VK */,_16q/* s6V7 */),_16a/* s6UL */)));
        });
      };
      return new T1(0,_16j/* s6VO */);
    };
    return new T1(0,_16c/* s6VQ */);
  };
  return E(_169/* s6VR */);
},
_16E/* lvl59 */ = new T(function(){
  return B(_Fc/* Motion.Main.consView */(_15r/* Motion.Main.lvl56 */, _166/* Motion.Trot.trotMot */, _15s/* Motion.Main.lvl57 */, _15t/* Motion.Main.lvl58 */));
}),
_16F/* lvl60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("height"));
}),
_16G/* lvl61 */ = 1,
_16H/* lvl62 */ = new T1(1,_6/* GHC.Types.[] */),
_16I/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.scale(x,y);})");
}),
_16J/* f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,rad){ctx.rotate(rad);})");
}),
_16K/* f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.translate(x,y);})");
}),
_16L/* f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})");
}),
_16M/* render2 */ = function(_16N/*  sFRJ */, _16O/*  sFRK */, _/* EXTERNAL */){
  while(1){
    var _16P/*  render2 */ = B((function(_16Q/* sFRJ */, _16R/* sFRK */, _/* EXTERNAL */){
      var _16S/* sFRM */ = B(_fo/* Control.Monad.Skeleton.debone */(_16Q/* sFRJ */));
      if(!_16S/* sFRM */._){
        return _16S/* sFRM */.a;
      }else{
        var _16T/* sFRP */ = _16S/* sFRM */.b,
        _16U/* sFRQ */ = E(_16S/* sFRM */.a);
        switch(_16U/* sFRQ */._){
          case 0:
            var _16V/* sFRT */ = B(A2(_16U/* sFRQ */.a,_16R/* sFRK */, _/* EXTERNAL */)),
            _16W/*   sFRK */ = _16R/* sFRK */;
            _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16U/* sFRQ */.b));
            _16O/*  sFRK */ = _16W/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 1:
            var _16X/* sFRY */ = B(A1(_16U/* sFRQ */.a,_/* EXTERNAL */)),
            _16W/*   sFRK */ = _16R/* sFRK */;
            _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16X/* sFRY */));
            _16O/*  sFRK */ = _16W/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 2:
            var _16W/*   sFRK */ = _16R/* sFRK */;
            _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16U/* sFRQ */.b));
            _16O/*  sFRK */ = _16W/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 3:
            var _16Y/* sFS8 */ = B(_16M/* Core.Render.Internal.render2 */(_16U/* sFRQ */.b, _16U/* sFRQ */.a, _/* EXTERNAL */)),
            _16W/*   sFRK */ = _16R/* sFRK */;
            _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16U/* sFRQ */.c));
            _16O/*  sFRK */ = _16W/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 4:
            var _16Z/* sFSj */ = _16U/* sFRQ */.h,
            _170/* sFSk */ = function(_171/* sFSl */, _/* EXTERNAL */){
              var _172/* sFTp */ = function(_173/* sFSn */, _/* EXTERNAL */){
                var _174/* sFTo */ = function(_175/* sFSp */, _/* EXTERNAL */){
                  var _176/* sFTn */ = function(_177/* sFSr */, _/* EXTERNAL */){
                    var _178/* sFTm */ = function(_179/* sFSt */, _/* EXTERNAL */){
                      return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_16U/* sFRQ */.f, function(_17a/* sFSv */, _/* EXTERNAL */){
                        var _17b/* sFSx */ = E(_16R/* sFRK */),
                        _17c/* sFSC */ = __app1/* EXTERNAL */(E(_x1/* Core.Render.Internal.clip_f4 */), _17b/* sFSx */),
                        _17d/* sFT9 */ = __apply/* EXTERNAL */(E(_16L/* Core.Render.Internal.f4 */), new T2(1,E(_17a/* sFSv */),new T2(1,E(_179/* sFSt */),new T2(1,E(_177/* sFSr */),new T2(1,E(_175/* sFSp */),new T2(1,E(_173/* sFSn */),new T2(1,E(_171/* sFSl */),new T2(1,_17b/* sFSx */,_6/* GHC.Types.[] */)))))))),
                        _17e/* sFTc */ = B(_16M/* Core.Render.Internal.render2 */(_16U/* sFRQ */.g, _17b/* sFSx */, _/* EXTERNAL */)),
                        _17f/* sFTi */ = __app1/* EXTERNAL */(E(_wS/* Core.Render.Internal.clip_f1 */), _17b/* sFSx */);
                        return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
                      }, _/* EXTERNAL */);});
                    };
                    return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_16U/* sFRQ */.e, _178/* sFTm */, _/* EXTERNAL */);});
                  };
                  return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_16U/* sFRQ */.d, _176/* sFTn */, _/* EXTERNAL */);});
                };
                return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_16U/* sFRQ */.c, _174/* sFTo */, _/* EXTERNAL */);});
              };
              return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_16U/* sFRQ */.b, _172/* sFTp */, _/* EXTERNAL */);});
            },
            _17g/* sFTq */ = E(_16U/* sFRQ */.a);
            switch(_17g/* sFTq */._){
              case 0:
                var _17h/* sFTs */ = B(_170/* sFSk */(_17g/* sFTq */.a, _/* EXTERNAL */)),
                _16W/*   sFRK */ = _16R/* sFRK */;
                _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16Z/* sFSj */));
                _16O/*  sFRK */ = _16W/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _17i/* sFTx */ = B(A1(_17g/* sFTq */.a,_/* EXTERNAL */)),
                _17j/* sFTA */ = B(_170/* sFSk */(_17i/* sFTx */, _/* EXTERNAL */)),
                _16W/*   sFRK */ = _16R/* sFRK */;
                _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16Z/* sFSj */));
                _16O/*  sFRK */ = _16W/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _17k/* sFTM */ = rMV/* EXTERNAL */(E(E(_17g/* sFTq */.a).c)),
                _17l/* sFTP */ = E(_17k/* sFTM */);
                if(!_17l/* sFTP */._){
                  var _17m/* sFTT */ = new T(function(){
                    return B(A1(_17g/* sFTq */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_17l/* sFTP */.a));
                    })));
                  },1),
                  _17n/* sFTU */ = B(_170/* sFSk */(_17m/* sFTT */, _/* EXTERNAL */)),
                  _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16Z/* sFSj */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16Z/* sFSj */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _17o/* sFU8 */ = rMV/* EXTERNAL */(E(E(_17g/* sFTq */.a).c)),
                _17p/* sFUb */ = E(_17o/* sFU8 */);
                if(!_17p/* sFUb */._){
                  var _17q/* sFUh */ = B(A2(_17g/* sFTq */.b,E(_17p/* sFUb */.a).a, _/* EXTERNAL */)),
                  _17r/* sFUk */ = B(_170/* sFSk */(_17q/* sFUh */, _/* EXTERNAL */)),
                  _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16Z/* sFSj */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16Z/* sFSj */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 5:
            var _17s/* sFUs */ = _16U/* sFRQ */.c,
            _17t/* sFUt */ = E(_16U/* sFRQ */.a),
            _17u/* sFUw */ = function(_17v/* sFUx */, _/* EXTERNAL */){
              return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_17t/* sFUt */.b, function(_17w/* sFUz */, _/* EXTERNAL */){
                var _17x/* sFUB */ = E(_16R/* sFRK */),
                _17y/* sFUG */ = __app1/* EXTERNAL */(E(_x1/* Core.Render.Internal.clip_f4 */), _17x/* sFUB */),
                _17z/* sFUU */ = __app3/* EXTERNAL */(E(_16K/* Core.Render.Internal.f3 */), _17x/* sFUB */, E(_17v/* sFUx */), E(_17w/* sFUz */)),
                _17A/* sFUX */ = B(_16M/* Core.Render.Internal.render2 */(_16U/* sFRQ */.b, _17x/* sFUB */, _/* EXTERNAL */)),
                _17B/* sFV3 */ = __app1/* EXTERNAL */(E(_wS/* Core.Render.Internal.clip_f1 */), _17x/* sFUB */);
                return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _17C/* sFV7 */ = E(_17t/* sFUt */.a);
            switch(_17C/* sFV7 */._){
              case 0:
                var _17D/* sFV9 */ = B(_17u/* sFUw */(_17C/* sFV7 */.a, _/* EXTERNAL */)),
                _16W/*   sFRK */ = _16R/* sFRK */;
                _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17s/* sFUs */));
                _16O/*  sFRK */ = _16W/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _17E/* sFVe */ = B(A1(_17C/* sFV7 */.a,_/* EXTERNAL */)),
                _17F/* sFVh */ = B(_17u/* sFUw */(_17E/* sFVe */, _/* EXTERNAL */)),
                _16W/*   sFRK */ = _16R/* sFRK */;
                _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17s/* sFUs */));
                _16O/*  sFRK */ = _16W/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _17G/* sFVt */ = rMV/* EXTERNAL */(E(E(_17C/* sFV7 */.a).c)),
                _17H/* sFVw */ = E(_17G/* sFVt */);
                if(!_17H/* sFVw */._){
                  var _17I/* sFVA */ = new T(function(){
                    return B(A1(_17C/* sFV7 */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_17H/* sFVw */.a));
                    })));
                  },1),
                  _17J/* sFVB */ = B(_17u/* sFUw */(_17I/* sFVA */, _/* EXTERNAL */)),
                  _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17s/* sFUs */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17s/* sFUs */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _17K/* sFVP */ = rMV/* EXTERNAL */(E(E(_17C/* sFV7 */.a).c)),
                _17L/* sFVS */ = E(_17K/* sFVP */);
                if(!_17L/* sFVS */._){
                  var _17M/* sFVY */ = B(A2(_17C/* sFV7 */.b,E(_17L/* sFVS */.a).a, _/* EXTERNAL */)),
                  _17N/* sFW1 */ = B(_17u/* sFUw */(_17M/* sFVY */, _/* EXTERNAL */)),
                  _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17s/* sFUs */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17s/* sFUs */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 6:
            var _17O/* sFW9 */ = _16U/* sFRQ */.c,
            _17P/* sFWa */ = function(_17Q/* sFWb */, _/* EXTERNAL */){
              var _17R/* sFWd */ = E(_16R/* sFRK */),
              _17S/* sFWi */ = __app1/* EXTERNAL */(E(_x1/* Core.Render.Internal.clip_f4 */), _17R/* sFWd */),
              _17T/* sFWs */ = __app2/* EXTERNAL */(E(_16J/* Core.Render.Internal.f2 */), _17R/* sFWd */, E(_17Q/* sFWb */)),
              _17U/* sFWv */ = B(_16M/* Core.Render.Internal.render2 */(_16U/* sFRQ */.b, _17R/* sFWd */, _/* EXTERNAL */)),
              _17V/* sFWB */ = __app1/* EXTERNAL */(E(_wS/* Core.Render.Internal.clip_f1 */), _17R/* sFWd */);
              return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
            },
            _17W/* sFWE */ = E(_16U/* sFRQ */.a);
            switch(_17W/* sFWE */._){
              case 0:
                var _17X/* sFWG */ = B(_17P/* sFWa */(_17W/* sFWE */.a, _/* EXTERNAL */)),
                _16W/*   sFRK */ = _16R/* sFRK */;
                _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17O/* sFW9 */));
                _16O/*  sFRK */ = _16W/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _17Y/* sFWL */ = B(A1(_17W/* sFWE */.a,_/* EXTERNAL */)),
                _17Z/* sFWO */ = B(_17P/* sFWa */(_17Y/* sFWL */, _/* EXTERNAL */)),
                _16W/*   sFRK */ = _16R/* sFRK */;
                _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17O/* sFW9 */));
                _16O/*  sFRK */ = _16W/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _180/* sFX0 */ = rMV/* EXTERNAL */(E(E(_17W/* sFWE */.a).c)),
                _181/* sFX3 */ = E(_180/* sFX0 */);
                if(!_181/* sFX3 */._){
                  var _182/* sFX7 */ = new T(function(){
                    return B(A1(_17W/* sFWE */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_181/* sFX3 */.a));
                    })));
                  },1),
                  _183/* sFX8 */ = B(_17P/* sFWa */(_182/* sFX7 */, _/* EXTERNAL */)),
                  _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17O/* sFW9 */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17O/* sFW9 */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _184/* sFXm */ = rMV/* EXTERNAL */(E(E(_17W/* sFWE */.a).c)),
                _185/* sFXp */ = E(_184/* sFXm */);
                if(!_185/* sFXp */._){
                  var _186/* sFXv */ = B(A2(_17W/* sFWE */.b,E(_185/* sFXp */.a).a, _/* EXTERNAL */)),
                  _187/* sFXy */ = B(_17P/* sFWa */(_186/* sFXv */, _/* EXTERNAL */)),
                  _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17O/* sFW9 */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_17O/* sFW9 */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 7:
            var _188/* sFXG */ = _16U/* sFRQ */.c,
            _189/* sFXH */ = E(_16U/* sFRQ */.a),
            _18a/* sFXK */ = function(_18b/* sFXL */, _/* EXTERNAL */){
              return new F(function(){return _x2/* Core.Render.Internal.getImage2 */(_189/* sFXH */.b, function(_18c/* sFXN */, _/* EXTERNAL */){
                var _18d/* sFXP */ = E(_16R/* sFRK */),
                _18e/* sFXU */ = __app1/* EXTERNAL */(E(_x1/* Core.Render.Internal.clip_f4 */), _18d/* sFXP */),
                _18f/* sFY8 */ = __app3/* EXTERNAL */(E(_16I/* Core.Render.Internal.f1 */), _18d/* sFXP */, E(_18b/* sFXL */), E(_18c/* sFXN */)),
                _18g/* sFYb */ = B(_16M/* Core.Render.Internal.render2 */(_16U/* sFRQ */.b, _18d/* sFXP */, _/* EXTERNAL */)),
                _18h/* sFYh */ = __app1/* EXTERNAL */(E(_wS/* Core.Render.Internal.clip_f1 */), _18d/* sFXP */);
                return new F(function(){return _ko/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _18i/* sFYl */ = E(_189/* sFXH */.a);
            switch(_18i/* sFYl */._){
              case 0:
                var _18j/* sFYn */ = B(_18a/* sFXK */(_18i/* sFYl */.a, _/* EXTERNAL */)),
                _16W/*   sFRK */ = _16R/* sFRK */;
                _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_188/* sFXG */));
                _16O/*  sFRK */ = _16W/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _18k/* sFYs */ = B(A1(_18i/* sFYl */.a,_/* EXTERNAL */)),
                _18l/* sFYv */ = B(_18a/* sFXK */(_18k/* sFYs */, _/* EXTERNAL */)),
                _16W/*   sFRK */ = _16R/* sFRK */;
                _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_188/* sFXG */));
                _16O/*  sFRK */ = _16W/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _18m/* sFYH */ = rMV/* EXTERNAL */(E(E(_18i/* sFYl */.a).c)),
                _18n/* sFYK */ = E(_18m/* sFYH */);
                if(!_18n/* sFYK */._){
                  var _18o/* sFYO */ = new T(function(){
                    return B(A1(_18i/* sFYl */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_18n/* sFYK */.a));
                    })));
                  },1),
                  _18p/* sFYP */ = B(_18a/* sFXK */(_18o/* sFYO */, _/* EXTERNAL */)),
                  _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_188/* sFXG */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_188/* sFXG */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _18q/* sFZ3 */ = rMV/* EXTERNAL */(E(E(_18i/* sFYl */.a).c)),
                _18r/* sFZ6 */ = E(_18q/* sFZ3 */);
                if(!_18r/* sFZ6 */._){
                  var _18s/* sFZc */ = B(A2(_18i/* sFYl */.b,E(_18r/* sFZ6 */.a).a, _/* EXTERNAL */)),
                  _18t/* sFZf */ = B(_18a/* sFXK */(_18s/* sFZc */, _/* EXTERNAL */)),
                  _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_188/* sFXG */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16W/*   sFRK */ = _16R/* sFRK */;
                  _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_188/* sFXG */));
                  _16O/*  sFRK */ = _16W/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          default:
            var _18u/* sFZo */ = B(_16M/* Core.Render.Internal.render2 */(_16U/* sFRQ */.a, _16R/* sFRK */, _/* EXTERNAL */)),
            _16W/*   sFRK */ = _16R/* sFRK */;
            _16N/*  sFRJ */ = B(A1(_16T/* sFRP */,_16U/* sFRQ */.c));
            _16O/*  sFRK */ = _16W/*   sFRK */;
            return __continue/* EXTERNAL */;
        }
      }
    })(_16N/*  sFRJ */, _16O/*  sFRK */, _/* EXTERNAL */));
    if(_16P/*  render2 */!=__continue/* EXTERNAL */){
      return _16P/*  render2 */;
    }
  }
},
_18v/* a12 */ = new T1(0,_/* EXTERNAL */),
_18w/* a13 */ = new T1(0,_6/* GHC.Types.[] */),
_18x/* a14 */ = new T2(0,E(_18w/* Motion.Main.a13 */),E(_18v/* Motion.Main.a12 */)),
_18y/* pad */ = 40,
_18z/* lvl1 */ = new T1(0,_18y/* Motion.Main.pad */),
_18A/* rendering1 */ = function(_18B/* sWcL */){
  return E(E(_18B/* sWcL */).b);
},
_18C/* renderContents_go */ = function(_18D/* s7CA */, _18E/* s7CB */){
  var _18F/* s7CC */ = E(_18D/* s7CA */);
  if(!_18F/* s7CC */._){
    return E(_18x/* Motion.Main.a14 */);
  }else{
    var _18G/* s7CF */ = E(_18E/* s7CB */);
    if(!_18G/* s7CF */._){
      return E(_18x/* Motion.Main.a14 */);
    }else{
      var _18H/* s7CS */ = B(_rn/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_18z/* Motion.Main.lvl1 */,new T1(0,new T(function(){
        return 40+190*E(_18F/* s7CC */.a);
      }))),new T(function(){
        return B(_18A/* Core.View.rendering1 */(_18G/* s7CF */.a));
      }),_7/* GHC.Tuple.() */))),
      _18I/* s7CV */ = new T(function(){
        return B(_18C/* Motion.Main.renderContents_go */(_18F/* s7CC */.b, _18G/* s7CF */.b));
      }),
      _18J/* s7D6 */ = function(_18K/* s7CW */){
        var _18L/* s7CX */ = E(_18I/* s7CV */);
        return new T2(0,E(_18L/* s7CX */.a),E(new T2(2,_18L/* s7CX */.b,new T1(1,function(_18M/* s7D0 */){
          return new T2(0,E(new T1(0,new T2(1,_18K/* s7CW */,_18M/* s7D0 */))),E(_18v/* Motion.Main.a12 */));
        }))));
      };
      return new T2(0,E(_18H/* s7CS */.a),E(new T2(2,_18H/* s7CS */.b,new T1(1,_18J/* s7D6 */))));
    }
  }
},
_18N/* renderContents1 */ = function(_18O/* s7D9 */){
  return new F(function(){return _rf/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
    return B(_18C/* Motion.Main.renderContents_go */(_Ia/* Core.Util.iforM1 */, _18O/* s7D9 */));
  }));});
},
_18P/* launch1 */ = function(_18Q/* s7EI */, _18R/* s7EJ */){
  var _18S/* s7EK */ = function(_18T/* s7EL */, _/* EXTERNAL */){
    var _18U/* s7EN */ = E(_18Q/* s7EI */),
    _18V/* s7ET */ = __app1/* EXTERNAL */(E(_ib/* Haste.Graphics.Canvas.buffer_f1 */), _18U/* s7EN */.b);
    return new F(function(){return _16M/* Core.Render.Internal.render2 */(B(_18N/* Motion.Main.renderContents1 */(_18T/* s7EL */)), _18U/* s7EN */.a, _/* EXTERNAL */);});
  },
  _18W/* s7EY */ = new T(function(){
    return B(A1(_FS/* Motion.Main.lvl39 */,_18R/* s7EJ */));
  }),
  _18X/* s7GL */ = function(_18Y/* s7EZ */){
    var _18Z/* s7GK */ = function(_190/* s7F0 */){
      var _191/* s7F1 */ = E(_190/* s7F0 */),
      _192/* s7GJ */ = function(_193/* s7F4 */){
        var _194/* s7F5 */ = E(_193/* s7F4 */),
        _195/* s7GI */ = function(_196/* s7F8 */){
          var _197/* s7F9 */ = E(_196/* s7F8 */),
          _198/* s7GH */ = function(_199/* s7Fc */){
            var _19a/* s7Fd */ = E(_199/* s7Fc */),
            _19b/* s7GG */ = function(_19c/* s7Fg */){
              var _19d/* s7Fh */ = E(_19c/* s7Fg */),
              _19e/* s7Fo */ = new T2(1,_191/* s7F1 */.a,new T2(1,_194/* s7F5 */.a,new T2(1,_197/* s7F9 */.a,new T2(1,_19a/* s7Fd */.a,new T2(1,_19d/* s7Fh */.a,_6/* GHC.Types.[] */))))),
              _19f/* s7GF */ = function(_/* EXTERNAL */){
                var _19g/* s7FD */ = jsShow/* EXTERNAL */(40+B(_eT/* GHC.List.$wlenAcc */(_19e/* s7Fo */, 0))*190),
                _19h/* s7FP */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), E(_18Q/* s7EI */).b, toJSStr/* EXTERNAL */(E(_16F/* Motion.Main.lvl60 */)), toJSStr/* EXTERNAL */(fromJSStr/* EXTERNAL */(_19g/* s7FD */))),
                _19i/* s7GD */ = function(_/* EXTERNAL */){
                  var _19j/* s7FU */ = nMV/* EXTERNAL */(new T2(0,_19e/* s7Fo */,_6/* GHC.Types.[] */));
                  return new T(function(){
                    var _19k/* s7FY */ = new T(function(){
                      return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _19j/* s7FU */, _eY/* Motion.Main.a24 */));
                    }),
                    _19l/* s7G0 */ = function(_19m/* s7G6 */){
                      return new F(function(){return _19n/* s7G3 */(E(_19m/* s7G6 */).b);});
                    },
                    _19o/* s7G1 */ = function(_19p/* s7Ga */){
                      return new F(function(){return _tl/* Core.World.Internal.sleep1 */(_16G/* Motion.Main.lvl61 */, E(_19p/* s7Ga */).b, _19l/* s7G0 */);});
                    },
                    _19q/* s7G2 */ = function(_19r/* s7Ge */){
                      var _19s/* s7Gf */ = E(_19r/* s7Ge */);
                      return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[B(_18N/* Motion.Main.renderContents1 */(_19s/* s7Gf */.a)), _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _19s/* s7Gf */.b, _19o/* s7G1 */]);});
                    },
                    _19n/* s7G3 */ = function(_19t/* s7Gj */){
                      return new F(function(){return A2(_19k/* s7FY */,_19t/* s7Gj */, _19q/* s7G2 */);});
                    },
                    _19u/* s7Gz */ = function(_19v/* s7Gk */){
                      var _19w/* s7Gn */ = E(_19v/* s7Gk */).b,
                      _19x/* s7Gy */ = function(_/* EXTERNAL */){
                        var _19y/* s7Gp */ = nMV/* EXTERNAL */(_16H/* Motion.Main.lvl62 */);
                        return new T1(1,new T2(1,new T(function(){
                          return B(A1(_18Y/* s7EZ */,new T2(0,_7/* GHC.Tuple.() */,_19w/* s7Gn */)));
                        }),new T2(1,new T(function(){
                          return B(_19n/* s7G3 */(_19w/* s7Gn */));
                        }),_6/* GHC.Types.[] */)));
                      };
                      return new T1(0,_19x/* s7Gy */);
                    };
                    return new T1(0,B(_e8/* Core.Front.Internal.$wa */(_19j/* s7FU */, _18S/* s7EK */, _19d/* s7Fh */.b, _19u/* s7Gz */)));
                  });
                };
                return new T1(0,_19i/* s7GD */);
              };
              return new T1(0,_19f/* s7GF */);
            };
            return new F(function(){return A2(_16E/* Motion.Main.lvl59 */,_19a/* s7Fd */.b, _19b/* s7GG */);});
          };
          return new F(function(){return A2(_15q/* Motion.Main.lvl55 */,_197/* s7F9 */.b, _198/* s7GH */);});
        };
        return new F(function(){return A2(_YP/* Motion.Main.lvl49 */,_194/* s7F5 */.b, _195/* s7GI */);});
      };
      return new F(function(){return A2(_Jb/* Motion.Main.lvl45 */,_191/* s7F1 */.b, _192/* s7GJ */);});
    };
    return new F(function(){return A1(_18W/* s7EY */,_18Z/* s7GK */);});
  };
  return E(_18X/* s7GL */);
},
_19z/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Canvas not found!"));
}),
_19A/* main2 */ = new T(function(){
  return B(err/* EXTERNAL */(_19z/* Main.lvl */));
}),
_19B/* main3 */ = "canvas",
_19C/* start_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(Util.onload)");
}),
_19D/* main1 */ = function(_/* EXTERNAL */){
  var _19E/* s11fh */ = __app1/* EXTERNAL */(E(_19C/* Core.Front.Internal.start_f1 */), E(_48/* Haste.Prim.Any.jsNull */)),
  _19F/* s11fk */ = B(A3(_e1/* Haste.DOM.JSString.elemById */,_2G/* Control.Monad.IO.Class.$fMonadIOIO */, _19B/* Main.main3 */, _/* EXTERNAL */)),
  _19G/* s11fn */ = E(_19F/* s11fk */);
  if(!_19G/* s11fn */._){
    return E(_19A/* Main.main2 */);
  }else{
    var _19H/* s11fq */ = E(_19G/* s11fn */.a),
    _19I/* s11fv */ = __app1/* EXTERNAL */(E(_1/* Haste.Graphics.Canvas.$fFromAnyCanvas_f2 */), _19H/* s11fq */);
    if(!_19I/* s11fv */){
      return E(_19A/* Main.main2 */);
    }else{
      var _19J/* s11fD */ = __app1/* EXTERNAL */(E(_0/* Haste.Graphics.Canvas.$fFromAnyCanvas_f1 */), _19H/* s11fq */),
      _19K/* s11fF */ = _19J/* s11fD */,
      _19L/* s11fK */ = new T(function(){
        return new T1(0,B(_d7/* Core.World.Internal.$wa5 */(function(_19M/* B1 */){
          return new F(function(){return _18P/* Motion.Main.launch1 */(new T2(0,_19K/* s11fF */,_19H/* s11fq */), _19M/* B1 */);});
        }, _2I/* Haste.Concurrent.Monad.forkIO1 */)));
      });
      return new F(function(){return _e/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(_19L/* s11fK */, _6/* GHC.Types.[] */, _/* EXTERNAL */);});
    }
  }
},
_19N/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _19D/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_19N, [0]));};window.onload = hasteMain;