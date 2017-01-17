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
_eY/* a24 */ = function(_eZ/* s7MU */, _f0/* s7MV */, _f1/* s7MW */){
  return new F(function(){return A1(_f1/* s7MW */,new T2(0,new T2(0,_eZ/* s7MU */,_eZ/* s7MU */),_f0/* s7MV */));});
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
_fD/* valueOf1 */ = function(_fE/* sb3P */, _fF/* sb3Q */, _fG/* sb3R */){
  var _fH/* sb3S */ = E(_fE/* sb3P */);
  switch(_fH/* sb3S */._){
    case 0:
      return new F(function(){return _5D/* Core.World.Internal.$fMonadWorld2 */(_fH/* sb3S */.a, _fF/* sb3Q */, _fG/* sb3R */);});
      break;
    case 1:
      return new F(function(){return _8s/* Core.World.Internal.$fMonadIOWorld1 */(_fH/* sb3S */.a, _fF/* sb3Q */, _fG/* sb3R */);});
      break;
    case 2:
      var _fI/* sb40 */ = E(_fH/* sb3S */.a).c,
      _fJ/* sb4a */ = function(_fK/* sb41 */){
        var _fL/* sb42 */ = new T(function(){
          var _fM/* sb44 */ = new T(function(){
            return B(A1(_fH/* sb3S */.b,new T(function(){
              return B(_fB/* Data.Tuple.fst */(_fK/* sb41 */));
            })));
          });
          return B(A1(_fG/* sb3R */,new T2(0,_fM/* sb44 */,_fF/* sb3Q */)));
        });
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_fI/* sb40 */, _fK/* sb41 */, function(_fN/* sb46 */){
          return E(_fL/* sb42 */);
        })));
      };
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_fI/* sb40 */, _fJ/* sb4a */)));
    default:
      var _fO/* sb4i */ = E(_fH/* sb3S */.a).c,
      _fP/* sb4x */ = function(_fQ/* sb4j */){
        var _fR/* sb4k */ = function(_/* EXTERNAL */){
          var _fS/* sb4n */ = B(A2(_fH/* sb3S */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_fQ/* sb4j */));
          }), _/* EXTERNAL */));
          return new T(function(){
            return B(A1(_fG/* sb3R */,new T2(0,_fS/* sb4n */,_fF/* sb3Q */)));
          });
        };
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_fO/* sb4i */, _fQ/* sb4j */, function(_fT/* sb4t */){
          return E(new T1(0,_fR/* sb4k */));
        })));
      };
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_fO/* sb4i */, _fP/* sb4x */)));
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
_id/* $fMorphDouble_$clerp */ = function(_ie/* sbeD */, _if/* sbeE */, _ig/* sbeF */){
  var _ih/* sbeI */ = E(_ie/* sbeD */);
  return E(_if/* sbeE */)*(1-_ih/* sbeI */)+E(_ig/* sbeF */)*_ih/* sbeI */;
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
_iz/* a7 */ = function(_iA/* sbfy */, _iB/* sbfz */, _iC/* sbfA */){
  var _iD/* sbfB */ = new T(function(){
    return E(E(_iA/* sbfy */).b);
  });
  return new F(function(){return A1(_iC/* sbfA */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,new T(function(){
    return E(E(_iA/* sbfy */).a);
  }),new T4(0,new T(function(){
    return E(E(_iD/* sbfB */).a);
  }),new T(function(){
    return E(E(_iD/* sbfB */).b);
  }),new T(function(){
    return E(E(_iD/* sbfB */).c);
  }),_av/* GHC.Types.False */))),_iB/* sbfz */));});
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
_iS/* $weaseHandle */ = function(_iT/* sbg5 */, _iU/* sbg6 */, _iV/* sbg7 */, _iW/* sbg8 */, _iX/* sbg9 */, _iY/* sbga */){
  var _iZ/* sbgb */ = new T(function(){
    var _j0/* sbgc */ = new T(function(){
      return B(A1(_iV/* sbg7 */,_2E/* GHC.Base.id */));
    }),
    _j1/* sbgv */ = function(_j2/* sbgd */, _j3/* sbge */, _j4/* sbgf */){
      var _j5/* sbgg */ = E(_j2/* sbgd */),
      _j6/* sbgj */ = E(_j5/* sbgg */.b),
      _j7/* sbgq */ = new T(function(){
        var _j8/* sbgp */ = new T(function(){
          return B(A1(_j0/* sbgc */,new T(function(){
            return B(_iE/* GHC.Float.divideDouble */(_j6/* sbgj */.c, _iU/* sbg6 */));
          })));
        });
        return B(A3(_iT/* sbg5 */,_j8/* sbgp */, _j6/* sbgj */.a, _j6/* sbgj */.b));
      });
      return new F(function(){return A1(_j4/* sbgf */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_j5/* sbgg */.a,new T4(0,_j7/* sbgq */,_iX/* sbg9 */,_iH/* Core.Ease.ease2 */,_j6/* sbgj */.d))),_j3/* sbge */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iW/* sbg8 */, _j1/* sbgv */));
  }),
  _j9/* sbgw */ = new T(function(){
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iW/* sbg8 */, _iz/* Core.Ease.a7 */));
  }),
  _ja/* sbgx */ = new T(function(){
    var _jb/* sbgy */ = new T(function(){
      return B(A1(_iY/* sbga */,_av/* GHC.Types.False */));
    }),
    _jc/* sbgz */ = new T(function(){
      return B(A1(_iY/* sbga */,_aw/* GHC.Types.True */));
    }),
    _jd/* sbgA */ = new T(function(){
      return B(A1(_iV/* sbg7 */,_2E/* GHC.Base.id */));
    }),
    _je/* sbhn */ = function(_jf/* sbgB */, _jg/* sbgC */, _jh/* sbgD */){
      var _ji/* sbgE */ = E(_jf/* sbgB */),
      _jj/* sbgH */ = E(_ji/* sbgE */.b),
      _jk/* sbgI */ = _jj/* sbgH */.a,
      _jl/* sbgJ */ = _jj/* sbgH */.b;
      if(!E(_jj/* sbgH */.d)){
        var _jm/* sbgN */ = E(_iU/* sbg6 */),
        _jn/* sbgR */ = E(_jj/* sbgH */.c)+1,
        _jo/* sbgS */ = function(_jp/* sbgT */, _jq/* sbgU */){
          var _jr/* sbgV */ = new T(function(){
            var _js/* sbgY */ = new T(function(){
              return B(A1(_jd/* sbgA */,new T(function(){
                return _jp/* sbgT *//_jm/* sbgN */;
              })));
            });
            return B(A3(_iT/* sbg5 */,_js/* sbgY */, _jk/* sbgI */, _jl/* sbgJ */));
          }),
          _jt/* sbgZ */ = new T4(0,_jk/* sbgI */,_jl/* sbgJ */,_jq/* sbgU */,_aw/* GHC.Types.True */);
          if(_jp/* sbgT */>=_jm/* sbgN */){
            return new F(function(){return A2(_jc/* sbgz */,_jg/* sbgC */, function(_ju/* sbh4 */){
              return new F(function(){return A1(_jh/* sbgD */,new T2(0,new T2(0,_av/* GHC.Types.False */,new T2(0,_jr/* sbgV */,_jt/* sbgZ */)),E(_ju/* sbh4 */).b));});
            });});
          }else{
            return new F(function(){return A1(_jh/* sbgD */,new T2(0,new T2(0,_aw/* GHC.Types.True */,new T2(0,_jr/* sbgV */,_jt/* sbgZ */)),_jg/* sbgC */));});
          }
        };
        if(_jm/* sbgN */>_jn/* sbgR */){
          return new F(function(){return _jo/* sbgS */(_jn/* sbgR */, _jn/* sbgR */);});
        }else{
          return new F(function(){return _jo/* sbgS */(_jm/* sbgN */, _jm/* sbgN */);});
        }
      }else{
        return new F(function(){return A2(_jb/* sbgy */,_jg/* sbgC */, function(_jv/* sbhh */){
          return new F(function(){return A1(_jh/* sbgD */,new T2(0,new T2(0,_av/* GHC.Types.False */,_ji/* sbgE */),E(_jv/* sbhh */).b));});
        });});
      }
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iW/* sbg8 */, _je/* sbhn */));
  }),
  _jw/* sbhT */ = function(_jx/* sbho */, _jy/* sbhp */){
    var _jz/* sbhq */ = new T(function(){
      return B(A2(_iZ/* sbgb */,_jx/* sbho */, function(_jA/* sbhr */){
        return new F(function(){return _iI/* Core.World.Internal.easeRegister1 */(_j9/* sbgw */, _ja/* sbgx */, E(_jA/* sbhr */).b, _jy/* sbhp */);});
      }));
    }),
    _jB/* sbhQ */ = function(_jC/* sbhw */){
      var _jD/* sbhx */ = new T(function(){
        var _jE/* sbhy */ = E(_jC/* sbhw */),
        _jF/* sbhB */ = E(_jE/* sbhy */.a),
        _jG/* sbhC */ = E(_jE/* sbhy */.b),
        _jH/* sbhH */ = E(_jG/* sbhC */.a),
        _jI/* sbhI */ = E(_jG/* sbhC */.b),
        _jJ/* sbhK */ = E(_jG/* sbhC */.c),
        _jK/* sbhL */ = E(_jG/* sbhC */.d);
        return E(_jz/* sbhq */);
      });
      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_iW/* sbg8 */, _jC/* sbhw */, function(_jL/* sbhM */){
        return E(_jD/* sbhx */);
      })));
    };
    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_iW/* sbg8 */, _jB/* sbhQ */)));
  };
  return E(_jw/* sbhT */);
},
_jM/* forceTo_b1 */ = 1,
_jN/* $wforceTo */ = function(_jO/* sb1p */, _jP/* sb1q */){
  var _jQ/* sb1r */ = new T(function(){
    var _jR/* sb1I */ = function(_jS/* sb1s */, _jT/* sb1t */, _jU/* sb1u */){
      return new F(function(){return A1(_jU/* sb1u */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_jP/* sb1q */,new T4(0,_jP/* sb1q */,_jP/* sb1q */,_jM/* Core.Ease.forceTo_b1 */,new T(function(){
        return E(E(E(_jS/* sb1s */).b).d);
      })))),_jT/* sb1t */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _jO/* sb1p */, _jR/* sb1I */));
  }),
  _jV/* sb29 */ = function(_jW/* sb1J */, _jX/* sb1K */){
    var _jY/* sb1L */ = new T(function(){
      return B(A2(_jQ/* sb1r */,_jW/* sb1J */, _jX/* sb1K */));
    }),
    _jZ/* sb26 */ = function(_k0/* sb1M */){
      var _k1/* sb1N */ = new T(function(){
        var _k2/* sb1O */ = E(_k0/* sb1M */),
        _k3/* sb1R */ = E(_k2/* sb1O */.a),
        _k4/* sb1S */ = E(_k2/* sb1O */.b),
        _k5/* sb1X */ = E(_k4/* sb1S */.a),
        _k6/* sb1Y */ = E(_k4/* sb1S */.b),
        _k7/* sb20 */ = E(_k4/* sb1S */.c),
        _k8/* sb21 */ = E(_k4/* sb1S */.d);
        return E(_jY/* sb1L */);
      });
      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_jO/* sb1p */, _k0/* sb1M */, function(_k9/* sb22 */){
        return E(_k1/* sb1N */);
      })));
    };
    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_jO/* sb1p */, _jZ/* sb26 */)));
  };
  return E(_jV/* sb29 */);
},
_ka/* $fAffineShape2 */ = function(_kb/* stet */, _kc/* steu */, _kd/* stev */, _ke/* stew */, _/* EXTERNAL */){
  var _kf/* stey */ = E(_kb/* stet */);
  switch(_kf/* stey */._){
    case 0:
      return new F(function(){return A(_kc/* steu */,[_kf/* stey */.a, _kd/* stev */, _ke/* stew */, _/* EXTERNAL */]);});
      break;
    case 1:
      var _kg/* steB */ = B(A1(_kf/* stey */.a,_/* EXTERNAL */));
      return new F(function(){return A(_kc/* steu */,[_kg/* steB */, _kd/* stev */, _ke/* stew */, _/* EXTERNAL */]);});
      break;
    case 2:
      var _kh/* steM */ = rMV/* EXTERNAL */(E(E(_kf/* stey */.a).c)),
      _ki/* steP */ = E(_kh/* steM */);
      if(!_ki/* steP */._){
        var _kj/* steT */ = new T(function(){
          return B(A1(_kf/* stey */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_ki/* steP */.a));
          })));
        });
        return new F(function(){return A(_kc/* steu */,[_kj/* steT */, _kd/* stev */, _ke/* stew */, _/* EXTERNAL */]);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _kk/* stf3 */ = rMV/* EXTERNAL */(E(E(_kf/* stey */.a).c)),
      _kl/* stf6 */ = E(_kk/* stf3 */);
      if(!_kl/* stf6 */._){
        var _km/* stfc */ = B(A2(_kf/* stey */.b,E(_kl/* stf6 */.a).a, _/* EXTERNAL */));
        return new F(function(){return A(_kc/* steu */,[_km/* stfc */, _kd/* stev */, _ke/* stew */, _/* EXTERNAL */]);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
  }
},
_kn/* $fAffineShape3 */ = function(_ko/* stfg */, _kp/* stfh */, _/* EXTERNAL */){
  var _kq/* stfj */ = E(_ko/* stfg */);
  switch(_kq/* stfj */._){
    case 0:
      return new F(function(){return A2(_kp/* stfh */,_kq/* stfj */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _kr/* stfm */ = B(A1(_kq/* stfj */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_kp/* stfh */,_kr/* stfm */, _/* EXTERNAL */);});
      break;
    case 2:
      var _ks/* stfx */ = rMV/* EXTERNAL */(E(E(_kq/* stfj */.a).c)),
      _kt/* stfA */ = E(_ks/* stfx */);
      if(!_kt/* stfA */._){
        var _ku/* stfE */ = new T(function(){
          return B(A1(_kq/* stfj */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_kt/* stfA */.a));
          })));
        });
        return new F(function(){return A2(_kp/* stfh */,_ku/* stfE */, _/* EXTERNAL */);});
      }else{
        return _av/* GHC.Types.False */;
      }
      break;
    default:
      var _kv/* stfO */ = rMV/* EXTERNAL */(E(E(_kq/* stfj */.a).c)),
      _kw/* stfR */ = E(_kv/* stfO */);
      if(!_kw/* stfR */._){
        var _kx/* stfX */ = B(A2(_kq/* stfj */.b,E(_kw/* stfR */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_kp/* stfh */,_kx/* stfX */, _/* EXTERNAL */);});
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
_kB/* $wrect */ = function(_kC/* stAy */, _kD/* stAz */, _kE/* stAA */, _kF/* stAB */){
  var _kG/* stCD */ = function(_kH/* stBA */, _kI/* stBB */, _kJ/* stBC */, _/* EXTERNAL */){
    var _kK/* stCC */ = function(_kL/* stBE */, _kM/* stBF */, _kN/* stBG */, _/* EXTERNAL */){
      var _kO/* stCB */ = function(_kP/* stBI */, _kQ/* stBJ */, _kR/* stBK */, _/* EXTERNAL */){
        return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_kF/* stAB */, function(_kS/* stBM */, _kT/* stBN */, _kU/* stBO */, _/* EXTERNAL */){
          var _kV/* stBQ */ = E(_kH/* stBA */),
          _kW/* stBU */ = E(_kL/* stBE */),
          _kX/* stBY */ = E(_kT/* stBN */),
          _kY/* stC2 */ = E(_kU/* stBO */),
          _kZ/* stC5 */ = __app4/* EXTERNAL */(E(_kz/* Core.Shape.Internal.bezier_f2 */), _kV/* stBQ */, _kW/* stBU */, _kX/* stBY */, _kY/* stC2 */),
          _l0/* stCa */ = _kV/* stBQ */+E(_kP/* stBI */),
          _l1/* stCd */ = E(_kA/* Core.Shape.Internal.line_f1 */),
          _l2/* stCg */ = __app4/* EXTERNAL */(_l1/* stCd */, _l0/* stCa */, _kW/* stBU */, _kX/* stBY */, _kY/* stC2 */),
          _l3/* stCl */ = _kW/* stBU */+E(_kS/* stBM */),
          _l4/* stCp */ = __app4/* EXTERNAL */(_l1/* stCd */, _l0/* stCa */, _l3/* stCl */, _kX/* stBY */, _kY/* stC2 */),
          _l5/* stCt */ = __app4/* EXTERNAL */(_l1/* stCd */, _kV/* stBQ */, _l3/* stCl */, _kX/* stBY */, _kY/* stC2 */),
          _l6/* stCx */ = __app4/* EXTERNAL */(_l1/* stCd */, _kV/* stBQ */, _kW/* stBU */, _kX/* stBY */, _kY/* stC2 */);
          return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _kQ/* stBJ */, _kR/* stBK */, _/* EXTERNAL */);});
      };
      return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_kE/* stAA */, _kO/* stCB */, _kM/* stBF */, _kN/* stBG */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_kD/* stAz */, _kK/* stCC */, _kI/* stBB */, _kJ/* stBC */, _/* EXTERNAL */);});
  },
  _l7/* stBz */ = function(_l8/* stAC */, _/* EXTERNAL */){
    var _l9/* stAE */ = E(_l8/* stAC */),
    _la/* stBy */ = function(_lb/* stAH */, _/* EXTERNAL */){
      var _lc/* stBx */ = function(_ld/* stAJ */, _/* EXTERNAL */){
        var _le/* stBw */ = function(_lf/* stAL */, _/* EXTERNAL */){
          var _lg/* stBv */ = function(_lh/* stAN */, _/* EXTERNAL */){
            return new T(function(){
              var _li/* stAT */ = E(_lf/* stAL */),
              _lj/* stAV */ = function(_lk/* stAW */){
                var _ll/* stB1 */ = E(_lh/* stAN */),
                _lm/* stB5 */ = E(_l9/* stAE */.b)-E(_ld/* stAJ */)-_ll/* stB1 *//2;
                return (_lm/* stB5 */==0) ? 0<_ll/* stB1 *//2 : (_lm/* stB5 */<=0) ?  -_lm/* stB5 */<_ll/* stB1 *//2 : _lm/* stB5 */<_ll/* stB1 *//2;
              },
              _ln/* stBh */ = E(_l9/* stAE */.a)-E(_lb/* stAH */)-_li/* stAT *//2;
              if(!_ln/* stBh */){
                if(0>=_li/* stAT *//2){
                  return false;
                }else{
                  return B(_lj/* stAV */(_/* EXTERNAL */));
                }
              }else{
                if(_ln/* stBh */<=0){
                  if( -_ln/* stBh */>=_li/* stAT *//2){
                    return false;
                  }else{
                    return B(_lj/* stAV */(_/* EXTERNAL */));
                  }
                }else{
                  if(_ln/* stBh */>=_li/* stAT *//2){
                    return false;
                  }else{
                    return B(_lj/* stAV */(_/* EXTERNAL */));
                  }
                }
              }
            });
          };
          return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_kF/* stAB */, _lg/* stBv */, _/* EXTERNAL */);});
        };
        return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_kE/* stAA */, _le/* stBw */, _/* EXTERNAL */);});
      };
      return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_kD/* stAz */, _lc/* stBx */, _/* EXTERNAL */);});
    };
    return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_kC/* stAy */, _la/* stBy */, _/* EXTERNAL */);});
  };
  return new T3(0,_l7/* stBz */,function(_lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_kC/* stAy */, _kG/* stCD */, _lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_lq/* a */ = 100,
_lr/* a4 */ = function(_ls/* sNuv */, _lt/* sNuw */){
  var _lu/* sNuC */ = B(A1(_ls/* sNuv */,new T(function(){
    return 1-(1-E(_lt/* sNuw */));
  })));
  return 1-(1-_lu/* sNuC */*_lu/* sNuC */);
},
_lv/* dur */ = 20,
_lw/* e */ = function(_lx/* sNul */, _ly/* sNum */){
  var _lz/* sNur */ = B(A1(_lx/* sNul */,new T(function(){
    return 1-E(_ly/* sNum */);
  })));
  return 1-_lz/* sNur */*_lz/* sNur */;
},
_lA/* easeIn */ = function(_lB/* sb18 */, _lC/* sb19 */){
  return new F(function(){return A1(_lB/* sb18 */,_lC/* sb19 */);});
},
_lD/* $wa */ = function(_lE/* sFyy */, _lF/* sFyz */, _lG/* sFyA */, _lH/* sFyB */, _/* EXTERNAL */){
  var _lI/* sFyD */ = function(_/* EXTERNAL */, _lJ/* sFyF */){
    var _lK/* sFyG */ = function(_/* EXTERNAL */, _lL/* sFyI */){
      var _lM/* sFyJ */ = function(_/* EXTERNAL */, _lN/* sFyL */){
        var _lO/* sFyM */ = E(_lH/* sFyB */);
        switch(_lO/* sFyM */._){
          case 0:
            return new T(function(){
              var _lP/* sFyO */ = function(_lQ/* sFyP */){
                var _lR/* sFyQ */ = _lQ/* sFyP */*256,
                _lS/* sFyR */ = _lR/* sFyQ */&4294967295,
                _lT/* sFyS */ = function(_lU/* sFyT */){
                  var _lV/* sFyW */ = E(_lL/* sFyI */)*256,
                  _lW/* sFyX */ = _lV/* sFyW */&4294967295,
                  _lX/* sFyY */ = function(_lY/* sFyZ */){
                    var _lZ/* sFz0 */ = function(_m0/* sFz1 */){
                      var _m1/* sFz2 */ = _m0/* sFz1 */*256,
                      _m2/* sFz3 */ = _m1/* sFz2 */&4294967295,
                      _m3/* sFz4 */ = function(_m4/* sFz5 */){
                        var _m5/* sFz6 */ = E(_lO/* sFyM */.a);
                        return (1>_m5/* sFz6 */) ? (0>_m5/* sFz6 */) ? new T4(1,_lU/* sFyT */,_lY/* sFyZ */,_m4/* sFz5 */,0) : new T4(1,_lU/* sFyT */,_lY/* sFyZ */,_m4/* sFz5 */,_m5/* sFz6 */) : new T4(1,_lU/* sFyT */,_lY/* sFyZ */,_m4/* sFz5 */,1);
                      };
                      if(_m1/* sFz2 */>=_m2/* sFz3 */){
                        if(255>_m2/* sFz3 */){
                          if(0>_m2/* sFz3 */){
                            return new F(function(){return _m3/* sFz4 */(0);});
                          }else{
                            return new F(function(){return _m3/* sFz4 */(_m2/* sFz3 */);});
                          }
                        }else{
                          return new F(function(){return _m3/* sFz4 */(255);});
                        }
                      }else{
                        var _m6/* sFzj */ = _m2/* sFz3 */-1|0;
                        if(255>_m6/* sFzj */){
                          if(0>_m6/* sFzj */){
                            return new F(function(){return _m3/* sFz4 */(0);});
                          }else{
                            return new F(function(){return _m3/* sFz4 */(_m6/* sFzj */);});
                          }
                        }else{
                          return new F(function(){return _m3/* sFz4 */(255);});
                        }
                      }
                    },
                    _m7/* sFzo */ = E(_lN/* sFyL */);
                    if(!_m7/* sFzo */._){
                      return new F(function(){return _lZ/* sFz0 */(0);});
                    }else{
                      return new F(function(){return _lZ/* sFz0 */(E(_m7/* sFzo */.a));});
                    }
                  };
                  if(_lV/* sFyW */>=_lW/* sFyX */){
                    if(255>_lW/* sFyX */){
                      if(0>_lW/* sFyX */){
                        return new F(function(){return _lX/* sFyY */(0);});
                      }else{
                        return new F(function(){return _lX/* sFyY */(_lW/* sFyX */);});
                      }
                    }else{
                      return new F(function(){return _lX/* sFyY */(255);});
                    }
                  }else{
                    var _m8/* sFzz */ = _lW/* sFyX */-1|0;
                    if(255>_m8/* sFzz */){
                      if(0>_m8/* sFzz */){
                        return new F(function(){return _lX/* sFyY */(0);});
                      }else{
                        return new F(function(){return _lX/* sFyY */(_m8/* sFzz */);});
                      }
                    }else{
                      return new F(function(){return _lX/* sFyY */(255);});
                    }
                  }
                };
                if(_lR/* sFyQ */>=_lS/* sFyR */){
                  if(255>_lS/* sFyR */){
                    if(0>_lS/* sFyR */){
                      return new F(function(){return _lT/* sFyS */(0);});
                    }else{
                      return new F(function(){return _lT/* sFyS */(_lS/* sFyR */);});
                    }
                  }else{
                    return new F(function(){return _lT/* sFyS */(255);});
                  }
                }else{
                  var _m9/* sFzL */ = _lS/* sFyR */-1|0;
                  if(255>_m9/* sFzL */){
                    if(0>_m9/* sFzL */){
                      return new F(function(){return _lT/* sFyS */(0);});
                    }else{
                      return new F(function(){return _lT/* sFyS */(_m9/* sFzL */);});
                    }
                  }else{
                    return new F(function(){return _lT/* sFyS */(255);});
                  }
                }
              },
              _ma/* sFzQ */ = E(_lJ/* sFyF */);
              if(!_ma/* sFzQ */._){
                return B(_lP/* sFyO */(0));
              }else{
                return B(_lP/* sFyO */(E(_ma/* sFzQ */.a)));
              }
            });
          case 1:
            var _mb/* sFzW */ = B(A1(_lO/* sFyM */.a,_/* EXTERNAL */)),
            _mc/* sFzY */ = _mb/* sFzW */;
            return new T(function(){
              var _md/* sFzZ */ = function(_me/* sFA0 */){
                var _mf/* sFA1 */ = _me/* sFA0 */*256,
                _mg/* sFA2 */ = _mf/* sFA1 */&4294967295,
                _mh/* sFA3 */ = function(_mi/* sFA4 */){
                  var _mj/* sFA7 */ = E(_lL/* sFyI */)*256,
                  _mk/* sFA8 */ = _mj/* sFA7 */&4294967295,
                  _ml/* sFA9 */ = function(_mm/* sFAa */){
                    var _mn/* sFAb */ = function(_mo/* sFAc */){
                      var _mp/* sFAd */ = _mo/* sFAc */*256,
                      _mq/* sFAe */ = _mp/* sFAd */&4294967295,
                      _mr/* sFAf */ = function(_ms/* sFAg */){
                        var _mt/* sFAh */ = E(_mc/* sFzY */);
                        return (1>_mt/* sFAh */) ? (0>_mt/* sFAh */) ? new T4(1,_mi/* sFA4 */,_mm/* sFAa */,_ms/* sFAg */,0) : new T4(1,_mi/* sFA4 */,_mm/* sFAa */,_ms/* sFAg */,_mt/* sFAh */) : new T4(1,_mi/* sFA4 */,_mm/* sFAa */,_ms/* sFAg */,1);
                      };
                      if(_mp/* sFAd */>=_mq/* sFAe */){
                        if(255>_mq/* sFAe */){
                          if(0>_mq/* sFAe */){
                            return new F(function(){return _mr/* sFAf */(0);});
                          }else{
                            return new F(function(){return _mr/* sFAf */(_mq/* sFAe */);});
                          }
                        }else{
                          return new F(function(){return _mr/* sFAf */(255);});
                        }
                      }else{
                        var _mu/* sFAu */ = _mq/* sFAe */-1|0;
                        if(255>_mu/* sFAu */){
                          if(0>_mu/* sFAu */){
                            return new F(function(){return _mr/* sFAf */(0);});
                          }else{
                            return new F(function(){return _mr/* sFAf */(_mu/* sFAu */);});
                          }
                        }else{
                          return new F(function(){return _mr/* sFAf */(255);});
                        }
                      }
                    },
                    _mv/* sFAz */ = E(_lN/* sFyL */);
                    if(!_mv/* sFAz */._){
                      return new F(function(){return _mn/* sFAb */(0);});
                    }else{
                      return new F(function(){return _mn/* sFAb */(E(_mv/* sFAz */.a));});
                    }
                  };
                  if(_mj/* sFA7 */>=_mk/* sFA8 */){
                    if(255>_mk/* sFA8 */){
                      if(0>_mk/* sFA8 */){
                        return new F(function(){return _ml/* sFA9 */(0);});
                      }else{
                        return new F(function(){return _ml/* sFA9 */(_mk/* sFA8 */);});
                      }
                    }else{
                      return new F(function(){return _ml/* sFA9 */(255);});
                    }
                  }else{
                    var _mw/* sFAK */ = _mk/* sFA8 */-1|0;
                    if(255>_mw/* sFAK */){
                      if(0>_mw/* sFAK */){
                        return new F(function(){return _ml/* sFA9 */(0);});
                      }else{
                        return new F(function(){return _ml/* sFA9 */(_mw/* sFAK */);});
                      }
                    }else{
                      return new F(function(){return _ml/* sFA9 */(255);});
                    }
                  }
                };
                if(_mf/* sFA1 */>=_mg/* sFA2 */){
                  if(255>_mg/* sFA2 */){
                    if(0>_mg/* sFA2 */){
                      return new F(function(){return _mh/* sFA3 */(0);});
                    }else{
                      return new F(function(){return _mh/* sFA3 */(_mg/* sFA2 */);});
                    }
                  }else{
                    return new F(function(){return _mh/* sFA3 */(255);});
                  }
                }else{
                  var _mx/* sFAW */ = _mg/* sFA2 */-1|0;
                  if(255>_mx/* sFAW */){
                    if(0>_mx/* sFAW */){
                      return new F(function(){return _mh/* sFA3 */(0);});
                    }else{
                      return new F(function(){return _mh/* sFA3 */(_mx/* sFAW */);});
                    }
                  }else{
                    return new F(function(){return _mh/* sFA3 */(255);});
                  }
                }
              },
              _my/* sFB1 */ = E(_lJ/* sFyF */);
              if(!_my/* sFB1 */._){
                return B(_md/* sFzZ */(0));
              }else{
                return B(_md/* sFzZ */(E(_my/* sFB1 */.a)));
              }
            });
          case 2:
            var _mz/* sFBe */ = rMV/* EXTERNAL */(E(E(_lO/* sFyM */.a).c)),
            _mA/* sFBh */ = E(_mz/* sFBe */);
            return (_mA/* sFBh */._==0) ? new T(function(){
              var _mB/* sFBk */ = function(_mC/* sFBl */){
                var _mD/* sFBm */ = _mC/* sFBl */*256,
                _mE/* sFBn */ = _mD/* sFBm */&4294967295,
                _mF/* sFBo */ = function(_mG/* sFBp */){
                  var _mH/* sFBs */ = E(_lL/* sFyI */)*256,
                  _mI/* sFBt */ = _mH/* sFBs */&4294967295,
                  _mJ/* sFBu */ = function(_mK/* sFBv */){
                    var _mL/* sFBw */ = function(_mM/* sFBx */){
                      var _mN/* sFBy */ = _mM/* sFBx */*256,
                      _mO/* sFBz */ = _mN/* sFBy */&4294967295,
                      _mP/* sFBA */ = function(_mQ/* sFBB */){
                        var _mR/* sFBD */ = B(A1(_lO/* sFyM */.b,new T(function(){
                          return B(_fB/* Data.Tuple.fst */(_mA/* sFBh */.a));
                        })));
                        return (1>_mR/* sFBD */) ? (0>_mR/* sFBD */) ? new T4(1,_mG/* sFBp */,_mK/* sFBv */,_mQ/* sFBB */,0) : new T4(1,_mG/* sFBp */,_mK/* sFBv */,_mQ/* sFBB */,_mR/* sFBD */) : new T4(1,_mG/* sFBp */,_mK/* sFBv */,_mQ/* sFBB */,1);
                      };
                      if(_mN/* sFBy */>=_mO/* sFBz */){
                        if(255>_mO/* sFBz */){
                          if(0>_mO/* sFBz */){
                            return new F(function(){return _mP/* sFBA */(0);});
                          }else{
                            return new F(function(){return _mP/* sFBA */(_mO/* sFBz */);});
                          }
                        }else{
                          return new F(function(){return _mP/* sFBA */(255);});
                        }
                      }else{
                        var _mS/* sFBQ */ = _mO/* sFBz */-1|0;
                        if(255>_mS/* sFBQ */){
                          if(0>_mS/* sFBQ */){
                            return new F(function(){return _mP/* sFBA */(0);});
                          }else{
                            return new F(function(){return _mP/* sFBA */(_mS/* sFBQ */);});
                          }
                        }else{
                          return new F(function(){return _mP/* sFBA */(255);});
                        }
                      }
                    },
                    _mT/* sFBV */ = E(_lN/* sFyL */);
                    if(!_mT/* sFBV */._){
                      return new F(function(){return _mL/* sFBw */(0);});
                    }else{
                      return new F(function(){return _mL/* sFBw */(E(_mT/* sFBV */.a));});
                    }
                  };
                  if(_mH/* sFBs */>=_mI/* sFBt */){
                    if(255>_mI/* sFBt */){
                      if(0>_mI/* sFBt */){
                        return new F(function(){return _mJ/* sFBu */(0);});
                      }else{
                        return new F(function(){return _mJ/* sFBu */(_mI/* sFBt */);});
                      }
                    }else{
                      return new F(function(){return _mJ/* sFBu */(255);});
                    }
                  }else{
                    var _mU/* sFC6 */ = _mI/* sFBt */-1|0;
                    if(255>_mU/* sFC6 */){
                      if(0>_mU/* sFC6 */){
                        return new F(function(){return _mJ/* sFBu */(0);});
                      }else{
                        return new F(function(){return _mJ/* sFBu */(_mU/* sFC6 */);});
                      }
                    }else{
                      return new F(function(){return _mJ/* sFBu */(255);});
                    }
                  }
                };
                if(_mD/* sFBm */>=_mE/* sFBn */){
                  if(255>_mE/* sFBn */){
                    if(0>_mE/* sFBn */){
                      return new F(function(){return _mF/* sFBo */(0);});
                    }else{
                      return new F(function(){return _mF/* sFBo */(_mE/* sFBn */);});
                    }
                  }else{
                    return new F(function(){return _mF/* sFBo */(255);});
                  }
                }else{
                  var _mV/* sFCi */ = _mE/* sFBn */-1|0;
                  if(255>_mV/* sFCi */){
                    if(0>_mV/* sFCi */){
                      return new F(function(){return _mF/* sFBo */(0);});
                    }else{
                      return new F(function(){return _mF/* sFBo */(_mV/* sFCi */);});
                    }
                  }else{
                    return new F(function(){return _mF/* sFBo */(255);});
                  }
                }
              },
              _mW/* sFCn */ = E(_lJ/* sFyF */);
              if(!_mW/* sFCn */._){
                return B(_mB/* sFBk */(0));
              }else{
                return B(_mB/* sFBk */(E(_mW/* sFCn */.a)));
              }
            }) : new T(function(){
              var _mX/* sFCt */ = function(_mY/* sFCu */){
                var _mZ/* sFCv */ = _mY/* sFCu */*256,
                _n0/* sFCw */ = _mZ/* sFCv */&4294967295,
                _n1/* sFCx */ = function(_n2/* sFCy */){
                  var _n3/* sFCB */ = E(_lL/* sFyI */)*256,
                  _n4/* sFCC */ = _n3/* sFCB */&4294967295,
                  _n5/* sFCD */ = function(_n6/* sFCE */){
                    var _n7/* sFCF */ = function(_n8/* sFCG */){
                      var _n9/* sFCH */ = _n8/* sFCG */*256,
                      _na/* sFCI */ = _n9/* sFCH */&4294967295;
                      if(_n9/* sFCH */>=_na/* sFCI */){
                        return (255>_na/* sFCI */) ? (0>_na/* sFCI */) ? new T4(1,_n2/* sFCy */,_n6/* sFCE */,0,1) : new T4(1,_n2/* sFCy */,_n6/* sFCE */,_na/* sFCI */,1) : new T4(1,_n2/* sFCy */,_n6/* sFCE */,255,1);
                      }else{
                        var _nb/* sFCQ */ = _na/* sFCI */-1|0;
                        return (255>_nb/* sFCQ */) ? (0>_nb/* sFCQ */) ? new T4(1,_n2/* sFCy */,_n6/* sFCE */,0,1) : new T4(1,_n2/* sFCy */,_n6/* sFCE */,_nb/* sFCQ */,1) : new T4(1,_n2/* sFCy */,_n6/* sFCE */,255,1);
                      }
                    },
                    _nc/* sFCV */ = E(_lN/* sFyL */);
                    if(!_nc/* sFCV */._){
                      return new F(function(){return _n7/* sFCF */(0);});
                    }else{
                      return new F(function(){return _n7/* sFCF */(E(_nc/* sFCV */.a));});
                    }
                  };
                  if(_n3/* sFCB */>=_n4/* sFCC */){
                    if(255>_n4/* sFCC */){
                      if(0>_n4/* sFCC */){
                        return new F(function(){return _n5/* sFCD */(0);});
                      }else{
                        return new F(function(){return _n5/* sFCD */(_n4/* sFCC */);});
                      }
                    }else{
                      return new F(function(){return _n5/* sFCD */(255);});
                    }
                  }else{
                    var _nd/* sFD6 */ = _n4/* sFCC */-1|0;
                    if(255>_nd/* sFD6 */){
                      if(0>_nd/* sFD6 */){
                        return new F(function(){return _n5/* sFCD */(0);});
                      }else{
                        return new F(function(){return _n5/* sFCD */(_nd/* sFD6 */);});
                      }
                    }else{
                      return new F(function(){return _n5/* sFCD */(255);});
                    }
                  }
                };
                if(_mZ/* sFCv */>=_n0/* sFCw */){
                  if(255>_n0/* sFCw */){
                    if(0>_n0/* sFCw */){
                      return new F(function(){return _n1/* sFCx */(0);});
                    }else{
                      return new F(function(){return _n1/* sFCx */(_n0/* sFCw */);});
                    }
                  }else{
                    return new F(function(){return _n1/* sFCx */(255);});
                  }
                }else{
                  var _ne/* sFDi */ = _n0/* sFCw */-1|0;
                  if(255>_ne/* sFDi */){
                    if(0>_ne/* sFDi */){
                      return new F(function(){return _n1/* sFCx */(0);});
                    }else{
                      return new F(function(){return _n1/* sFCx */(_ne/* sFDi */);});
                    }
                  }else{
                    return new F(function(){return _n1/* sFCx */(255);});
                  }
                }
              },
              _nf/* sFDn */ = E(_lJ/* sFyF */);
              if(!_nf/* sFDn */._){
                return B(_mX/* sFCt */(0));
              }else{
                return B(_mX/* sFCt */(E(_nf/* sFDn */.a)));
              }
            });
          default:
            var _ng/* sFDA */ = rMV/* EXTERNAL */(E(E(_lO/* sFyM */.a).c)),
            _nh/* sFDD */ = E(_ng/* sFDA */);
            if(!_nh/* sFDD */._){
              var _ni/* sFDJ */ = B(A2(_lO/* sFyM */.b,E(_nh/* sFDD */.a).a, _/* EXTERNAL */)),
              _nj/* sFDL */ = _ni/* sFDJ */;
              return new T(function(){
                var _nk/* sFDM */ = function(_nl/* sFDN */){
                  var _nm/* sFDO */ = _nl/* sFDN */*256,
                  _nn/* sFDP */ = _nm/* sFDO */&4294967295,
                  _no/* sFDQ */ = function(_np/* sFDR */){
                    var _nq/* sFDU */ = E(_lL/* sFyI */)*256,
                    _nr/* sFDV */ = _nq/* sFDU */&4294967295,
                    _ns/* sFDW */ = function(_nt/* sFDX */){
                      var _nu/* sFDY */ = function(_nv/* sFDZ */){
                        var _nw/* sFE0 */ = _nv/* sFDZ */*256,
                        _nx/* sFE1 */ = _nw/* sFE0 */&4294967295,
                        _ny/* sFE2 */ = function(_nz/* sFE3 */){
                          var _nA/* sFE4 */ = E(_nj/* sFDL */);
                          return (1>_nA/* sFE4 */) ? (0>_nA/* sFE4 */) ? new T4(1,_np/* sFDR */,_nt/* sFDX */,_nz/* sFE3 */,0) : new T4(1,_np/* sFDR */,_nt/* sFDX */,_nz/* sFE3 */,_nA/* sFE4 */) : new T4(1,_np/* sFDR */,_nt/* sFDX */,_nz/* sFE3 */,1);
                        };
                        if(_nw/* sFE0 */>=_nx/* sFE1 */){
                          if(255>_nx/* sFE1 */){
                            if(0>_nx/* sFE1 */){
                              return new F(function(){return _ny/* sFE2 */(0);});
                            }else{
                              return new F(function(){return _ny/* sFE2 */(_nx/* sFE1 */);});
                            }
                          }else{
                            return new F(function(){return _ny/* sFE2 */(255);});
                          }
                        }else{
                          var _nB/* sFEh */ = _nx/* sFE1 */-1|0;
                          if(255>_nB/* sFEh */){
                            if(0>_nB/* sFEh */){
                              return new F(function(){return _ny/* sFE2 */(0);});
                            }else{
                              return new F(function(){return _ny/* sFE2 */(_nB/* sFEh */);});
                            }
                          }else{
                            return new F(function(){return _ny/* sFE2 */(255);});
                          }
                        }
                      },
                      _nC/* sFEm */ = E(_lN/* sFyL */);
                      if(!_nC/* sFEm */._){
                        return new F(function(){return _nu/* sFDY */(0);});
                      }else{
                        return new F(function(){return _nu/* sFDY */(E(_nC/* sFEm */.a));});
                      }
                    };
                    if(_nq/* sFDU */>=_nr/* sFDV */){
                      if(255>_nr/* sFDV */){
                        if(0>_nr/* sFDV */){
                          return new F(function(){return _ns/* sFDW */(0);});
                        }else{
                          return new F(function(){return _ns/* sFDW */(_nr/* sFDV */);});
                        }
                      }else{
                        return new F(function(){return _ns/* sFDW */(255);});
                      }
                    }else{
                      var _nD/* sFEx */ = _nr/* sFDV */-1|0;
                      if(255>_nD/* sFEx */){
                        if(0>_nD/* sFEx */){
                          return new F(function(){return _ns/* sFDW */(0);});
                        }else{
                          return new F(function(){return _ns/* sFDW */(_nD/* sFEx */);});
                        }
                      }else{
                        return new F(function(){return _ns/* sFDW */(255);});
                      }
                    }
                  };
                  if(_nm/* sFDO */>=_nn/* sFDP */){
                    if(255>_nn/* sFDP */){
                      if(0>_nn/* sFDP */){
                        return new F(function(){return _no/* sFDQ */(0);});
                      }else{
                        return new F(function(){return _no/* sFDQ */(_nn/* sFDP */);});
                      }
                    }else{
                      return new F(function(){return _no/* sFDQ */(255);});
                    }
                  }else{
                    var _nE/* sFEJ */ = _nn/* sFDP */-1|0;
                    if(255>_nE/* sFEJ */){
                      if(0>_nE/* sFEJ */){
                        return new F(function(){return _no/* sFDQ */(0);});
                      }else{
                        return new F(function(){return _no/* sFDQ */(_nE/* sFEJ */);});
                      }
                    }else{
                      return new F(function(){return _no/* sFDQ */(255);});
                    }
                  }
                },
                _nF/* sFEO */ = E(_lJ/* sFyF */);
                if(!_nF/* sFEO */._){
                  return B(_nk/* sFDM */(0));
                }else{
                  return B(_nk/* sFDM */(E(_nF/* sFEO */.a)));
                }
              });
            }else{
              return new T(function(){
                var _nG/* sFEU */ = function(_nH/* sFEV */){
                  var _nI/* sFEW */ = _nH/* sFEV */*256,
                  _nJ/* sFEX */ = _nI/* sFEW */&4294967295,
                  _nK/* sFEY */ = function(_nL/* sFEZ */){
                    var _nM/* sFF2 */ = E(_lL/* sFyI */)*256,
                    _nN/* sFF3 */ = _nM/* sFF2 */&4294967295,
                    _nO/* sFF4 */ = function(_nP/* sFF5 */){
                      var _nQ/* sFF6 */ = function(_nR/* sFF7 */){
                        var _nS/* sFF8 */ = _nR/* sFF7 */*256,
                        _nT/* sFF9 */ = _nS/* sFF8 */&4294967295;
                        if(_nS/* sFF8 */>=_nT/* sFF9 */){
                          return (255>_nT/* sFF9 */) ? (0>_nT/* sFF9 */) ? new T4(1,_nL/* sFEZ */,_nP/* sFF5 */,0,1) : new T4(1,_nL/* sFEZ */,_nP/* sFF5 */,_nT/* sFF9 */,1) : new T4(1,_nL/* sFEZ */,_nP/* sFF5 */,255,1);
                        }else{
                          var _nU/* sFFh */ = _nT/* sFF9 */-1|0;
                          return (255>_nU/* sFFh */) ? (0>_nU/* sFFh */) ? new T4(1,_nL/* sFEZ */,_nP/* sFF5 */,0,1) : new T4(1,_nL/* sFEZ */,_nP/* sFF5 */,_nU/* sFFh */,1) : new T4(1,_nL/* sFEZ */,_nP/* sFF5 */,255,1);
                        }
                      },
                      _nV/* sFFm */ = E(_lN/* sFyL */);
                      if(!_nV/* sFFm */._){
                        return new F(function(){return _nQ/* sFF6 */(0);});
                      }else{
                        return new F(function(){return _nQ/* sFF6 */(E(_nV/* sFFm */.a));});
                      }
                    };
                    if(_nM/* sFF2 */>=_nN/* sFF3 */){
                      if(255>_nN/* sFF3 */){
                        if(0>_nN/* sFF3 */){
                          return new F(function(){return _nO/* sFF4 */(0);});
                        }else{
                          return new F(function(){return _nO/* sFF4 */(_nN/* sFF3 */);});
                        }
                      }else{
                        return new F(function(){return _nO/* sFF4 */(255);});
                      }
                    }else{
                      var _nW/* sFFx */ = _nN/* sFF3 */-1|0;
                      if(255>_nW/* sFFx */){
                        if(0>_nW/* sFFx */){
                          return new F(function(){return _nO/* sFF4 */(0);});
                        }else{
                          return new F(function(){return _nO/* sFF4 */(_nW/* sFFx */);});
                        }
                      }else{
                        return new F(function(){return _nO/* sFF4 */(255);});
                      }
                    }
                  };
                  if(_nI/* sFEW */>=_nJ/* sFEX */){
                    if(255>_nJ/* sFEX */){
                      if(0>_nJ/* sFEX */){
                        return new F(function(){return _nK/* sFEY */(0);});
                      }else{
                        return new F(function(){return _nK/* sFEY */(_nJ/* sFEX */);});
                      }
                    }else{
                      return new F(function(){return _nK/* sFEY */(255);});
                    }
                  }else{
                    var _nX/* sFFJ */ = _nJ/* sFEX */-1|0;
                    if(255>_nX/* sFFJ */){
                      if(0>_nX/* sFFJ */){
                        return new F(function(){return _nK/* sFEY */(0);});
                      }else{
                        return new F(function(){return _nK/* sFEY */(_nX/* sFFJ */);});
                      }
                    }else{
                      return new F(function(){return _nK/* sFEY */(255);});
                    }
                  }
                },
                _nY/* sFFO */ = E(_lJ/* sFyF */);
                if(!_nY/* sFFO */._){
                  return B(_nG/* sFEU */(0));
                }else{
                  return B(_nG/* sFEU */(E(_nY/* sFFO */.a)));
                }
              });
            }
        }
      },
      _nZ/* sFFT */ = E(_lG/* sFyA */);
      switch(_nZ/* sFFT */._){
        case 0:
          return new F(function(){return _lM/* sFyJ */(_/* EXTERNAL */, new T1(1,_nZ/* sFFT */.a));});
          break;
        case 1:
          var _o0/* sFFX */ = B(A1(_nZ/* sFFT */.a,_/* EXTERNAL */));
          return new F(function(){return _lM/* sFyJ */(_/* EXTERNAL */, new T1(1,_o0/* sFFX */));});
          break;
        case 2:
          var _o1/* sFG9 */ = rMV/* EXTERNAL */(E(E(_nZ/* sFFT */.a).c)),
          _o2/* sFGc */ = E(_o1/* sFG9 */);
          if(!_o2/* sFGc */._){
            var _o3/* sFGg */ = new T(function(){
              return B(A1(_nZ/* sFFT */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_o2/* sFGc */.a));
              })));
            });
            return new F(function(){return _lM/* sFyJ */(_/* EXTERNAL */, new T1(1,_o3/* sFGg */));});
          }else{
            return new F(function(){return _lM/* sFyJ */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _o4/* sFGr */ = rMV/* EXTERNAL */(E(E(_nZ/* sFFT */.a).c)),
          _o5/* sFGu */ = E(_o4/* sFGr */);
          if(!_o5/* sFGu */._){
            var _o6/* sFGA */ = B(A2(_nZ/* sFFT */.b,E(_o5/* sFGu */.a).a, _/* EXTERNAL */));
            return new F(function(){return _lM/* sFyJ */(_/* EXTERNAL */, new T1(1,_o6/* sFGA */));});
          }else{
            return new F(function(){return _lM/* sFyJ */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _o7/* sFGF */ = function(_/* EXTERNAL */){
      var _o8/* sFGH */ = function(_/* EXTERNAL */, _o9/* sFGJ */){
        var _oa/* sFGK */ = E(_lH/* sFyB */);
        switch(_oa/* sFGK */._){
          case 0:
            return new T(function(){
              var _ob/* sFGM */ = function(_oc/* sFGN */){
                var _od/* sFGO */ = _oc/* sFGN */*256,
                _oe/* sFGP */ = _od/* sFGO */&4294967295,
                _of/* sFGQ */ = function(_og/* sFGR */){
                  var _oh/* sFGS */ = function(_oi/* sFGT */){
                    var _oj/* sFGU */ = _oi/* sFGT */*256,
                    _ok/* sFGV */ = _oj/* sFGU */&4294967295,
                    _ol/* sFGW */ = function(_om/* sFGX */){
                      var _on/* sFGY */ = E(_oa/* sFGK */.a);
                      return (1>_on/* sFGY */) ? (0>_on/* sFGY */) ? new T4(1,_og/* sFGR */,0,_om/* sFGX */,0) : new T4(1,_og/* sFGR */,0,_om/* sFGX */,_on/* sFGY */) : new T4(1,_og/* sFGR */,0,_om/* sFGX */,1);
                    };
                    if(_oj/* sFGU */>=_ok/* sFGV */){
                      if(255>_ok/* sFGV */){
                        if(0>_ok/* sFGV */){
                          return new F(function(){return _ol/* sFGW */(0);});
                        }else{
                          return new F(function(){return _ol/* sFGW */(_ok/* sFGV */);});
                        }
                      }else{
                        return new F(function(){return _ol/* sFGW */(255);});
                      }
                    }else{
                      var _oo/* sFHb */ = _ok/* sFGV */-1|0;
                      if(255>_oo/* sFHb */){
                        if(0>_oo/* sFHb */){
                          return new F(function(){return _ol/* sFGW */(0);});
                        }else{
                          return new F(function(){return _ol/* sFGW */(_oo/* sFHb */);});
                        }
                      }else{
                        return new F(function(){return _ol/* sFGW */(255);});
                      }
                    }
                  },
                  _op/* sFHg */ = E(_o9/* sFGJ */);
                  if(!_op/* sFHg */._){
                    return new F(function(){return _oh/* sFGS */(0);});
                  }else{
                    return new F(function(){return _oh/* sFGS */(E(_op/* sFHg */.a));});
                  }
                };
                if(_od/* sFGO */>=_oe/* sFGP */){
                  if(255>_oe/* sFGP */){
                    if(0>_oe/* sFGP */){
                      return new F(function(){return _of/* sFGQ */(0);});
                    }else{
                      return new F(function(){return _of/* sFGQ */(_oe/* sFGP */);});
                    }
                  }else{
                    return new F(function(){return _of/* sFGQ */(255);});
                  }
                }else{
                  var _oq/* sFHr */ = _oe/* sFGP */-1|0;
                  if(255>_oq/* sFHr */){
                    if(0>_oq/* sFHr */){
                      return new F(function(){return _of/* sFGQ */(0);});
                    }else{
                      return new F(function(){return _of/* sFGQ */(_oq/* sFHr */);});
                    }
                  }else{
                    return new F(function(){return _of/* sFGQ */(255);});
                  }
                }
              },
              _or/* sFHw */ = E(_lJ/* sFyF */);
              if(!_or/* sFHw */._){
                return B(_ob/* sFGM */(0));
              }else{
                return B(_ob/* sFGM */(E(_or/* sFHw */.a)));
              }
            });
          case 1:
            var _os/* sFHC */ = B(A1(_oa/* sFGK */.a,_/* EXTERNAL */)),
            _ot/* sFHE */ = _os/* sFHC */;
            return new T(function(){
              var _ou/* sFHF */ = function(_ov/* sFHG */){
                var _ow/* sFHH */ = _ov/* sFHG */*256,
                _ox/* sFHI */ = _ow/* sFHH */&4294967295,
                _oy/* sFHJ */ = function(_oz/* sFHK */){
                  var _oA/* sFHL */ = function(_oB/* sFHM */){
                    var _oC/* sFHN */ = _oB/* sFHM */*256,
                    _oD/* sFHO */ = _oC/* sFHN */&4294967295,
                    _oE/* sFHP */ = function(_oF/* sFHQ */){
                      var _oG/* sFHR */ = E(_ot/* sFHE */);
                      return (1>_oG/* sFHR */) ? (0>_oG/* sFHR */) ? new T4(1,_oz/* sFHK */,0,_oF/* sFHQ */,0) : new T4(1,_oz/* sFHK */,0,_oF/* sFHQ */,_oG/* sFHR */) : new T4(1,_oz/* sFHK */,0,_oF/* sFHQ */,1);
                    };
                    if(_oC/* sFHN */>=_oD/* sFHO */){
                      if(255>_oD/* sFHO */){
                        if(0>_oD/* sFHO */){
                          return new F(function(){return _oE/* sFHP */(0);});
                        }else{
                          return new F(function(){return _oE/* sFHP */(_oD/* sFHO */);});
                        }
                      }else{
                        return new F(function(){return _oE/* sFHP */(255);});
                      }
                    }else{
                      var _oH/* sFI4 */ = _oD/* sFHO */-1|0;
                      if(255>_oH/* sFI4 */){
                        if(0>_oH/* sFI4 */){
                          return new F(function(){return _oE/* sFHP */(0);});
                        }else{
                          return new F(function(){return _oE/* sFHP */(_oH/* sFI4 */);});
                        }
                      }else{
                        return new F(function(){return _oE/* sFHP */(255);});
                      }
                    }
                  },
                  _oI/* sFI9 */ = E(_o9/* sFGJ */);
                  if(!_oI/* sFI9 */._){
                    return new F(function(){return _oA/* sFHL */(0);});
                  }else{
                    return new F(function(){return _oA/* sFHL */(E(_oI/* sFI9 */.a));});
                  }
                };
                if(_ow/* sFHH */>=_ox/* sFHI */){
                  if(255>_ox/* sFHI */){
                    if(0>_ox/* sFHI */){
                      return new F(function(){return _oy/* sFHJ */(0);});
                    }else{
                      return new F(function(){return _oy/* sFHJ */(_ox/* sFHI */);});
                    }
                  }else{
                    return new F(function(){return _oy/* sFHJ */(255);});
                  }
                }else{
                  var _oJ/* sFIk */ = _ox/* sFHI */-1|0;
                  if(255>_oJ/* sFIk */){
                    if(0>_oJ/* sFIk */){
                      return new F(function(){return _oy/* sFHJ */(0);});
                    }else{
                      return new F(function(){return _oy/* sFHJ */(_oJ/* sFIk */);});
                    }
                  }else{
                    return new F(function(){return _oy/* sFHJ */(255);});
                  }
                }
              },
              _oK/* sFIp */ = E(_lJ/* sFyF */);
              if(!_oK/* sFIp */._){
                return B(_ou/* sFHF */(0));
              }else{
                return B(_ou/* sFHF */(E(_oK/* sFIp */.a)));
              }
            });
          case 2:
            var _oL/* sFIC */ = rMV/* EXTERNAL */(E(E(_oa/* sFGK */.a).c)),
            _oM/* sFIF */ = E(_oL/* sFIC */);
            return (_oM/* sFIF */._==0) ? new T(function(){
              var _oN/* sFII */ = function(_oO/* sFIJ */){
                var _oP/* sFIK */ = _oO/* sFIJ */*256,
                _oQ/* sFIL */ = _oP/* sFIK */&4294967295,
                _oR/* sFIM */ = function(_oS/* sFIN */){
                  var _oT/* sFIO */ = function(_oU/* sFIP */){
                    var _oV/* sFIQ */ = _oU/* sFIP */*256,
                    _oW/* sFIR */ = _oV/* sFIQ */&4294967295,
                    _oX/* sFIS */ = function(_oY/* sFIT */){
                      var _oZ/* sFIV */ = B(A1(_oa/* sFGK */.b,new T(function(){
                        return B(_fB/* Data.Tuple.fst */(_oM/* sFIF */.a));
                      })));
                      return (1>_oZ/* sFIV */) ? (0>_oZ/* sFIV */) ? new T4(1,_oS/* sFIN */,0,_oY/* sFIT */,0) : new T4(1,_oS/* sFIN */,0,_oY/* sFIT */,_oZ/* sFIV */) : new T4(1,_oS/* sFIN */,0,_oY/* sFIT */,1);
                    };
                    if(_oV/* sFIQ */>=_oW/* sFIR */){
                      if(255>_oW/* sFIR */){
                        if(0>_oW/* sFIR */){
                          return new F(function(){return _oX/* sFIS */(0);});
                        }else{
                          return new F(function(){return _oX/* sFIS */(_oW/* sFIR */);});
                        }
                      }else{
                        return new F(function(){return _oX/* sFIS */(255);});
                      }
                    }else{
                      var _p0/* sFJ8 */ = _oW/* sFIR */-1|0;
                      if(255>_p0/* sFJ8 */){
                        if(0>_p0/* sFJ8 */){
                          return new F(function(){return _oX/* sFIS */(0);});
                        }else{
                          return new F(function(){return _oX/* sFIS */(_p0/* sFJ8 */);});
                        }
                      }else{
                        return new F(function(){return _oX/* sFIS */(255);});
                      }
                    }
                  },
                  _p1/* sFJd */ = E(_o9/* sFGJ */);
                  if(!_p1/* sFJd */._){
                    return new F(function(){return _oT/* sFIO */(0);});
                  }else{
                    return new F(function(){return _oT/* sFIO */(E(_p1/* sFJd */.a));});
                  }
                };
                if(_oP/* sFIK */>=_oQ/* sFIL */){
                  if(255>_oQ/* sFIL */){
                    if(0>_oQ/* sFIL */){
                      return new F(function(){return _oR/* sFIM */(0);});
                    }else{
                      return new F(function(){return _oR/* sFIM */(_oQ/* sFIL */);});
                    }
                  }else{
                    return new F(function(){return _oR/* sFIM */(255);});
                  }
                }else{
                  var _p2/* sFJo */ = _oQ/* sFIL */-1|0;
                  if(255>_p2/* sFJo */){
                    if(0>_p2/* sFJo */){
                      return new F(function(){return _oR/* sFIM */(0);});
                    }else{
                      return new F(function(){return _oR/* sFIM */(_p2/* sFJo */);});
                    }
                  }else{
                    return new F(function(){return _oR/* sFIM */(255);});
                  }
                }
              },
              _p3/* sFJt */ = E(_lJ/* sFyF */);
              if(!_p3/* sFJt */._){
                return B(_oN/* sFII */(0));
              }else{
                return B(_oN/* sFII */(E(_p3/* sFJt */.a)));
              }
            }) : new T(function(){
              var _p4/* sFJz */ = function(_p5/* sFJA */){
                var _p6/* sFJB */ = _p5/* sFJA */*256,
                _p7/* sFJC */ = _p6/* sFJB */&4294967295,
                _p8/* sFJD */ = function(_p9/* sFJE */){
                  var _pa/* sFJF */ = function(_pb/* sFJG */){
                    var _pc/* sFJH */ = _pb/* sFJG */*256,
                    _pd/* sFJI */ = _pc/* sFJH */&4294967295;
                    if(_pc/* sFJH */>=_pd/* sFJI */){
                      return (255>_pd/* sFJI */) ? (0>_pd/* sFJI */) ? new T4(1,_p9/* sFJE */,0,0,1) : new T4(1,_p9/* sFJE */,0,_pd/* sFJI */,1) : new T4(1,_p9/* sFJE */,0,255,1);
                    }else{
                      var _pe/* sFJQ */ = _pd/* sFJI */-1|0;
                      return (255>_pe/* sFJQ */) ? (0>_pe/* sFJQ */) ? new T4(1,_p9/* sFJE */,0,0,1) : new T4(1,_p9/* sFJE */,0,_pe/* sFJQ */,1) : new T4(1,_p9/* sFJE */,0,255,1);
                    }
                  },
                  _pf/* sFJV */ = E(_o9/* sFGJ */);
                  if(!_pf/* sFJV */._){
                    return new F(function(){return _pa/* sFJF */(0);});
                  }else{
                    return new F(function(){return _pa/* sFJF */(E(_pf/* sFJV */.a));});
                  }
                };
                if(_p6/* sFJB */>=_p7/* sFJC */){
                  if(255>_p7/* sFJC */){
                    if(0>_p7/* sFJC */){
                      return new F(function(){return _p8/* sFJD */(0);});
                    }else{
                      return new F(function(){return _p8/* sFJD */(_p7/* sFJC */);});
                    }
                  }else{
                    return new F(function(){return _p8/* sFJD */(255);});
                  }
                }else{
                  var _pg/* sFK6 */ = _p7/* sFJC */-1|0;
                  if(255>_pg/* sFK6 */){
                    if(0>_pg/* sFK6 */){
                      return new F(function(){return _p8/* sFJD */(0);});
                    }else{
                      return new F(function(){return _p8/* sFJD */(_pg/* sFK6 */);});
                    }
                  }else{
                    return new F(function(){return _p8/* sFJD */(255);});
                  }
                }
              },
              _ph/* sFKb */ = E(_lJ/* sFyF */);
              if(!_ph/* sFKb */._){
                return B(_p4/* sFJz */(0));
              }else{
                return B(_p4/* sFJz */(E(_ph/* sFKb */.a)));
              }
            });
          default:
            var _pi/* sFKo */ = rMV/* EXTERNAL */(E(E(_oa/* sFGK */.a).c)),
            _pj/* sFKr */ = E(_pi/* sFKo */);
            if(!_pj/* sFKr */._){
              var _pk/* sFKx */ = B(A2(_oa/* sFGK */.b,E(_pj/* sFKr */.a).a, _/* EXTERNAL */)),
              _pl/* sFKz */ = _pk/* sFKx */;
              return new T(function(){
                var _pm/* sFKA */ = function(_pn/* sFKB */){
                  var _po/* sFKC */ = _pn/* sFKB */*256,
                  _pp/* sFKD */ = _po/* sFKC */&4294967295,
                  _pq/* sFKE */ = function(_pr/* sFKF */){
                    var _ps/* sFKG */ = function(_pt/* sFKH */){
                      var _pu/* sFKI */ = _pt/* sFKH */*256,
                      _pv/* sFKJ */ = _pu/* sFKI */&4294967295,
                      _pw/* sFKK */ = function(_px/* sFKL */){
                        var _py/* sFKM */ = E(_pl/* sFKz */);
                        return (1>_py/* sFKM */) ? (0>_py/* sFKM */) ? new T4(1,_pr/* sFKF */,0,_px/* sFKL */,0) : new T4(1,_pr/* sFKF */,0,_px/* sFKL */,_py/* sFKM */) : new T4(1,_pr/* sFKF */,0,_px/* sFKL */,1);
                      };
                      if(_pu/* sFKI */>=_pv/* sFKJ */){
                        if(255>_pv/* sFKJ */){
                          if(0>_pv/* sFKJ */){
                            return new F(function(){return _pw/* sFKK */(0);});
                          }else{
                            return new F(function(){return _pw/* sFKK */(_pv/* sFKJ */);});
                          }
                        }else{
                          return new F(function(){return _pw/* sFKK */(255);});
                        }
                      }else{
                        var _pz/* sFKZ */ = _pv/* sFKJ */-1|0;
                        if(255>_pz/* sFKZ */){
                          if(0>_pz/* sFKZ */){
                            return new F(function(){return _pw/* sFKK */(0);});
                          }else{
                            return new F(function(){return _pw/* sFKK */(_pz/* sFKZ */);});
                          }
                        }else{
                          return new F(function(){return _pw/* sFKK */(255);});
                        }
                      }
                    },
                    _pA/* sFL4 */ = E(_o9/* sFGJ */);
                    if(!_pA/* sFL4 */._){
                      return new F(function(){return _ps/* sFKG */(0);});
                    }else{
                      return new F(function(){return _ps/* sFKG */(E(_pA/* sFL4 */.a));});
                    }
                  };
                  if(_po/* sFKC */>=_pp/* sFKD */){
                    if(255>_pp/* sFKD */){
                      if(0>_pp/* sFKD */){
                        return new F(function(){return _pq/* sFKE */(0);});
                      }else{
                        return new F(function(){return _pq/* sFKE */(_pp/* sFKD */);});
                      }
                    }else{
                      return new F(function(){return _pq/* sFKE */(255);});
                    }
                  }else{
                    var _pB/* sFLf */ = _pp/* sFKD */-1|0;
                    if(255>_pB/* sFLf */){
                      if(0>_pB/* sFLf */){
                        return new F(function(){return _pq/* sFKE */(0);});
                      }else{
                        return new F(function(){return _pq/* sFKE */(_pB/* sFLf */);});
                      }
                    }else{
                      return new F(function(){return _pq/* sFKE */(255);});
                    }
                  }
                },
                _pC/* sFLk */ = E(_lJ/* sFyF */);
                if(!_pC/* sFLk */._){
                  return B(_pm/* sFKA */(0));
                }else{
                  return B(_pm/* sFKA */(E(_pC/* sFLk */.a)));
                }
              });
            }else{
              return new T(function(){
                var _pD/* sFLq */ = function(_pE/* sFLr */){
                  var _pF/* sFLs */ = _pE/* sFLr */*256,
                  _pG/* sFLt */ = _pF/* sFLs */&4294967295,
                  _pH/* sFLu */ = function(_pI/* sFLv */){
                    var _pJ/* sFLw */ = function(_pK/* sFLx */){
                      var _pL/* sFLy */ = _pK/* sFLx */*256,
                      _pM/* sFLz */ = _pL/* sFLy */&4294967295;
                      if(_pL/* sFLy */>=_pM/* sFLz */){
                        return (255>_pM/* sFLz */) ? (0>_pM/* sFLz */) ? new T4(1,_pI/* sFLv */,0,0,1) : new T4(1,_pI/* sFLv */,0,_pM/* sFLz */,1) : new T4(1,_pI/* sFLv */,0,255,1);
                      }else{
                        var _pN/* sFLH */ = _pM/* sFLz */-1|0;
                        return (255>_pN/* sFLH */) ? (0>_pN/* sFLH */) ? new T4(1,_pI/* sFLv */,0,0,1) : new T4(1,_pI/* sFLv */,0,_pN/* sFLH */,1) : new T4(1,_pI/* sFLv */,0,255,1);
                      }
                    },
                    _pO/* sFLM */ = E(_o9/* sFGJ */);
                    if(!_pO/* sFLM */._){
                      return new F(function(){return _pJ/* sFLw */(0);});
                    }else{
                      return new F(function(){return _pJ/* sFLw */(E(_pO/* sFLM */.a));});
                    }
                  };
                  if(_pF/* sFLs */>=_pG/* sFLt */){
                    if(255>_pG/* sFLt */){
                      if(0>_pG/* sFLt */){
                        return new F(function(){return _pH/* sFLu */(0);});
                      }else{
                        return new F(function(){return _pH/* sFLu */(_pG/* sFLt */);});
                      }
                    }else{
                      return new F(function(){return _pH/* sFLu */(255);});
                    }
                  }else{
                    var _pP/* sFLX */ = _pG/* sFLt */-1|0;
                    if(255>_pP/* sFLX */){
                      if(0>_pP/* sFLX */){
                        return new F(function(){return _pH/* sFLu */(0);});
                      }else{
                        return new F(function(){return _pH/* sFLu */(_pP/* sFLX */);});
                      }
                    }else{
                      return new F(function(){return _pH/* sFLu */(255);});
                    }
                  }
                },
                _pQ/* sFM2 */ = E(_lJ/* sFyF */);
                if(!_pQ/* sFM2 */._){
                  return B(_pD/* sFLq */(0));
                }else{
                  return B(_pD/* sFLq */(E(_pQ/* sFM2 */.a)));
                }
              });
            }
        }
      },
      _pR/* sFM7 */ = E(_lG/* sFyA */);
      switch(_pR/* sFM7 */._){
        case 0:
          return new F(function(){return _o8/* sFGH */(_/* EXTERNAL */, new T1(1,_pR/* sFM7 */.a));});
          break;
        case 1:
          var _pS/* sFMb */ = B(A1(_pR/* sFM7 */.a,_/* EXTERNAL */));
          return new F(function(){return _o8/* sFGH */(_/* EXTERNAL */, new T1(1,_pS/* sFMb */));});
          break;
        case 2:
          var _pT/* sFMn */ = rMV/* EXTERNAL */(E(E(_pR/* sFM7 */.a).c)),
          _pU/* sFMq */ = E(_pT/* sFMn */);
          if(!_pU/* sFMq */._){
            var _pV/* sFMu */ = new T(function(){
              return B(A1(_pR/* sFM7 */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_pU/* sFMq */.a));
              })));
            });
            return new F(function(){return _o8/* sFGH */(_/* EXTERNAL */, new T1(1,_pV/* sFMu */));});
          }else{
            return new F(function(){return _o8/* sFGH */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _pW/* sFMF */ = rMV/* EXTERNAL */(E(E(_pR/* sFM7 */.a).c)),
          _pX/* sFMI */ = E(_pW/* sFMF */);
          if(!_pX/* sFMI */._){
            var _pY/* sFMO */ = B(A2(_pR/* sFM7 */.b,E(_pX/* sFMI */.a).a, _/* EXTERNAL */));
            return new F(function(){return _o8/* sFGH */(_/* EXTERNAL */, new T1(1,_pY/* sFMO */));});
          }else{
            return new F(function(){return _o8/* sFGH */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _pZ/* sFMT */ = E(_lF/* sFyz */);
    switch(_pZ/* sFMT */._){
      case 0:
        return new F(function(){return _lK/* sFyG */(_/* EXTERNAL */, _pZ/* sFMT */.a);});
        break;
      case 1:
        var _q0/* sFMW */ = B(A1(_pZ/* sFMT */.a,_/* EXTERNAL */));
        return new F(function(){return _lK/* sFyG */(_/* EXTERNAL */, _q0/* sFMW */);});
        break;
      case 2:
        var _q1/* sFN7 */ = rMV/* EXTERNAL */(E(E(_pZ/* sFMT */.a).c)),
        _q2/* sFNa */ = E(_q1/* sFN7 */);
        if(!_q2/* sFNa */._){
          var _q3/* sFNh */ = new T(function(){
            return B(A1(_pZ/* sFMT */.b,new T(function(){
              return E(E(_q2/* sFNa */.a).a);
            })));
          });
          return new F(function(){return _lK/* sFyG */(_/* EXTERNAL */, _q3/* sFNh */);});
        }else{
          return new F(function(){return _o7/* sFGF */(_/* EXTERNAL */);});
        }
        break;
      default:
        var _q4/* sFNr */ = rMV/* EXTERNAL */(E(E(_pZ/* sFMT */.a).c)),
        _q5/* sFNu */ = E(_q4/* sFNr */);
        if(!_q5/* sFNu */._){
          var _q6/* sFNA */ = B(A2(_pZ/* sFMT */.b,E(_q5/* sFNu */.a).a, _/* EXTERNAL */));
          return new F(function(){return _lK/* sFyG */(_/* EXTERNAL */, _q6/* sFNA */);});
        }else{
          return new F(function(){return _o7/* sFGF */(_/* EXTERNAL */);});
        }
    }
  },
  _q7/* sFNE */ = E(_lE/* sFyy */);
  switch(_q7/* sFNE */._){
    case 0:
      return new F(function(){return _lI/* sFyD */(_/* EXTERNAL */, new T1(1,_q7/* sFNE */.a));});
      break;
    case 1:
      var _q8/* sFNI */ = B(A1(_q7/* sFNE */.a,_/* EXTERNAL */));
      return new F(function(){return _lI/* sFyD */(_/* EXTERNAL */, new T1(1,_q8/* sFNI */));});
      break;
    case 2:
      var _q9/* sFNU */ = rMV/* EXTERNAL */(E(E(_q7/* sFNE */.a).c)),
      _qa/* sFNX */ = E(_q9/* sFNU */);
      if(!_qa/* sFNX */._){
        var _qb/* sFO1 */ = new T(function(){
          return B(A1(_q7/* sFNE */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_qa/* sFNX */.a));
          })));
        });
        return new F(function(){return _lI/* sFyD */(_/* EXTERNAL */, new T1(1,_qb/* sFO1 */));});
      }else{
        return new F(function(){return _lI/* sFyD */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
      }
      break;
    default:
      var _qc/* sFOc */ = rMV/* EXTERNAL */(E(E(_q7/* sFNE */.a).c)),
      _qd/* sFOf */ = E(_qc/* sFOc */);
      if(!_qd/* sFOf */._){
        var _qe/* sFOl */ = B(A2(_q7/* sFNE */.b,E(_qd/* sFOf */.a).a, _/* EXTERNAL */));
        return new F(function(){return _lI/* sFyD */(_/* EXTERNAL */, new T1(1,_qe/* sFOl */));});
      }else{
        return new F(function(){return _lI/* sFyD */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
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
_ql/* $wcolor2JSString */ = function(_qm/* sFk6 */){
  var _qn/* sFk7 */ = E(_qm/* sFk6 */);
  if(!_qn/* sFk7 */._){
    var _qo/* sFkG */ = jsCat/* EXTERNAL */(new T2(1,_qg/* Core.Render.Internal.lvl2 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk7 */.a);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk7 */.b);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk7 */.c);
    }),_qk/* Core.Render.Internal.lvl6 */)))))), E(_qf/* Core.Render.Internal.lvl1 */));
    return E(_qo/* sFkG */);
  }else{
    var _qp/* sFlp */ = jsCat/* EXTERNAL */(new T2(1,_qi/* Core.Render.Internal.lvl5 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk7 */.a);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk7 */.b);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk7 */.c);
    }),new T2(1,_qh/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_qn/* sFk7 */.d);
    }),_qk/* Core.Render.Internal.lvl6 */)))))))), E(_qf/* Core.Render.Internal.lvl1 */));
    return E(_qp/* sFlp */);
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
_rB/* fill1 */ = function(_rC/* sFOq */, _rD/* sFOr */){
  return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T2(0,function(_rE/* sFOs */, _/* EXTERNAL */){
    var _rF/* sFOu */ = E(_rC/* sFOq */),
    _rG/* sFOz */ = B(_lD/* Core.Render.Internal.$wa */(_rF/* sFOu */.a, _rF/* sFOu */.b, _rF/* sFOu */.c, _rF/* sFOu */.d, _/* EXTERNAL */)),
    _rH/* sFOC */ = E(_rE/* sFOs */),
    _rI/* sFOK */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), _rH/* sFOC */, E(_rz/* Core.Render.Internal.fill2 */), B(_ql/* Core.Render.Internal.$wcolor2JSString */(_rG/* sFOz */))),
    _rJ/* sFOQ */ = __app1/* EXTERNAL */(E(_ry/* Core.Render.Internal.clip_f3 */), _rH/* sFOC */),
    _rK/* sFOX */ = B(A3(E(_rD/* sFOr */).b,_rH/* sFOC */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _rL/* sFP3 */ = __app1/* EXTERNAL */(E(_rA/* Core.Render.Internal.fill_f1 */), _rH/* sFOC */);
    return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */));});
},
_rM/* lvl */ = 50,
_rN/* lvl1 */ = 3,
_rO/* lvl10 */ = function(_rP/* sNuH */){
  return  -E(_rP/* sNuH */);
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
_sd/* $wpoly_fail */ = function(_se/* sb80 */){
  return new F(function(){return err/* EXTERNAL */(_sc/* Core.Ease.lvl */);});
},
_sf/* lvl1 */ = new T(function(){
  return B(_sd/* Core.Ease.$wpoly_fail */(_/* EXTERNAL */));
}),
_sg/* opLift */ = function(_sh/* sb81 */, _si/* sb82 */, _sj/* sb83 */){
  var _sk/* sb84 */ = function(_sl/* sb85 */){
    var _sm/* sbax */ = function(_/* EXTERNAL */){
      var _sn/* sb87 */ = function(_/* EXTERNAL */, _so/* sb89 */){
        var _sp/* sb8a */ = E(_sj/* sb83 */);
        switch(_sp/* sb8a */._){
          case 0:
            return new T(function(){
              return B(A2(_sh/* sb81 */,_so/* sb89 */, _sp/* sb8a */.a));
            });
          case 1:
            var _sq/* sb8e */ = B(A1(_sp/* sb8a */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb81 */,_so/* sb89 */, _sq/* sb8e */));
            });
          case 2:
            var _sr/* sb8q */ = rMV/* EXTERNAL */(E(E(_sp/* sb8a */.a).c)),
            _ss/* sb8t */ = E(_sr/* sb8q */);
            return (_ss/* sb8t */._==0) ? new T(function(){
              var _st/* sb8x */ = new T(function(){
                return B(A1(_sp/* sb8a */.b,new T(function(){
                  return B(_fB/* Data.Tuple.fst */(_ss/* sb8t */.a));
                })));
              });
              return B(A2(_sh/* sb81 */,_so/* sb89 */, _st/* sb8x */));
            }) : E(_sf/* Core.Ease.lvl1 */);
          default:
            var _su/* sb8J */ = rMV/* EXTERNAL */(E(E(_sp/* sb8a */.a).c)),
            _sv/* sb8M */ = E(_su/* sb8J */);
            if(!_sv/* sb8M */._){
              var _sw/* sb8S */ = B(A2(_sp/* sb8a */.b,E(_sv/* sb8M */.a).a, _/* EXTERNAL */));
              return new T(function(){
                return B(A2(_sh/* sb81 */,_so/* sb89 */, _sw/* sb8S */));
              });
            }else{
              return E(_sf/* Core.Ease.lvl1 */);
            }
        }
      },
      _sx/* sb8Y */ = function(_/* EXTERNAL */){
        var _sy/* sb90 */ = E(_sj/* sb83 */);
        switch(_sy/* sb90 */._){
          case 0:
            return E(_sf/* Core.Ease.lvl1 */);
          case 1:
            var _sz/* sb94 */ = B(A1(_sy/* sb90 */.a,_/* EXTERNAL */));
            return E(_sf/* Core.Ease.lvl1 */);
          case 2:
            var _sA/* sb9g */ = rMV/* EXTERNAL */(E(E(_sy/* sb90 */.a).c));
            return (E(_sA/* sb9g */)._==0) ? E(_sf/* Core.Ease.lvl1 */) : E(_sf/* Core.Ease.lvl1 */);
          default:
            var _sB/* sb9x */ = rMV/* EXTERNAL */(E(E(_sy/* sb90 */.a).c)),
            _sC/* sb9A */ = E(_sB/* sb9x */);
            if(!_sC/* sb9A */._){
              var _sD/* sb9G */ = B(A2(_sy/* sb90 */.b,E(_sC/* sb9A */.a).a, _/* EXTERNAL */));
              return E(_sf/* Core.Ease.lvl1 */);
            }else{
              return E(_sf/* Core.Ease.lvl1 */);
            }
        }
      },
      _sE/* sb9M */ = E(_si/* sb82 */);
      switch(_sE/* sb9M */._){
        case 0:
          return new F(function(){return _sn/* sb87 */(_/* EXTERNAL */, _sE/* sb9M */.a);});
          break;
        case 1:
          var _sF/* sb9P */ = B(A1(_sE/* sb9M */.a,_/* EXTERNAL */));
          return new F(function(){return _sn/* sb87 */(_/* EXTERNAL */, _sF/* sb9P */);});
          break;
        case 2:
          var _sG/* sba0 */ = rMV/* EXTERNAL */(E(E(_sE/* sb9M */.a).c)),
          _sH/* sba3 */ = E(_sG/* sba0 */);
          if(!_sH/* sba3 */._){
            var _sI/* sbaa */ = new T(function(){
              return B(A1(_sE/* sb9M */.b,new T(function(){
                return E(E(_sH/* sba3 */.a).a);
              })));
            });
            return new F(function(){return _sn/* sb87 */(_/* EXTERNAL */, _sI/* sbaa */);});
          }else{
            return new F(function(){return _sx/* sb8Y */(_/* EXTERNAL */);});
          }
          break;
        default:
          var _sJ/* sbak */ = rMV/* EXTERNAL */(E(E(_sE/* sb9M */.a).c)),
          _sK/* sban */ = E(_sJ/* sbak */);
          if(!_sK/* sban */._){
            var _sL/* sbat */ = B(A2(_sE/* sb9M */.b,E(_sK/* sban */.a).a, _/* EXTERNAL */));
            return new F(function(){return _sn/* sb87 */(_/* EXTERNAL */, _sL/* sbat */);});
          }else{
            return new F(function(){return _sx/* sb8Y */(_/* EXTERNAL */);});
          }
      }
    };
    return new T1(1,_sm/* sbax */);
  },
  _sM/* sbay */ = E(_si/* sb82 */);
  switch(_sM/* sbay */._){
    case 0:
      var _sN/* sbaz */ = _sM/* sbay */.a,
      _sO/* sbaA */ = E(_sj/* sb83 */);
      switch(_sO/* sbaA */._){
        case 0:
          return new T1(0,new T(function(){
            return B(A2(_sh/* sb81 */,_sN/* sbaz */, _sO/* sbaA */.a));
          }));
        case 1:
          var _sP/* sbaJ */ = function(_/* EXTERNAL */){
            var _sQ/* sbaF */ = B(A1(_sO/* sbaA */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb81 */,_sN/* sbaz */, _sQ/* sbaF */));
            });
          };
          return new T1(1,_sP/* sbaJ */);
        case 2:
          var _sR/* sbaM */ = new T(function(){
            return B(A1(_sh/* sb81 */,_sN/* sbaz */));
          }),
          _sS/* sbaP */ = function(_sT/* sbaN */){
            return new F(function(){return A1(_sR/* sbaM */,new T(function(){
              return B(A1(_sO/* sbaA */.b,_sT/* sbaN */));
            }));});
          };
          return new T2(2,_sO/* sbaA */.a,_sS/* sbaP */);
        default:
          var _sU/* sbaS */ = new T(function(){
            return B(A1(_sh/* sb81 */,_sN/* sbaz */));
          }),
          _sV/* sbaZ */ = function(_sW/* sbaT */, _/* EXTERNAL */){
            var _sX/* sbaV */ = B(A2(_sO/* sbaA */.b,_sW/* sbaT */, _/* EXTERNAL */));
            return new T(function(){
              return B(A1(_sU/* sbaS */,_sX/* sbaV */));
            });
          };
          return new T2(3,_sO/* sbaA */.a,_sV/* sbaZ */);
      }
      break;
    case 1:
      var _sY/* sbb0 */ = _sM/* sbay */.a,
      _sZ/* sbb1 */ = E(_sj/* sb83 */);
      switch(_sZ/* sbb1 */._){
        case 0:
          var _t0/* sbb8 */ = function(_/* EXTERNAL */){
            var _t1/* sbb4 */ = B(A1(_sY/* sbb0 */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb81 */,_t1/* sbb4 */, _sZ/* sbb1 */.a));
            });
          };
          return new T1(1,_t0/* sbb8 */);
        case 1:
          return new T1(1,function(_/* EXTERNAL */){
            return new F(function(){return _s6/* GHC.Base.liftA1 */(_sh/* sb81 */, _sY/* sbb0 */, _sZ/* sbb1 */.a, _/* EXTERNAL */);});
          });
        case 2:
          var _t2/* sbbk */ = function(_t3/* sbbd */, _/* EXTERNAL */){
            var _t4/* sbbf */ = B(A1(_sY/* sbb0 */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb81 */,_t4/* sbbf */, new T(function(){
                return B(A1(_sZ/* sbb1 */.b,_t3/* sbbd */));
              })));
            });
          };
          return new T2(3,_sZ/* sbb1 */.a,_t2/* sbbk */);
        default:
          var _t5/* sbbw */ = function(_t6/* sbbn */, _/* EXTERNAL */){
            var _t7/* sbbp */ = B(A1(_sY/* sbb0 */,_/* EXTERNAL */)),
            _t8/* sbbs */ = B(A2(_sZ/* sbb1 */.b,_t6/* sbbn */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb81 */,_t7/* sbbp */, _t8/* sbbs */));
            });
          };
          return new T2(3,_sZ/* sbb1 */.a,_t5/* sbbw */);
      }
      break;
    case 2:
      var _t9/* sbbx */ = _sM/* sbay */.a,
      _ta/* sbby */ = _sM/* sbay */.b,
      _tb/* sbbz */ = E(_sj/* sb83 */);
      switch(_tb/* sbbz */._){
        case 0:
          var _tc/* sbbD */ = function(_td/* sbbB */){
            return new F(function(){return A2(_sh/* sb81 */,new T(function(){
              return B(A1(_ta/* sbby */,_td/* sbbB */));
            }), _tb/* sbbz */.a);});
          };
          return new T2(2,_t9/* sbbx */,_tc/* sbbD */);
        case 1:
          var _te/* sbbM */ = function(_tf/* sbbF */, _/* EXTERNAL */){
            var _tg/* sbbH */ = B(A1(_tb/* sbbz */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb81 */,new T(function(){
                return B(A1(_ta/* sbby */,_tf/* sbbF */));
              }), _tg/* sbbH */));
            });
          };
          return new T2(3,_t9/* sbbx */,_te/* sbbM */);
        default:
          return new F(function(){return _sk/* sb84 */(_/* EXTERNAL */);});
      }
      break;
    default:
      var _th/* sbbN */ = _sM/* sbay */.a,
      _ti/* sbbO */ = _sM/* sbay */.b,
      _tj/* sbbP */ = E(_sj/* sb83 */);
      switch(_tj/* sbbP */._){
        case 0:
          var _tk/* sbbX */ = function(_tl/* sbbR */, _/* EXTERNAL */){
            var _tm/* sbbT */ = B(A2(_ti/* sbbO */,_tl/* sbbR */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb81 */,_tm/* sbbT */, _tj/* sbbP */.a));
            });
          };
          return new T2(3,_th/* sbbN */,_tk/* sbbX */);
        case 1:
          var _tn/* sbc8 */ = function(_to/* sbbZ */, _/* EXTERNAL */){
            var _tp/* sbc1 */ = B(A2(_ti/* sbbO */,_to/* sbbZ */, _/* EXTERNAL */)),
            _tq/* sbc4 */ = B(A1(_tj/* sbbP */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_sh/* sb81 */,_tp/* sbc1 */, _tq/* sbc4 */));
            });
          };
          return new T2(3,_th/* sbbN */,_tn/* sbc8 */);
        default:
          return new F(function(){return _sk/* sb84 */(_/* EXTERNAL */);});
      }
  }
},
_tr/* plusDouble */ = function(_ts/* s18yY */, _tt/* s18yZ */){
  return E(_ts/* s18yY */)+E(_tt/* s18yZ */);
},
_tu/* Zero */ = 0,
_tv/* sleep1 */ = function(_tw/* sc1a */, _tx/* sc1b */, _ty/* sc1c */){
  var _tz/* sc32 */ = function(_tA/* sc1d */){
    var _tB/* sc1e */ = E(_tA/* sc1d */),
    _tC/* sc1g */ = _tB/* sc1e */.b,
    _tD/* sc1h */ = new T(function(){
      return E(_tB/* sc1e */.a)+E(_tw/* sc1a */)|0;
    }),
    _tE/* sc31 */ = function(_/* EXTERNAL */){
      var _tF/* sc1o */ = nMV/* EXTERNAL */(_ii/* Core.World.Internal.waitUntil2 */),
      _tG/* sc1q */ = _tF/* sc1o */;
      return new T(function(){
        var _tH/* sc2Z */ = function(_tI/* sc2P */){
          var _tJ/* sc2T */ = new T(function(){
            return B(A1(_ty/* sc1c */,new T2(0,_7/* GHC.Tuple.() */,E(_tI/* sc2P */).b)));
          });
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_tG/* sc1q */, function(_tK/* sc2V */){
            return E(_tJ/* sc2T */);
          })));
        },
        _tL/* sc1s */ = new T2(0,_tD/* sc1h */,_tG/* sc1q */),
        _tM/* sc2O */ = function(_tN/* sc1u */){
          var _tO/* sc1v */ = new T(function(){
            var _tP/* sc1w */ = E(_tN/* sc1u */),
            _tQ/* sc1B */ = E(_tP/* sc1w */.c);
            if(!_tQ/* sc1B */._){
              var _tR/* sc1B#result */ = E(new T3(1,1,_tL/* sc1s */,E(_ax/* Data.PQueue.Internals.Nil */)));
            }else{
              var _tS/* sc1C */ = _tQ/* sc1B */.a,
              _tT/* sc1E */ = _tQ/* sc1B */.c,
              _tU/* sc1F */ = E(_tQ/* sc1B */.b),
              _tV/* sc1I */ = E(_tD/* sc1h */),
              _tW/* sc1K */ = E(_tU/* sc1F */.a);
              if(_tV/* sc1I */>=_tW/* sc1K */){
                if(_tV/* sc1I */!=_tW/* sc1K */){
                  var _tX/* sc1P#result */ = new T3(1,_tS/* sc1C */+1|0,_tU/* sc1F */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_tY/* sc1Q */, _tZ/* sc1R */){
                    var _u0/* sc1Y */ = E(E(_tY/* sc1Q */).a),
                    _u1/* sc20 */ = E(E(_tZ/* sc1R */).a);
                    return (_u0/* sc1Y */>=_u1/* sc20 */) ? _u0/* sc1Y */==_u1/* sc20 */ : true;
                  }, _tL/* sc1s */, _tu/* Data.PQueue.Internals.Zero */, _tT/* sc1E */))));
                }else{
                  var _tX/* sc1P#result */ = new T3(1,_tS/* sc1C */+1|0,_tL/* sc1s */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_u2/* sc28 */, _u3/* sc29 */){
                    var _u4/* sc2g */ = E(E(_u2/* sc28 */).a),
                    _u5/* sc2i */ = E(E(_u3/* sc29 */).a);
                    return (_u4/* sc2g */>=_u5/* sc2i */) ? _u4/* sc2g */==_u5/* sc2i */ : true;
                  }, _tU/* sc1F */, _tu/* Data.PQueue.Internals.Zero */, _tT/* sc1E */))));
                }
                var _u6/* sc1N#result */ = _tX/* sc1P#result */;
              }else{
                var _u6/* sc1N#result */ = new T3(1,_tS/* sc1C */+1|0,_tL/* sc1s */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_u7/* sc2q */, _u8/* sc2r */){
                  var _u9/* sc2y */ = E(E(_u7/* sc2q */).a),
                  _ua/* sc2A */ = E(E(_u8/* sc2r */).a);
                  return (_u9/* sc2y */>=_ua/* sc2A */) ? _u9/* sc2y */==_ua/* sc2A */ : true;
                }, _tU/* sc1F */, _tu/* Data.PQueue.Internals.Zero */, _tT/* sc1E */))));
              }
              var _tR/* sc1B#result */ = _u6/* sc1N#result */;
            }
            return new T4(0,E(_tP/* sc1w */.a),_tP/* sc1w */.b,E(_tR/* sc1B#result */),E(_tP/* sc1w */.d));
          });
          return function(_ub/* sc2K */, _uc/* sc2L */){
            return new F(function(){return A1(_uc/* sc2L */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,_tO/* sc1v */),_ub/* sc2K */));});
          };
        };
        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _tC/* sc1g */, _tM/* sc2O */, _tC/* sc1g */, _tH/* sc2Z */]));
      });
    };
    return new T1(0,_tE/* sc31 */);
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _tx/* sc1b */, _ar/* Core.World.Internal.a */, _tx/* sc1b */, _tz/* sc32 */]);});
},
_ud/* $wa */ = function(_ue/* sNuL */, _uf/* sNuM */, _ug/* sNuN */){
  return function(_/* EXTERNAL */){
    var _uh/* sNuP */ = nMV/* EXTERNAL */(_rW/* Motion.Bounce.lvl16 */),
    _ui/* sNuR */ = _uh/* sNuP */,
    _uj/* sNuT */ = function(_uk/* sNuU */){
      return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _lv/* Motion.Bounce.dur */, _lr/* Motion.Bounce.a4 */, _ui/* sNuR */, _lq/* Motion.Bounce.a */, function(_ul/* sNuV */){
        return E(_uk/* sNuU */);
      });});
    },
    _um/* sNuX */ = function(_un/* sNuY */){
      return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _lv/* Motion.Bounce.dur */, _lw/* Motion.Bounce.e */, _ui/* sNuR */, _rY/* Motion.Bounce.lvl3 */, function(_uo/* sNuZ */){
        return E(_un/* sNuY */);
      });});
    },
    _up/* sNCB */ = function(_/* EXTERNAL */){
      var _uq/* sNv2 */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
      _ur/* sNv4 */ = _uq/* sNv2 */,
      _us/* sNv6 */ = new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_ur/* sNv4 */),
      _ut/* sNCz */ = function(_/* EXTERNAL */){
        var _uu/* sNv8 */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
        _uv/* sNva */ = _uu/* sNv8 */,
        _uw/* sNCx */ = function(_/* EXTERNAL */){
          var _ux/* sNvd */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
          _uy/* sNvf */ = _ux/* sNvd */,
          _uz/* sNvh */ = new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_uy/* sNvf */),
          _uA/* sNCv */ = function(_/* EXTERNAL */){
            var _uB/* sNvj */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
            _uC/* sNvl */ = _uB/* sNvj */,
            _uD/* sNCt */ = function(_/* EXTERNAL */){
              var _uE/* sNvo */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
              _uF/* sNvq */ = _uE/* sNvo */,
              _uG/* sNCr */ = function(_/* EXTERNAL */){
                var _uH/* sNvt */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                _uI/* sNvv */ = _uH/* sNvt */,
                _uJ/* sNCp */ = function(_/* EXTERNAL */){
                  var _uK/* sNvy */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                  _uL/* sNvA */ = _uK/* sNvy */,
                  _uM/* sNvC */ = new T(function(){
                    return B(_jN/* Core.Ease.$wforceTo */(_uL/* sNvA */, _rX/* Motion.Bounce.lvl2 */));
                  }),
                  _uN/* sNCn */ = function(_/* EXTERNAL */){
                    var _uO/* sNvE */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                    _uP/* sNvG */ = _uO/* sNvE */,
                    _uQ/* sNCl */ = function(_/* EXTERNAL */){
                      var _uR/* sNvJ */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                      _uS/* sNvL */ = _uR/* sNvJ */,
                      _uT/* sNvN */ = new T(function(){
                        return B(_jN/* Core.Ease.$wforceTo */(_uS/* sNvL */, _rN/* Motion.Bounce.lvl1 */));
                      }),
                      _uU/* sNCj */ = function(_/* EXTERNAL */){
                        var _uV/* sNvP */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                        _uW/* sNvR */ = _uV/* sNvP */,
                        _uX/* sNvT */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_uW/* sNvR */, _rN/* Motion.Bounce.lvl1 */));
                        }),
                        _uY/* sNCh */ = function(_/* EXTERNAL */){
                          var _uZ/* sNvV */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                          _v0/* sNvX */ = _uZ/* sNvV */,
                          _v1/* sNCf */ = function(_/* EXTERNAL */){
                            var _v2/* sNw0 */ = nMV/* EXTERNAL */(_rT/* Motion.Bounce.lvl13 */),
                            _v3/* sNw2 */ = _v2/* sNw0 */;
                            return new T(function(){
                              var _v4/* sNw5 */ = function(_v5/* sNwa */){
                                return new F(function(){return _v6/* sNw7 */(E(_v5/* sNwa */).b);});
                              },
                              _v7/* sNw6 */ = function(_v8/* sNwe */){
                                return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_s0/* Motion.Bounce.lvl5 */, E(_v8/* sNwe */).b, _v4/* sNw5 */);});
                              },
                              _v6/* sNw7 */ = function(_v9/* sNwi */){
                                var _va/* sNAX */ = function(_vb/* sNwj */){
                                  var _vc/* sNwk */ = new T(function(){
                                    var _vd/* sNAQ */ = function(_ve/* sNwl */){
                                      var _vf/* sNwm */ = new T(function(){
                                        var _vg/* sNAJ */ = function(_vh/* sNwn */){
                                          var _vi/* sNwo */ = new T(function(){
                                            var _vj/* sNAC */ = function(_vk/* sNwp */){
                                              var _vl/* sNwq */ = new T(function(){
                                                var _vm/* sNAv */ = function(_vn/* sNwr */){
                                                  var _vo/* sNws */ = new T(function(){
                                                    var _vp/* sNwt */ = new T(function(){
                                                      return E(E(_vn/* sNwr */).a);
                                                    }),
                                                    _vq/* sNwx */ = new T(function(){
                                                      return B(_jN/* Core.Ease.$wforceTo */(_ur/* sNv4 */, new T(function(){
                                                        return (E(E(_vb/* sNwj */).a)+E(_vp/* sNwt */))*0.7;
                                                      })));
                                                    }),
                                                    _vr/* sNAo */ = function(_vs/* sNwI */){
                                                      var _vt/* sNwJ */ = new T(function(){
                                                        var _vu/* sNwK */ = new T(function(){
                                                          return E(E(_vs/* sNwI */).a);
                                                        }),
                                                        _vv/* sNwO */ = new T(function(){
                                                          return B(_jN/* Core.Ease.$wforceTo */(_uv/* sNva */, new T(function(){
                                                            return (E(E(_ve/* sNwl */).a)+E(_vu/* sNwK */))*0.7;
                                                          })));
                                                        }),
                                                        _vw/* sNAh */ = function(_vx/* sNwZ */){
                                                          var _vy/* sNx0 */ = new T(function(){
                                                            var _vz/* sNx1 */ = new T(function(){
                                                              return E(E(_vx/* sNwZ */).a);
                                                            }),
                                                            _vA/* sNx5 */ = new T(function(){
                                                              return B(_jN/* Core.Ease.$wforceTo */(_uy/* sNvf */, new T(function(){
                                                                return (E(E(_vh/* sNwn */).a)+E(_vz/* sNx1 */))*0.7;
                                                              })));
                                                            }),
                                                            _vB/* sNAa */ = function(_vC/* sNxg */){
                                                              var _vD/* sNxh */ = new T(function(){
                                                                var _vE/* sNxi */ = new T(function(){
                                                                  return E(E(_vC/* sNxg */).a);
                                                                }),
                                                                _vF/* sNxm */ = new T(function(){
                                                                  return B(_jN/* Core.Ease.$wforceTo */(_uC/* sNvl */, new T(function(){
                                                                    return (E(E(_vk/* sNwp */).a)+E(_vE/* sNxi */))*0.7;
                                                                  })));
                                                                }),
                                                                _vG/* sNxx */ = function(_vH/* sNxy */){
                                                                  return new F(function(){return A2(_vF/* sNxm */,E(_vH/* sNxy */).b, _v7/* sNw6 */);});
                                                                },
                                                                _vI/* sNxC */ = function(_vJ/* sNxD */){
                                                                  return new F(function(){return A2(_vA/* sNx5 */,E(_vJ/* sNxD */).b, _vG/* sNxx */);});
                                                                },
                                                                _vK/* sNxH */ = function(_vL/* sNxI */){
                                                                  return new F(function(){return A2(_vv/* sNwO */,E(_vL/* sNxI */).b, _vI/* sNxC */);});
                                                                },
                                                                _vM/* sNxM */ = function(_vN/* sNxN */){
                                                                  return new F(function(){return A2(_vq/* sNwx */,E(_vN/* sNxN */).b, _vK/* sNxH */);});
                                                                },
                                                                _vO/* sNA3 */ = function(_vP/* sNxR */){
                                                                  var _vQ/* sNxS */ = new T(function(){
                                                                    var _vR/* sNxT */ = new T(function(){
                                                                      return E(E(_vP/* sNxR */).a);
                                                                    }),
                                                                    _vS/* sNxX */ = new T(function(){
                                                                      return B(_jN/* Core.Ease.$wforceTo */(_uS/* sNvL */, new T(function(){
                                                                        return E(_vR/* sNxT */)*0.7;
                                                                      })));
                                                                    }),
                                                                    _vT/* sNy2 */ = new T(function(){
                                                                      return B(_jN/* Core.Ease.$wforceTo */(_uF/* sNvq */, new T(function(){
                                                                        return (E(_vp/* sNwt */)+E(_vR/* sNxT */))*0.7;
                                                                      })));
                                                                    }),
                                                                    _vU/* sNzW */ = function(_vV/* sNya */){
                                                                      var _vW/* sNyb */ = new T(function(){
                                                                        var _vX/* sNyc */ = new T(function(){
                                                                          return E(E(_vV/* sNya */).a);
                                                                        }),
                                                                        _vY/* sNyg */ = new T(function(){
                                                                          return B(_jN/* Core.Ease.$wforceTo */(_uW/* sNvR */, new T(function(){
                                                                            return E(_vX/* sNyc */)*0.7;
                                                                          })));
                                                                        }),
                                                                        _vZ/* sNyl */ = new T(function(){
                                                                          return B(_jN/* Core.Ease.$wforceTo */(_uI/* sNvv */, new T(function(){
                                                                            return (E(_vu/* sNwK */)+E(_vX/* sNyc */))*0.7;
                                                                          })));
                                                                        }),
                                                                        _w0/* sNzP */ = function(_w1/* sNyt */){
                                                                          var _w2/* sNyu */ = new T(function(){
                                                                            var _w3/* sNyv */ = new T(function(){
                                                                              return E(E(_w1/* sNyt */).a);
                                                                            }),
                                                                            _w4/* sNyz */ = new T(function(){
                                                                              return B(_jN/* Core.Ease.$wforceTo */(_v0/* sNvX */, new T(function(){
                                                                                return E(_w3/* sNyv */)*0.7;
                                                                              })));
                                                                            }),
                                                                            _w5/* sNyE */ = new T(function(){
                                                                              return B(_jN/* Core.Ease.$wforceTo */(_uL/* sNvA */, new T(function(){
                                                                                return (E(_vz/* sNx1 */)+E(_w3/* sNyv */))*0.7;
                                                                              })));
                                                                            }),
                                                                            _w6/* sNzI */ = function(_w7/* sNyM */){
                                                                              var _w8/* sNyN */ = new T(function(){
                                                                                var _w9/* sNyO */ = new T(function(){
                                                                                  return E(E(_w7/* sNyM */).a);
                                                                                }),
                                                                                _wa/* sNyS */ = new T(function(){
                                                                                  return B(_jN/* Core.Ease.$wforceTo */(_v3/* sNw2 */, new T(function(){
                                                                                    return E(_w9/* sNyO */)*0.7;
                                                                                  })));
                                                                                }),
                                                                                _wb/* sNyX */ = new T(function(){
                                                                                  return B(_jN/* Core.Ease.$wforceTo */(_uP/* sNvG */, new T(function(){
                                                                                    return (E(_vE/* sNxi */)+E(_w9/* sNyO */))*0.7;
                                                                                  })));
                                                                                }),
                                                                                _wc/* sNz5 */ = function(_wd/* sNz6 */){
                                                                                  return new F(function(){return A2(_wb/* sNyX */,E(_wd/* sNz6 */).b, _vM/* sNxM */);});
                                                                                },
                                                                                _we/* sNza */ = function(_wf/* sNzb */){
                                                                                  return new F(function(){return A2(_w5/* sNyE */,E(_wf/* sNzb */).b, _wc/* sNz5 */);});
                                                                                },
                                                                                _wg/* sNzf */ = function(_wh/* sNzg */){
                                                                                  return new F(function(){return A2(_vZ/* sNyl */,E(_wh/* sNzg */).b, _we/* sNza */);});
                                                                                },
                                                                                _wi/* sNzk */ = function(_wj/* sNzl */){
                                                                                  return new F(function(){return A2(_vT/* sNy2 */,E(_wj/* sNzl */).b, _wg/* sNzf */);});
                                                                                },
                                                                                _wk/* sNzp */ = function(_wl/* sNzq */){
                                                                                  return new F(function(){return A2(_wa/* sNyS */,E(_wl/* sNzq */).b, _wi/* sNzk */);});
                                                                                },
                                                                                _wm/* sNzu */ = function(_wn/* sNzv */){
                                                                                  return new F(function(){return A2(_w4/* sNyz */,E(_wn/* sNzv */).b, _wk/* sNzp */);});
                                                                                };
                                                                                return B(A2(_vS/* sNxX */,_v9/* sNwi */, function(_wo/* sNzz */){
                                                                                  return new F(function(){return A2(_vY/* sNyg */,E(_wo/* sNzz */).b, _wm/* sNzu */);});
                                                                                }));
                                                                              });
                                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_v3/* sNw2 */, _w7/* sNyM */, function(_wp/* sNzE */){
                                                                                return E(_w8/* sNyN */);
                                                                              })));
                                                                            };
                                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_v3/* sNw2 */, _w6/* sNzI */)));
                                                                          });
                                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_v0/* sNvX */, _w1/* sNyt */, function(_wq/* sNzL */){
                                                                            return E(_w2/* sNyu */);
                                                                          })));
                                                                        };
                                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_v0/* sNvX */, _w0/* sNzP */)));
                                                                      });
                                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uW/* sNvR */, _vV/* sNya */, function(_wr/* sNzS */){
                                                                        return E(_vW/* sNyb */);
                                                                      })));
                                                                    };
                                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uW/* sNvR */, _vU/* sNzW */)));
                                                                  });
                                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uS/* sNvL */, _vP/* sNxR */, function(_ws/* sNzZ */){
                                                                    return E(_vQ/* sNxS */);
                                                                  })));
                                                                };
                                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uS/* sNvL */, _vO/* sNA3 */)));
                                                              });
                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uP/* sNvG */, _vC/* sNxg */, function(_wt/* sNA6 */){
                                                                return E(_vD/* sNxh */);
                                                              })));
                                                            };
                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uP/* sNvG */, _vB/* sNAa */)));
                                                          });
                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uL/* sNvA */, _vx/* sNwZ */, function(_wu/* sNAd */){
                                                            return E(_vy/* sNx0 */);
                                                          })));
                                                        };
                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uL/* sNvA */, _vw/* sNAh */)));
                                                      });
                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uI/* sNvv */, _vs/* sNwI */, function(_wv/* sNAk */){
                                                        return E(_vt/* sNwJ */);
                                                      })));
                                                    };
                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uI/* sNvv */, _vr/* sNAo */)));
                                                  });
                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uF/* sNvq */, _vn/* sNwr */, function(_ww/* sNAr */){
                                                    return E(_vo/* sNws */);
                                                  })));
                                                };
                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uF/* sNvq */, _vm/* sNAv */)));
                                              });
                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uC/* sNvl */, _vk/* sNwp */, function(_wx/* sNAy */){
                                                return E(_vl/* sNwq */);
                                              })));
                                            };
                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uC/* sNvl */, _vj/* sNAC */)));
                                          });
                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uy/* sNvf */, _vh/* sNwn */, function(_wy/* sNAF */){
                                            return E(_vi/* sNwo */);
                                          })));
                                        };
                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uy/* sNvf */, _vg/* sNAJ */)));
                                      });
                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_uv/* sNva */, _ve/* sNwl */, function(_wz/* sNAM */){
                                        return E(_vf/* sNwm */);
                                      })));
                                    };
                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_uv/* sNva */, _vd/* sNAQ */)));
                                  });
                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_ur/* sNv4 */, _vb/* sNwj */, function(_wA/* sNAT */){
                                    return E(_vc/* sNwk */);
                                  })));
                                };
                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_ur/* sNv4 */, _va/* sNAX */)));
                              },
                              _wB/* sNB0 */ = new T(function(){
                                return B(_jN/* Core.Ease.$wforceTo */(_v3/* sNw2 */, _rZ/* Motion.Bounce.lvl4 */));
                              }),
                              _wC/* sNB2 */ = function(_wD/* sNBc */){
                                return new F(function(){return _wE/* sNB9 */(E(_wD/* sNBc */).b);});
                              },
                              _wF/* sNB3 */ = function(_wG/* sNBg */){
                                return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_rM/* Motion.Bounce.lvl */, E(_wG/* sNBg */).b, _wC/* sNB2 */);});
                              },
                              _wH/* sNB4 */ = function(_wI/* sNBk */){
                                return new F(function(){return A2(_uX/* sNvT */,E(_wI/* sNBk */).b, _wF/* sNB3 */);});
                              },
                              _wJ/* sNB5 */ = function(_wK/* sNBo */){
                                return new F(function(){return A2(_uT/* sNvN */,E(_wK/* sNBo */).b, _wH/* sNB4 */);});
                              },
                              _wL/* sNB6 */ = function(_wM/* sNBs */){
                                return new F(function(){return A2(_uM/* sNvC */,E(_wM/* sNBs */).b, _wJ/* sNB5 */);});
                              },
                              _wN/* sNB7 */ = function(_wO/* sNBw */){
                                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_uj/* sNuT */, E(_wO/* sNBw */).b, _wL/* sNB6 */)));
                              },
                              _wP/* sNB8 */ = function(_wQ/* sNBC */){
                                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_um/* sNuX */, E(_wQ/* sNBC */).b, _wN/* sNB7 */)));
                              },
                              _wE/* sNB9 */ = function(_wR/* sNBI */){
                                return new F(function(){return A2(_wB/* sNB0 */,_wR/* sNBI */, _wP/* sNB8 */);});
                              },
                              _wS/* sNCb */ = function(_wT/* sNC5 */, _wU/* sNC6 */){
                                return new T1(1,new T2(1,new T(function(){
                                  return B(_wE/* sNB9 */(_wT/* sNC5 */));
                                }),new T2(1,new T(function(){
                                  return B(_v6/* sNw7 */(_wT/* sNC5 */));
                                }),_6/* GHC.Types.[] */)));
                              },
                              _wV/* sNC4 */ = new T(function(){
                                var _wW/* sNC3 */ = new T(function(){
                                  var _wX/* sNBZ */ = B(_kB/* Core.Shape.Internal.$wrect */(new T(function(){
                                    return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _s5/* Motion.Bounce.lvl8 */, new T2(2,_us/* sNv6 */,_rO/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, new T2(2,new T3(0,_lv/* Motion.Bounce.dur */,_lw/* Motion.Bounce.e */,_ui/* sNuR */),_2E/* GHC.Base.id */), new T2(2,_uz/* sNvh */,_rO/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _s3/* Motion.Bounce.lvl7 */, new T2(2,_us/* sNv6 */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_uv/* sNva */),_2E/* GHC.Base.id */)));
                                  }), new T(function(){
                                    return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _s1/* Motion.Bounce.lvl6 */, new T2(2,_uz/* sNvh */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_uC/* sNvl */),_2E/* GHC.Base.id */)));
                                  })));
                                  return new T3(0,_wX/* sNBZ */.a,_wX/* sNBZ */.b,_wX/* sNBZ */.c);
                                });
                                return B(_rB/* Core.Render.Internal.fill1 */(_ue/* sNuL */, _wW/* sNC3 */));
                              });
                              return B(A1(_ug/* sNuN */,new T2(0,new T2(0,_wV/* sNC4 */,_wS/* sNCb */),_uf/* sNuM */)));
                            });
                          };
                          return new T1(0,_v1/* sNCf */);
                        };
                        return new T1(0,_uY/* sNCh */);
                      };
                      return new T1(0,_uU/* sNCj */);
                    };
                    return new T1(0,_uQ/* sNCl */);
                  };
                  return new T1(0,_uN/* sNCn */);
                };
                return new T1(0,_uJ/* sNCp */);
              };
              return new T1(0,_uG/* sNCr */);
            };
            return new T1(0,_uD/* sNCt */);
          };
          return new T1(0,_uA/* sNCv */);
        };
        return new T1(0,_uw/* sNCx */);
      };
      return new T1(0,_ut/* sNCz */);
    };
    return new T1(0,_up/* sNCB */);
  };
},
_wY/* bounceMot1 */ = function(_wZ/* sNCE */, _x0/* sNCF */, _x1/* sNCG */){
  return new T1(0,B(_ud/* Motion.Bounce.$wa */(_wZ/* sNCE */, _x0/* sNCF */, _x1/* sNCG */)));
},
_x2/* clip_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.restore();})");
}),
_x3/* clip5 */ = function(_x4/* sFxI */, _/* EXTERNAL */){
  var _x5/* sFxP */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), E(_x4/* sFxI */));
  return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_x6/* clip4 */ = new T2(0,_x3/* Core.Render.Internal.clip5 */,_7/* GHC.Tuple.() */),
_x7/* clip3 */ = new T(function(){
  return B(_rx/* Control.Monad.Skeleton.bone */(_x6/* Core.Render.Internal.clip4 */));
}),
_x8/* clip2 */ = function(_x9/* sFxS */){
  return E(_x7/* Core.Render.Internal.clip3 */);
},
_xa/* clip1 */ = new T1(1,_x8/* Core.Render.Internal.clip2 */),
_xb/* clip_f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.save();})");
}),
_xc/* getImage2 */ = function(_xd/* sFgp */, _xe/* sFgq */, _/* EXTERNAL */){
  var _xf/* sFgs */ = E(_xd/* sFgp */);
  switch(_xf/* sFgs */._){
    case 0:
      return new F(function(){return A2(_xe/* sFgq */,_xf/* sFgs */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _xg/* sFgv */ = B(A1(_xf/* sFgs */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_xe/* sFgq */,_xg/* sFgv */, _/* EXTERNAL */);});
      break;
    case 2:
      var _xh/* sFgG */ = rMV/* EXTERNAL */(E(E(_xf/* sFgs */.a).c)),
      _xi/* sFgJ */ = E(_xh/* sFgG */);
      if(!_xi/* sFgJ */._){
        var _xj/* sFgN */ = new T(function(){
          return B(A1(_xf/* sFgs */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_xi/* sFgJ */.a));
          })));
        });
        return new F(function(){return A2(_xe/* sFgq */,_xj/* sFgN */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _xk/* sFgX */ = rMV/* EXTERNAL */(E(E(_xf/* sFgs */.a).c)),
      _xl/* sFh0 */ = E(_xk/* sFgX */);
      if(!_xl/* sFh0 */._){
        var _xm/* sFh6 */ = B(A2(_xf/* sFgs */.b,E(_xl/* sFh0 */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_xe/* sFgq */,_xm/* sFh6 */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
  }
},
_xn/* lvl10 */ = "shadowBlur",
_xo/* lvl7 */ = "shadowColor",
_xp/* lvl8 */ = "shadowOffsetX",
_xq/* lvl9 */ = "shadowOffsetY",
_xr/* $wshadowed */ = function(_xs/* sFQ7 */, _xt/* sFQ8 */, _xu/* sFQ9 */, _xv/* sFQa */, _xw/* sFQb */){
  var _xx/* sFRs */ = function(_xy/* sFQc */, _/* EXTERNAL */){
    var _xz/* sFRr */ = function(_xA/* sFQe */, _/* EXTERNAL */){
      var _xB/* sFRq */ = function(_xC/* sFQg */, _/* EXTERNAL */){
        return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_xu/* sFQ9 */, function(_xD/* sFQi */, _/* EXTERNAL */){
          var _xE/* sFQk */ = E(_xv/* sFQa */),
          _xF/* sFQp */ = B(_lD/* Core.Render.Internal.$wa */(_xE/* sFQk */.a, _xE/* sFQk */.b, _xE/* sFQk */.c, _xE/* sFQk */.d, _/* EXTERNAL */)),
          _xG/* sFQs */ = E(_xy/* sFQc */),
          _xH/* sFQx */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _xG/* sFQs */),
          _xI/* sFQD */ = E(_ic/* Haste.DOM.Core.jsSet_f1 */),
          _xJ/* sFQG */ = __app3/* EXTERNAL */(_xI/* sFQD */, _xG/* sFQs */, E(_xo/* Core.Render.Internal.lvl7 */), B(_ql/* Core.Render.Internal.$wcolor2JSString */(_xF/* sFQp */))),
          _xK/* sFQO */ = String/* EXTERNAL */(E(_xA/* sFQe */)),
          _xL/* sFQS */ = __app3/* EXTERNAL */(_xI/* sFQD */, _xG/* sFQs */, E(_xp/* Core.Render.Internal.lvl8 */), _xK/* sFQO */),
          _xM/* sFR0 */ = String/* EXTERNAL */(E(_xC/* sFQg */)),
          _xN/* sFR4 */ = __app3/* EXTERNAL */(_xI/* sFQD */, _xG/* sFQs */, E(_xq/* Core.Render.Internal.lvl9 */), _xM/* sFR0 */),
          _xO/* sFRc */ = String/* EXTERNAL */(E(_xD/* sFQi */)),
          _xP/* sFRg */ = __app3/* EXTERNAL */(_xI/* sFQD */, _xG/* sFQs */, E(_xn/* Core.Render.Internal.lvl10 */), _xO/* sFRc */),
          _xQ/* sFRm */ = __app1/* EXTERNAL */(E(_ry/* Core.Render.Internal.clip_f3 */), _xG/* sFQs */);
          return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _/* EXTERNAL */);});
      };
      return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_xt/* sFQ8 */, _xB/* sFRq */, _/* EXTERNAL */);});
    };
    return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_xs/* sFQ7 */, _xz/* sFRr */, _/* EXTERNAL */);});
  },
  _xR/* sFRu */ = B(_rx/* Control.Monad.Skeleton.bone */(new T2(0,_xx/* sFRs */,_7/* GHC.Tuple.() */)));
  return new T2(0,E(_xR/* sFRu */.a),E(new T2(2,new T2(2,_xR/* sFRu */.b,new T1(1,function(_xS/* sFRx */){
    return E(_xw/* sFQb */);
  })),_xa/* Core.Render.Internal.clip1 */)));
},
_xT/* $fAffineShape_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,_){ctx.restore();})");
}),
_xU/* $fApplicativeShape4 */ = function(_/* EXTERNAL */){
  return _av/* GHC.Types.False */;
},
_xV/* $fApplicativeShape3 */ = function(_xW/* stcD */, _/* EXTERNAL */){
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
_y9/* $wtext */ = function(_ya/* stTg */, _yb/* stTh */, _yc/* stTi */, _yd/* stTj */, _ye/* stTk */, _yf/* stTl */, _yg/* stTm */){
  var _yh/* stVu */ = function(_yi/* stTn */, _yj/* stTo */, _yk/* stTp */, _/* EXTERNAL */){
    var _yl/* stVt */ = function(_ym/* stTr */, _yn/* stTs */, _yo/* stTt */, _/* EXTERNAL */){
      var _yp/* stVs */ = function(_yq/* stTv */, _yr/* stTw */, _ys/* stTx */, _/* EXTERNAL */){
        var _yt/* stVr */ = function(_yu/* stTz */, _yv/* stTA */, _yw/* stTB */, _/* EXTERNAL */){
          var _yx/* stTD */ = E(_yv/* stTA */),
          _yy/* stTH */ = E(_yw/* stTB */),
          _yz/* stTK */ = __app2/* EXTERNAL */(E(_xX/* Core.Shape.Internal.f1 */), _yx/* stTD */, _yy/* stTH */),
          _yA/* stTP */ = function(_yB/* stTQ */){
            var _yC/* stTR */ = function(_yD/* stTS */){
              var _yE/* stTW */ = eval/* EXTERNAL */(E(_y8/* Core.Shape.Internal.lvl6 */)),
              _yF/* stU4 */ = __app4/* EXTERNAL */(E(_yE/* stTW */), E(_ya/* stTg */), _yB/* stTQ */, _yD/* stTS */, _yx/* stTD */),
              _yG/* stUi */ = __app4/* EXTERNAL */(E(_y1/* Core.Shape.Internal.f5 */), E(_ym/* stTr */), E(_yq/* stTv */), _yx/* stTD */, _yy/* stTH */),
              _yH/* stUn */ = E(_yu/* stTz */)/10,
              _yI/* stUt */ = __app4/* EXTERNAL */(E(_xY/* Core.Shape.Internal.f2 */), _yH/* stUn */, _yH/* stUn */, _yx/* stTD */, _yy/* stTH */);
              if(!_yy/* stTH */){
                var _yJ/* stUJ */ = __app5/* EXTERNAL */(E(_xZ/* Core.Shape.Internal.f3 */), toJSStr/* EXTERNAL */(E(_yi/* stTn */)), 0, 0, _yx/* stTD */, false),
                _yK/* stUP */ = __app2/* EXTERNAL */(E(_xT/* Core.Shape.Internal.$fAffineShape_f1 */), _yx/* stTD */, false);
                return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }else{
                var _yL/* stV4 */ = __app5/* EXTERNAL */(E(_y0/* Core.Shape.Internal.f4 */), toJSStr/* EXTERNAL */(E(_yi/* stTn */)), 0, 0, _yx/* stTD */, true),
                _yM/* stVa */ = __app2/* EXTERNAL */(E(_xT/* Core.Shape.Internal.$fAffineShape_f1 */), _yx/* stTD */, true);
                return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }
            };
            switch(E(_yd/* stTj */)){
              case 0:
                return new F(function(){return _yC/* stTR */(E(_y4/* Core.Shape.Internal.lvl2 */));});
                break;
              case 1:
                return new F(function(){return _yC/* stTR */(E(_y3/* Core.Shape.Internal.lvl1 */));});
                break;
              default:
                return new F(function(){return _yC/* stTR */(E(_y2/* Core.Shape.Internal.lvl */));});
            }
          };
          switch(E(_yc/* stTi */)){
            case 0:
              return new F(function(){return _yA/* stTP */(E(_y7/* Core.Shape.Internal.lvl5 */));});
              break;
            case 1:
              return new F(function(){return _yA/* stTP */(E(_y6/* Core.Shape.Internal.lvl4 */));});
              break;
            default:
              return new F(function(){return _yA/* stTP */(E(_y5/* Core.Shape.Internal.lvl3 */));});
          }
        };
        return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_yg/* stTm */, _yt/* stVr */, _yr/* stTw */, _ys/* stTx */, _/* EXTERNAL */);});
      };
      return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_yf/* stTl */, _yp/* stVs */, _yn/* stTs */, _yo/* stTt */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_ye/* stTk */, _yl/* stVt */, _yj/* stTo */, _yk/* stTp */, _/* EXTERNAL */);});
  };
  return new T3(0,_xV/* Core.Shape.Internal.$fApplicativeShape3 */,function(_lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_yb/* stTh */, _yh/* stVu */, _lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */);});
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
  var _yX/* s7Ls */ = B(_kB/* Core.Shape.Internal.$wrect */(_yT/* Motion.Main.lvl4 */, _yT/* Motion.Main.lvl4 */, _yV/* Motion.Main.sz */, _yV/* Motion.Main.sz */));
  return new T3(0,_yX/* s7Ls */.a,_yX/* s7Ls */.b,_yX/* s7Ls */.c);
}),
_yY/* black1 */ = new T1(0,_f3/* Core.Render.Internal.applyTransform2 */),
_yZ/* white */ = new T4(0,_yY/* Core.Render.Internal.black1 */,_yY/* Core.Render.Internal.black1 */,_yY/* Core.Render.Internal.black1 */,_yY/* Core.Render.Internal.black1 */),
_z0/* a17 */ = new T(function(){
  return B(_rB/* Core.Render.Internal.fill1 */(_yZ/* Core.Render.Internal.white */, _yW/* Motion.Main.shape */));
}),
_z1/* a23 */ = function(_z2/* s7Lw */, _z3/* s7Lx */){
  return new F(function(){return A1(_z3/* s7Lx */,new T2(0,_7/* GHC.Tuple.() */,_z2/* s7Lw */));});
},
_z4/* black2 */ = new T1(0,_f2/* Core.Render.Internal.applyTransform1 */),
_z5/* black */ = new T4(0,_z4/* Core.Render.Internal.black2 */,_z4/* Core.Render.Internal.black2 */,_z4/* Core.Render.Internal.black2 */,_yY/* Core.Render.Internal.black1 */),
_z6/* Leave */ = 2,
_z7/* lvl2 */ = function(_z8/* sZro */){
  switch(E(_z8/* sZro */)){
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
_z9/* lvl3 */ = function(_za/* sZrq */){
  return (E(_za/* sZrq */)==2) ? true : false;
},
_zb/* lvl4 */ = function(_zc/* sZrs */){
  switch(E(_zc/* sZrs */)){
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
_zj/* button */ = function(_zk/* sZru */, _zl/* sZrv */, _zm/* sZrw */, _zn/* sZrx */){
  var _zo/* sZry */ = new T(function(){
    var _zp/* sZrz */ = new T(function(){
      var _zq/* sZrH */ = function(_zr/* sZrA */, _zs/* sZrB */){
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zn/* sZrx */, function(_zt/* sZrC */){
          return new F(function(){return A1(_zs/* sZrB */,new T2(0,_zt/* sZrC */,_zr/* sZrA */));});
        })));
      };
      return B(_zd/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _zb/* Core.UI.lvl4 */, _zq/* sZrH */));
    }),
    _zu/* sZs4 */ = function(_zv/* sZrI */, _zw/* sZrJ */){
      var _zx/* sZrK */ = new T(function(){
        var _zy/* sZrX */ = function(_zz/* sZrL */){
          var _zA/* sZrM */ = E(_zz/* sZrL */),
          _zB/* sZrO */ = _zA/* sZrM */.b,
          _zC/* sZrP */ = E(_zA/* sZrM */.a);
          if(_zC/* sZrP */==6){
            return new F(function(){return A1(_zw/* sZrJ */,new T2(0,_z6/* Core.View.Leave */,_zB/* sZrO */));});
          }else{
            return new F(function(){return A2(_zm/* sZrw */,_zB/* sZrO */, function(_zD/* sZrQ */){
              return new F(function(){return A1(_zw/* sZrJ */,new T2(0,_zC/* sZrP */,E(_zD/* sZrQ */).b));});
            });});
          }
        };
        return B(A2(_zp/* sZrz */,_zv/* sZrI */, _zy/* sZrX */));
      });
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zn/* sZrx */, function(_zE/* sZrY */){
        var _zF/* sZrZ */ = E(_zE/* sZrY */);
        if(_zF/* sZrZ */==3){
          return E(_zx/* sZrK */);
        }else{
          return new F(function(){return A1(_zw/* sZrJ */,new T2(0,_zF/* sZrZ */,_zv/* sZrI */));});
        }
      })));
    };
    return B(_zd/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _z9/* Core.UI.lvl3 */, _zu/* sZs4 */));
  }),
  _zG/* sZs5 */ = new T(function(){
    var _zH/* sZsd */ = function(_zI/* sZs6 */, _zJ/* sZs7 */){
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zn/* sZrx */, function(_zK/* sZs8 */){
        return new F(function(){return A1(_zJ/* sZs7 */,new T2(0,_zK/* sZs8 */,_zI/* sZs6 */));});
      })));
    };
    return B(_zd/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _z7/* Core.UI.lvl2 */, _zH/* sZsd */));
  }),
  _zL/* sZse */ = function(_zM/* sZsf */){
    var _zN/* sZsg */ = new T(function(){
      return B(A1(_zk/* sZru */,_zM/* sZsf */));
    }),
    _zO/* sZsC */ = function(_zP/* sZsh */){
      var _zQ/* sZsi */ = function(_zR/* sZsj */){
        return new F(function(){return A2(_zL/* sZse */,E(_zR/* sZsj */).b, _zP/* sZsh */);});
      },
      _zS/* sZsn */ = function(_zT/* sZso */){
        return new F(function(){return A2(_zo/* sZry */,E(_zT/* sZso */).b, _zQ/* sZsi */);});
      },
      _zU/* sZss */ = function(_zV/* sZst */){
        return new F(function(){return A2(_zl/* sZrv */,E(_zV/* sZst */).b, _zS/* sZsn */);});
      };
      return new F(function(){return A1(_zN/* sZsg */,function(_zW/* sZsx */){
        return new F(function(){return A2(_zG/* sZs5 */,E(_zW/* sZsx */).b, _zU/* sZss */);});
      });});
    };
    return E(_zO/* sZsC */);
  };
  return E(_zL/* sZse */);
},
_zX/* clip_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.clip();})");
}),
_zY/* clip */ = function(_zZ/* sFxT */, _A0/* sFxU */){
  var _A1/* sFyq */ = B(_rx/* Control.Monad.Skeleton.bone */(new T2(0,function(_A2/* sFxV */, _/* EXTERNAL */){
    var _A3/* sFxX */ = E(_A2/* sFxV */),
    _A4/* sFy2 */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _A3/* sFxX */),
    _A5/* sFy8 */ = __app1/* EXTERNAL */(E(_ry/* Core.Render.Internal.clip_f3 */), _A3/* sFxX */),
    _A6/* sFyf */ = B(A3(E(_zZ/* sFxT */).b,_A3/* sFxX */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _A7/* sFyl */ = __app1/* EXTERNAL */(E(_zX/* Core.Render.Internal.clip_f2 */), _A3/* sFxX */);
    return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */)));
  return new T2(0,E(_A1/* sFyq */.a),E(new T2(2,new T2(2,_A1/* sFyq */.b,new T1(1,function(_A8/* sFyt */){
    return E(_A0/* sFxU */);
  })),_xa/* Core.Render.Internal.clip1 */)));
},
_A9/* easeTo2 */ = function(_Aa/* sbim */, _Ab/* sbin */){
  return new F(function(){return A1(_Ab/* sbin */,new T2(0,_7/* GHC.Tuple.() */,_Aa/* sbim */));});
},
_Ac/* easeTo1 */ = function(_Ad/* sbip */, _Ae/* B2 */, _Af/* B1 */){
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
_AM/* lvl32 */ = function(_AN/* s7Lz */){
  var _AO/* s7LA */ = E(_AN/* s7Lz */);
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
_AZ/* $fAffineShape1 */ = function(_B0/* stnh */, _B1/* stni */, _B2/* stnj */, _/* EXTERNAL */){
  var _B3/* stns */ = __app2/* EXTERNAL */(E(_xT/* Core.Shape.Internal.$fAffineShape_f1 */), E(_B1/* stni */), E(_B2/* stnj */));
  return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_B4/* $w$caffine */ = function(_B5/* stnv */, _B6/* stnw */, _B7/* stnx */, _B8/* stny */, _B9/* stnz */, _Ba/* stnA */, _Bb/* stnB */){
  var _Bc/* stpl */ = function(_Bd/* stoX */, _Be/* stoY */, _Bf/* stoZ */, _/* EXTERNAL */){
    var _Bg/* stpk */ = function(_Bh/* stp1 */, _Bi/* stp2 */, _Bj/* stp3 */, _/* EXTERNAL */){
      var _Bk/* stpj */ = function(_Bl/* stp5 */, _Bm/* stp6 */, _Bn/* stp7 */, _/* EXTERNAL */){
        var _Bo/* stpi */ = function(_Bp/* stp9 */, _Bq/* stpa */, _Br/* stpb */, _/* EXTERNAL */){
          return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B9/* stnz */, function(_Bs/* stpd */, _Bt/* stpe */, _Bu/* stpf */, _/* EXTERNAL */){
            return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_Ba/* stnA */, _AZ/* Core.Shape.Internal.$fAffineShape1 */, _Bt/* stpe */, _Bu/* stpf */, _/* EXTERNAL */);});
          }, _Bq/* stpa */, _Br/* stpb */, _/* EXTERNAL */);});
        };
        return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B8/* stny */, _Bo/* stpi */, _Bm/* stp6 */, _Bn/* stp7 */, _/* EXTERNAL */);});
      };
      return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B7/* stnx */, _Bk/* stpj */, _Bi/* stp2 */, _Bj/* stp3 */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B6/* stnw */, _Bg/* stpk */, _Be/* stoY */, _Bf/* stoZ */, _/* EXTERNAL */);});
  },
  _Bv/* stoW */ = function(_Bw/* stnC */, _/* EXTERNAL */){
    var _Bx/* stnE */ = E(_Bw/* stnC */),
    _By/* stnF */ = _Bx/* stnE */.a,
    _Bz/* stnG */ = _Bx/* stnE */.b,
    _BA/* stoV */ = function(_BB/* stnH */, _/* EXTERNAL */){
      var _BC/* stoU */ = function(_BD/* stnJ */, _/* EXTERNAL */){
        var _BE/* stoT */ = function(_BF/* stnL */, _/* EXTERNAL */){
          var _BG/* stoS */ = function(_BH/* stnN */, _/* EXTERNAL */){
            var _BI/* stoR */ = function(_BJ/* stnP */, _/* EXTERNAL */){
              var _BK/* stoQ */ = function(_BL/* stnR */){
                var _BM/* stnS */ = new T(function(){
                  return E(_BD/* stnJ */)*E(_BH/* stnN */)-E(_BB/* stnH */)*E(_BJ/* stnP */);
                });
                return new F(function(){return A1(_Bb/* stnB */,new T2(0,new T(function(){
                  var _BN/* sto4 */ = E(_BD/* stnJ */),
                  _BO/* stoa */ = E(_BJ/* stnP */);
                  return ( -(_BN/* sto4 */*E(_BL/* stnR */))+_BN/* sto4 */*E(_Bz/* stnG */)+_BO/* stoa */*E(_BF/* stnL */)-_BO/* stoa */*E(_By/* stnF */))/E(_BM/* stnS */);
                }),new T(function(){
                  var _BP/* stos */ = E(_BB/* stnH */),
                  _BQ/* stoy */ = E(_BH/* stnN */);
                  return (_BP/* stos */*E(_BL/* stnR */)-_BP/* stos */*E(_Bz/* stnG */)-_BQ/* stoy */*E(_BF/* stnL */)+_BQ/* stoy */*E(_By/* stnF */))/E(_BM/* stnS */);
                })));});
              };
              return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_Ba/* stnA */, _BK/* stoQ */, _/* EXTERNAL */);});
            };
            return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B9/* stnz */, _BI/* stoR */, _/* EXTERNAL */);});
          };
          return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B8/* stny */, _BG/* stoS */, _/* EXTERNAL */);});
        };
        return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B7/* stnx */, _BE/* stoT */, _/* EXTERNAL */);});
      };
      return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B6/* stnw */, _BC/* stoU */, _/* EXTERNAL */);});
    };
    return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_B5/* stnv */, _BA/* stoV */, _/* EXTERNAL */);});
  };
  return new T3(0,_Bv/* stoW */,function(_lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_B5/* stnv */, _Bc/* stpl */, _lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */);});
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
_Cp/* lvl23 */ = function(_Cq/* sWfn */, _Cr/* sWfo */){
  return new F(function(){return A1(_Cr/* sWfo */,new T2(0,_7/* GHC.Tuple.() */,_Cq/* sWfn */));});
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
_CQ/* makeView */ = function(_CR/* sWfq */, _CS/* sWfr */, _CT/* sWfs */, _CU/* sWft */){
  var _CV/* sWfu */ = new T(function(){
    return B(A1(_CR/* sWfq */,_z6/* Core.View.Leave */));
  }),
  _CW/* sWfv */ = new T(function(){
    return B(A1(_CR/* sWfq */,_Cl/* Core.View.Enter */));
  }),
  _CX/* sWfw */ = new T(function(){
    return B(A1(_CR/* sWfq */,_Ck/* Core.View.Drag */));
  }),
  _CY/* sWfx */ = new T(function(){
    return B(_CI/* Haste.Concurrent.spawn */(_8l/* Core.World.Internal.$fMonadConcWorld */, _CU/* sWft */));
  }),
  _CZ/* sWfy */ = new T(function(){
    return B(A1(_CR/* sWfq */,_Cj/* Core.View.Cancel */));
  }),
  _D0/* sWfz */ = new T(function(){
    return B(A1(_CR/* sWfq */,_Co/* Core.View.Release */));
  }),
  _D1/* sWfA */ = new T(function(){
    return B(A1(_CR/* sWfq */,_Cn/* Core.View.Press */));
  }),
  _D2/* sWfB */ = new T(function(){
    return B(A1(_CR/* sWfq */,_Cm/* Core.View.Move */));
  }),
  _D3/* sWkQ */ = function(_D4/* sWfC */){
    var _D5/* sWfD */ = new T(function(){
      return B(A1(_CY/* sWfx */,_D4/* sWfC */));
    }),
    _D6/* sWkP */ = function(_D7/* sWfE */){
      var _D8/* sWkO */ = function(_D9/* sWfF */){
        var _Da/* sWfG */ = E(_D9/* sWfF */),
        _Db/* sWfH */ = _Da/* sWfG */.a,
        _Dc/* sWfI */ = _Da/* sWfG */.b,
        _Dd/* sWfJ */ = new T(function(){
          var _De/* sWfK */ = E(_CV/* sWfu */);
          if(!_De/* sWfK */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sWfH */, _De/* sWfK */.a));
          }
        }),
        _Df/* sWfM */ = new T(function(){
          var _Dg/* sWfN */ = E(_CW/* sWfv */);
          if(!_Dg/* sWfN */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sWfH */, _Dg/* sWfN */.a));
          }
        }),
        _Dh/* sWfP */ = new T(function(){
          var _Di/* sWfQ */ = E(_CX/* sWfw */);
          if(!_Di/* sWfQ */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sWfH */, _Di/* sWfQ */.a));
          }
        }),
        _Dj/* sWfS */ = new T(function(){
          var _Dk/* sWfT */ = E(_CZ/* sWfy */);
          if(!_Dk/* sWfT */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sWfH */, _Dk/* sWfT */.a));
          }
        }),
        _Dl/* sWfV */ = new T(function(){
          var _Dm/* sWfW */ = E(_D0/* sWfz */);
          if(!_Dm/* sWfW */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sWfH */, _Dm/* sWfW */.a));
          }
        }),
        _Dn/* sWfY */ = new T(function(){
          var _Do/* sWfZ */ = E(_D1/* sWfA */);
          if(!_Do/* sWfZ */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sWfH */, _Do/* sWfZ */.a));
          }
        }),
        _Dp/* sWg1 */ = new T(function(){
          var _Dq/* sWg2 */ = E(_D2/* sWfB */);
          if(!_Dq/* sWg2 */._){
            return E(_Cp/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _Db/* sWfH */, _Dq/* sWg2 */.a));
          }
        }),
        _Dr/* sWkN */ = function(_/* EXTERNAL */){
          var _Ds/* sWg5 */ = nMV/* EXTERNAL */(_CA/* Core.View.lvl30 */),
          _Dt/* sWg7 */ = _Ds/* sWg5 */,
          _Du/* sWkL */ = function(_/* EXTERNAL */){
            var _Dv/* sWga */ = nMV/* EXTERNAL */(_Cw/* Core.View.lvl27 */),
            _Dw/* sWgc */ = _Dv/* sWga */,
            _Dx/* sWkJ */ = function(_/* EXTERNAL */){
              var _Dy/* sWgf */ = nMV/* EXTERNAL */(_Cw/* Core.View.lvl27 */),
              _Dz/* sWgh */ = _Dy/* sWgf */,
              _DA/* sWkH */ = function(_/* EXTERNAL */){
                var _DB/* sWgk */ = nMV/* EXTERNAL */(_Cw/* Core.View.lvl27 */),
                _DC/* sWgm */ = _DB/* sWgk */,
                _DD/* sWkF */ = function(_/* EXTERNAL */){
                  var _DE/* sWgp */ = nMV/* EXTERNAL */(_CA/* Core.View.lvl30 */),
                  _DF/* sWgr */ = _DE/* sWgp */,
                  _DG/* sWkD */ = function(_/* EXTERNAL */){
                    var _DH/* sWgu */ = nMV/* EXTERNAL */(_Cw/* Core.View.lvl27 */),
                    _DI/* sWgw */ = _DH/* sWgu */,
                    _DJ/* sWgy */ = new T(function(){
                      var _DK/* sWhl */ = function(_DL/* sWgz */, _DM/* sWgA */, _DN/* sWgB */, _DO/* sWgC */, _DP/* sWgD */, _DQ/* sWgE */){
                        var _DR/* sWgF */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_Dt/* sWg7 */, _DL/* sWgz */));
                        }),
                        _DS/* sWgG */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_Dw/* sWgc */, _DM/* sWgA */));
                        }),
                        _DT/* sWgH */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_Dz/* sWgh */, _DN/* sWgB */));
                        }),
                        _DU/* sWgI */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_DC/* sWgm */, _DO/* sWgC */));
                        }),
                        _DV/* sWgJ */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_DF/* sWgr */, _DP/* sWgD */));
                        }),
                        _DW/* sWgK */ = new T(function(){
                          return B(_jN/* Core.Ease.$wforceTo */(_DI/* sWgw */, _DQ/* sWgE */));
                        }),
                        _DX/* sWhk */ = function(_DY/* sWgL */){
                          var _DZ/* sWgM */ = new T(function(){
                            return B(A1(_DR/* sWgF */,_DY/* sWgL */));
                          }),
                          _E0/* sWhj */ = function(_E1/* sWgN */){
                            var _E2/* sWgO */ = function(_E3/* sWgP */){
                              return new F(function(){return A1(_E1/* sWgN */,new T2(0,_7/* GHC.Tuple.() */,E(_E3/* sWgP */).b));});
                            },
                            _E4/* sWgU */ = function(_E5/* sWgV */){
                              return new F(function(){return A2(_DW/* sWgK */,E(_E5/* sWgV */).b, _E2/* sWgO */);});
                            },
                            _E6/* sWgZ */ = function(_E7/* sWh0 */){
                              return new F(function(){return A2(_DV/* sWgJ */,E(_E7/* sWh0 */).b, _E4/* sWgU */);});
                            },
                            _E8/* sWh4 */ = function(_E9/* sWh5 */){
                              return new F(function(){return A2(_DU/* sWgI */,E(_E9/* sWh5 */).b, _E6/* sWgZ */);});
                            },
                            _Ea/* sWh9 */ = function(_Eb/* sWha */){
                              return new F(function(){return A2(_DT/* sWgH */,E(_Eb/* sWha */).b, _E8/* sWh4 */);});
                            };
                            return new F(function(){return A1(_DZ/* sWgM */,function(_Ec/* sWhe */){
                              return new F(function(){return A2(_DS/* sWgG */,E(_Ec/* sWhe */).b, _Ea/* sWh9 */);});
                            });});
                          };
                          return E(_E0/* sWhj */);
                        };
                        return E(_DX/* sWhk */);
                      };
                      return B(_rx/* Control.Monad.Skeleton.bone */(new T2(2,_DK/* sWhl */,_7/* GHC.Tuple.() */)));
                    }),
                    _Ed/* sWhn */ = new T(function(){
                      var _Ee/* sWho */ = E(_CT/* sWfs */);
                      return new T2(0,E(_Ee/* sWho */.a),E(new T2(2,_Ee/* sWho */.b,new T1(1,function(_Ef/* sWhr */){
                        return E(_DJ/* sWgy */);
                      }))));
                    }),
                    _Eg/* sWhv */ = new T(function(){
                      var _Eh/* sWhM */ = B(_B4/* Core.Shape.Internal.$w$caffine */(new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_Dt/* sWg7 */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_Dw/* sWgc */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_Dz/* sWgh */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_DC/* sWgm */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_DF/* sWgr */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_DI/* sWgw */),_2E/* GHC.Base.id */), E(_CS/* sWfr */).a));
                      return new T3(0,_Eh/* sWhM */.a,_Eh/* sWhM */.b,_Eh/* sWhM */.c);
                    }),
                    _Ei/* sWkB */ = function(_/* EXTERNAL */){
                      var _Ej/* sWhR */ = nMV/* EXTERNAL */(_Cs/* Core.View.lvl24 */),
                      _Ek/* sWhT */ = _Ej/* sWhR */,
                      _El/* sWkx */ = new T(function(){
                        var _Em/* sWiH */ = function(_En/* sWjf */){
                          return new F(function(){return _Eo/* sWiG */(E(_En/* sWjf */).b);});
                        },
                        _Ep/* sWiJ */ = function(_Eq/* sWjn */){
                          var _Er/* sWjo */ = new T(function(){
                            return B(A2(_Dp/* sWg1 */,_Eq/* sWjn */, _Es/* sWiI */));
                          }),
                          _Et/* sWjp */ = new T(function(){
                            return B(A2(_Dd/* sWfJ */,_Eq/* sWjn */, _Em/* sWiH */));
                          }),
                          _Eu/* sWjq */ = new T(function(){
                            return B(A2(_Dn/* sWfY */,_Eq/* sWjn */, _Ev/* sWiF */));
                          }),
                          _Ew/* sWjr */ = new T(function(){
                            return B(_Ep/* sWiJ */(_Eq/* sWjn */));
                          }),
                          _Ex/* sWjI */ = function(_Ey/* sWjs */){
                            var _Ez/* sWjt */ = E(_Ey/* sWjs */);
                            if(!_Ez/* sWjt */._){
                              return (!E(_Ez/* sWjt */.a)) ? E(_Ew/* sWjr */) : E(_Eu/* sWjq */);
                            }else{
                              var _EA/* sWjH */ = function(_/* EXTERNAL */){
                                var _EB/* sWjC */ = B(A2(E(_Eg/* sWhv */).a,_Ez/* sWjt */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_EB/* sWjC */)){
                                    return E(_Et/* sWjp */);
                                  }else{
                                    return E(_Er/* sWjo */);
                                  }
                                });
                              };
                              return new T1(0,_EA/* sWjH */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ek/* sWhT */, _Ex/* sWjI */)));
                        },
                        _Es/* sWiI */ = function(_EC/* sWjj */){
                          return new F(function(){return _Ep/* sWiJ */(E(_EC/* sWjj */).b);});
                        },
                        _Eo/* sWiG */ = function(_ED/* sWiU */){
                          var _EE/* sWiV */ = new T(function(){
                            return B(_Eo/* sWiG */(_ED/* sWiU */));
                          }),
                          _EF/* sWiW */ = new T(function(){
                            return B(A2(_Df/* sWfM */,_ED/* sWiU */, _Es/* sWiI */));
                          }),
                          _EG/* sWjc */ = function(_EH/* sWiX */){
                            var _EI/* sWiY */ = E(_EH/* sWiX */);
                            if(!_EI/* sWiY */._){
                              return E(_EE/* sWiV */);
                            }else{
                              var _EJ/* sWjb */ = function(_/* EXTERNAL */){
                                var _EK/* sWj6 */ = B(A2(E(_Eg/* sWhv */).a,_EI/* sWiY */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_EK/* sWj6 */)){
                                    return E(_EE/* sWiV */);
                                  }else{
                                    return E(_EF/* sWiW */);
                                  }
                                });
                              };
                              return new T1(0,_EJ/* sWjb */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ek/* sWhT */, _EG/* sWjc */)));
                        },
                        _EL/* sWiK */ = function(_EM/* sWjL */){
                          var _EN/* sWjM */ = new T(function(){
                            return B(A2(_Dh/* sWfP */,_EM/* sWjL */, _Ev/* sWiF */));
                          }),
                          _EO/* sWjN */ = new T(function(){
                            return B(A2(_Dd/* sWfJ */,_EM/* sWjL */, _EP/* sWiE */));
                          }),
                          _EQ/* sWjO */ = new T(function(){
                            return B(_EL/* sWiK */(_EM/* sWjL */));
                          }),
                          _ER/* sWjP */ = new T(function(){
                            return B(A2(_Dl/* sWfV */,_EM/* sWjL */, _Es/* sWiI */));
                          }),
                          _ES/* sWk6 */ = function(_ET/* sWjQ */){
                            var _EU/* sWjR */ = E(_ET/* sWjQ */);
                            if(!_EU/* sWjR */._){
                              return (!E(_EU/* sWjR */.a)) ? E(_ER/* sWjP */) : E(_EQ/* sWjO */);
                            }else{
                              var _EV/* sWk5 */ = function(_/* EXTERNAL */){
                                var _EW/* sWk0 */ = B(A2(E(_Eg/* sWhv */).a,_EU/* sWjR */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_EW/* sWk0 */)){
                                    return E(_EO/* sWjN */);
                                  }else{
                                    return E(_EN/* sWjM */);
                                  }
                                });
                              };
                              return new T1(0,_EV/* sWk5 */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ek/* sWhT */, _ES/* sWk6 */)));
                        },
                        _Ev/* sWiF */ = function(_EX/* sWiQ */){
                          return new F(function(){return _EL/* sWiK */(E(_EX/* sWiQ */).b);});
                        },
                        _EY/* sWiL */ = function(_EZ/* sWk9 */){
                          var _F0/* sWka */ = new T(function(){
                            return B(A2(_Df/* sWfM */,_EZ/* sWk9 */, _Ev/* sWiF */));
                          }),
                          _F1/* sWkb */ = new T(function(){
                            return B(A2(_Dh/* sWfP */,_EZ/* sWk9 */, _EP/* sWiE */));
                          }),
                          _F2/* sWkc */ = new T(function(){
                            return B(_EY/* sWiL */(_EZ/* sWk9 */));
                          }),
                          _F3/* sWkd */ = new T(function(){
                            return B(A2(_Dj/* sWfS */,_EZ/* sWk9 */, _Em/* sWiH */));
                          }),
                          _F4/* sWku */ = function(_F5/* sWke */){
                            var _F6/* sWkf */ = E(_F5/* sWke */);
                            if(!_F6/* sWkf */._){
                              return (!E(_F6/* sWkf */.a)) ? E(_F3/* sWkd */) : E(_F2/* sWkc */);
                            }else{
                              var _F7/* sWkt */ = function(_/* EXTERNAL */){
                                var _F8/* sWko */ = B(A2(E(_Eg/* sWhv */).a,_F6/* sWkf */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_F8/* sWko */)){
                                    return E(_F1/* sWkb */);
                                  }else{
                                    return E(_F0/* sWka */);
                                  }
                                });
                              };
                              return new T1(0,_F7/* sWkt */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Ek/* sWhT */, _F4/* sWku */)));
                        },
                        _EP/* sWiE */ = function(_F9/* sWiM */){
                          return new F(function(){return _EY/* sWiL */(E(_F9/* sWiM */).b);});
                        };
                        return B(_Eo/* sWiG */(_Dc/* sWfI */));
                      }),
                      _Fa/* sWiD */ = new T(function(){
                        var _Fb/* sWiC */ = function(_Fc/* sWis */){
                          var _Fd/* sWit */ = E(_Fc/* sWis */);
                          return new F(function(){return A1(_D7/* sWfE */,new T2(0,new T(function(){
                            return new T3(0,E(_Fd/* sWit */.a),_Ed/* sWhn */,E(_Db/* sWfH */));
                          }),_Fd/* sWit */.b));});
                        },
                        _Fe/* sWir */ = function(_Ff/* sWhV */, _Fg/* sWhW */, _Fh/* sWhX */){
                          var _Fi/* sWhY */ = new T(function(){
                            return E(E(_Ff/* sWhV */).d);
                          }),
                          _Fj/* sWi4 */ = new T(function(){
                            return E(E(_Fi/* sWhY */).a);
                          }),
                          _Fk/* sWio */ = new T(function(){
                            var _Fl/* sWi8 */ = E(_Ff/* sWhV */);
                            return new T4(0,E(_Fl/* sWi8 */.a),_Fl/* sWi8 */.b,E(_Fl/* sWi8 */.c),E(new T2(0,new T(function(){
                              return E(_Fj/* sWi4 */)+1|0;
                            }),new T(function(){
                              return B(_BR/* Data.IntMap.Strict.$winsert */(E(_Fj/* sWi4 */), _Ek/* sWhT */, E(_Fi/* sWhY */).b));
                            }))));
                          });
                          return new F(function(){return A1(_Fh/* sWhX */,new T2(0,new T2(0,_Fj/* sWi4 */,_Fk/* sWio */),_Fg/* sWhW */));});
                        };
                        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _Dc/* sWfI */, _Fe/* sWir */, _Dc/* sWfI */, _Fb/* sWiC */]));
                      });
                      return new T1(1,new T2(1,_Fa/* sWiD */,new T2(1,_El/* sWkx */,_6/* GHC.Types.[] */)));
                    };
                    return new T1(0,_Ei/* sWkB */);
                  };
                  return new T1(0,_DG/* sWkD */);
                };
                return new T1(0,_DD/* sWkF */);
              };
              return new T1(0,_DA/* sWkH */);
            };
            return new T1(0,_Dx/* sWkJ */);
          };
          return new T1(0,_Du/* sWkL */);
        };
        return new T1(0,_Dr/* sWkN */);
      };
      return new F(function(){return A1(_D5/* sWfD */,_D8/* sWkO */);});
    };
    return E(_D6/* sWkP */);
  };
  return E(_D3/* sWkQ */);
},
_Fm/* consView */ = function(_Fn/* s7LD */, _Fo/* s7LE */, _Fp/* s7LF */, _Fq/* s7LG */){
  var _Fr/* s7LH */ = new T(function(){
    var _Fs/* s7M2 */ = new T(function(){
      var _Ft/* s7LO */ = B(_rB/* Core.Render.Internal.fill1 */(_Am/* Motion.Main.lvl12 */, new T(function(){
        var _Fu/* s7LJ */ = B(_y9/* Core.Shape.Internal.$wtext */(_An/* Motion.Main.lvl13 */, new T1(0,_Fp/* s7LF */), _yQ/* Core.Shape.Internal.LeftAlign */, _yN/* Core.Shape.Internal.BottomBase */, _At/* Motion.Main.lvl16 */, _Aw/* Motion.Main.lvl19 */, _AA/* Motion.Main.lvl22 */));
        return new T3(0,_Fu/* s7LJ */.a,_Fu/* s7LJ */.b,_Fu/* s7LJ */.c);
      }))),
      _Fv/* s7LR */ = new T(function(){
        return B(_rB/* Core.Render.Internal.fill1 */(_AD/* Motion.Main.lvl24 */, new T(function(){
          var _Fw/* s7LT */ = B(_y9/* Core.Shape.Internal.$wtext */(_An/* Motion.Main.lvl13 */, new T1(0,_Fq/* s7LG */), _yQ/* Core.Shape.Internal.LeftAlign */, _yR/* Core.Shape.Internal.TopBase */, _At/* Motion.Main.lvl16 */, _AG/* Motion.Main.lvl27 */, _AK/* Motion.Main.lvl30 */));
          return new T3(0,_Fw/* s7LT */.a,_Fw/* s7LT */.b,_Fw/* s7LT */.c);
        })));
      });
      return new T2(0,E(_Ft/* s7LO */.a),E(new T2(2,_Ft/* s7LO */.b,new T1(1,function(_Fx/* s7LY */){
        return E(_Fv/* s7LR */);
      }))));
    });
    return B(_xr/* Core.Render.Internal.$wshadowed */(_yT/* Motion.Main.lvl4 */, _AT/* Motion.Main.lvl5 */, _AY/* Motion.Main.lvl8 */, _Aj/* Motion.Main.lvl10 */, _Fs/* s7M2 */));
  }),
  _Fy/* s7M3 */ = function(_Fz/* s7M4 */){
    return E(_Fr/* s7LH */);
  },
  _FA/* s7M6 */ = new T(function(){
    return B(A1(_Fo/* s7LE */,_Fn/* s7LD */));
  }),
  _FB/* s7MT */ = function(_FC/* s7M7 */){
    var _FD/* s7M8 */ = new T(function(){
      return B(A1(_FA/* s7M6 */,_FC/* s7M7 */));
    }),
    _FE/* s7MS */ = function(_FF/* s7M9 */){
      var _FG/* s7MR */ = function(_FH/* s7Ma */){
        var _FI/* s7Mb */ = E(_FH/* s7Ma */),
        _FJ/* s7Me */ = E(_FI/* s7Mb */.a),
        _FK/* s7Mh */ = new T(function(){
          var _FL/* s7Mk */ = B(_zY/* Core.Render.Internal.clip */(_yW/* Motion.Main.shape */, new T(function(){
            return B(_rx/* Control.Monad.Skeleton.bone */(new T3(7,_AW/* Motion.Main.lvl7 */,_FJ/* s7Me */.a,_7/* GHC.Tuple.() */)));
          })));
          return new T2(0,E(_FL/* s7Mk */.a),E(new T2(2,_FL/* s7Mk */.b,new T1(1,_Fy/* s7M3 */))));
        }),
        _FM/* s7MQ */ = function(_/* EXTERNAL */){
          var _FN/* s7Mp */ = nMV/* EXTERNAL */(_AR/* Motion.Main.lvl35 */);
          return new T(function(){
            var _FO/* s7Mt */ = new T(function(){
              return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _AH/* Motion.Main.lvl3 */, _Ag/* Core.Ease.linear */, _FN/* s7Mp */, _Ax/* Motion.Main.lvl2 */, _Ac/* Core.Ease.easeTo1 */));
            }),
            _FP/* s7Mu */ = new T(function(){
              return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _AH/* Motion.Main.lvl3 */, _Ag/* Core.Ease.linear */, _FN/* s7Mp */, _AL/* Motion.Main.lvl31 */, _Ac/* Core.Ease.easeTo1 */));
            }),
            _FQ/* s7MO */ = function(_FR/* s7MF */){
              var _FS/* s7MG */ = new T(function(){
                return B(_zj/* Core.UI.button */(_FO/* s7Mt */, _FP/* s7Mu */, _z1/* Motion.Main.a23 */, _FR/* s7MF */));
              }),
              _FT/* s7MN */ = function(_FU/* s7MH */, _FV/* s7MI */){
                return new T1(1,new T2(1,new T(function(){
                  return B(A2(_FS/* s7MG */,_FU/* s7MH */, _FV/* s7MI */));
                }),new T2(1,new T(function(){
                  return B(A2(_FJ/* s7Me */.b,_FU/* s7MH */, _AM/* Motion.Main.lvl32 */));
                }),_6/* GHC.Types.[] */)));
              };
              return E(_FT/* s7MN */);
            },
            _FW/* s7ME */ = new T(function(){
              var _FX/* s7Mx */ = B(_xr/* Core.Render.Internal.$wshadowed */(_yT/* Motion.Main.lvl4 */, _AT/* Motion.Main.lvl5 */, new T2(2,new T3(0,_AH/* Motion.Main.lvl3 */,_Ag/* Core.Ease.linear */,_FN/* s7Mp */),_2E/* GHC.Base.id */), _z5/* Core.Render.Internal.black */, _z0/* Motion.Main.a17 */));
              return new T2(0,E(_FX/* s7Mx */.a),E(new T2(2,_FX/* s7Mx */.b,new T1(1,function(_FY/* s7MA */){
                return E(_FK/* s7Mh */);
              }))));
            });
            return B(A(_CQ/* Core.View.makeView */,[_yO/* GHC.Base.Just */, _yW/* Motion.Main.shape */, _FW/* s7ME */, _FQ/* s7MO */, _FI/* s7Mb */.b, _FF/* s7M9 */]));
          });
        };
        return new T1(0,_FM/* s7MQ */);
      };
      return new F(function(){return A1(_FD/* s7M8 */,_FG/* s7MR */);});
    };
    return E(_FE/* s7MS */);
  };
  return E(_FB/* s7MT */);
},
_FZ/* lvl36 */ = 0.9,
_G0/* lvl37 */ = new T1(0,_FZ/* Motion.Main.lvl36 */),
_G1/* lvl38 */ = new T4(0,_yT/* Motion.Main.lvl4 */,_Az/* Motion.Main.lvl21 */,_G0/* Motion.Main.lvl37 */,_Al/* Motion.Main.lvl11 */),
_G2/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bounce"));
}),
_G3/* lvl40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Velocity & Acceleration"));
}),
_G4/* lvl41 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_G1/* Motion.Main.lvl38 */, _wY/* Motion.Bounce.bounceMot1 */, _G2/* Motion.Main.lvl39 */, _G3/* Motion.Main.lvl40 */));
}),
_G5/* negateDouble */ = function(_G6/* s18yz */){
  return  -E(_G6/* s18yz */);
},
_G7/* $fAffineRender1 */ = function(_G8/* sFdS */, _G9/* sFdT */, _Ga/* sFdU */, _Gb/* sFdV */){
  var _Gc/* sFeZ */ = new T(function(){
    var _Gd/* sFeX */ = new T(function(){
      var _Ge/* sFeU */ = new T(function(){
        var _Gf/* sFer */ = E(_Ga/* sFdU */);
        switch(_Gf/* sFer */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_Gf/* sFer */.a);
            }));
            break;
          case 1:
            var _Gg/* sFeD */ = function(_/* EXTERNAL */){
              var _Gh/* sFez */ = B(A1(_Gf/* sFer */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_G5/* GHC.Float.negateDouble */(_Gh/* sFez */));
              });
            };
            return new T1(1,_Gg/* sFeD */);
            break;
          case 2:
            return new T2(2,_Gf/* sFer */.a,function(_Gi/* sFeG */){
              return  -B(A1(_Gf/* sFer */.b,_Gi/* sFeG */));
            });
            break;
          default:
            var _Gj/* sFeT */ = function(_Gk/* sFeN */, _/* EXTERNAL */){
              var _Gl/* sFeP */ = B(A2(_Gf/* sFer */.b,_Gk/* sFeN */, _/* EXTERNAL */));
              return new T(function(){
                return B(_G5/* GHC.Float.negateDouble */(_Gl/* sFeP */));
              });
            };
            return new T2(3,_Gf/* sFer */.a,_Gj/* sFeT */);
        }
      }),
      _Gm/* sFeq */ = new T(function(){
        var _Gn/* sFdX */ = E(_G9/* sFdT */);
        switch(_Gn/* sFdX */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_Gn/* sFdX */.a);
            }));
            break;
          case 1:
            var _Go/* sFe9 */ = function(_/* EXTERNAL */){
              var _Gp/* sFe5 */ = B(A1(_Gn/* sFdX */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_G5/* GHC.Float.negateDouble */(_Gp/* sFe5 */));
              });
            };
            return new T1(1,_Go/* sFe9 */);
            break;
          case 2:
            return new T2(2,_Gn/* sFdX */.a,function(_Gq/* sFec */){
              return  -B(A1(_Gn/* sFdX */.b,_Gq/* sFec */));
            });
            break;
          default:
            var _Gr/* sFep */ = function(_Gs/* sFej */, _/* EXTERNAL */){
              var _Gt/* sFel */ = B(A2(_Gn/* sFdX */.b,_Gs/* sFej */, _/* EXTERNAL */));
              return new T(function(){
                return B(_G5/* GHC.Float.negateDouble */(_Gt/* sFel */));
              });
            };
            return new T2(3,_Gn/* sFdX */.a,_Gr/* sFep */);
        }
      });
      return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_Gm/* sFeq */,_Ge/* sFeU */),_Gb/* sFdV */,_7/* GHC.Tuple.() */)));
    });
    return B(_rx/* Control.Monad.Skeleton.bone */(new T3(7,_G8/* sFdS */,_Gd/* sFeX */,_7/* GHC.Tuple.() */)));
  });
  return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_G9/* sFdT */,_Ga/* sFdU */),_Gc/* sFeZ */,_7/* GHC.Tuple.() */));});
},
_Gu/* lvl */ = 0,
_Gv/* lvl1 */ = 40,
_Gw/* lvl2 */ = 0.9999999999999998,
_Gx/* lvl3 */ = new T4(0,_Gu/* Motion.Grow.lvl */,_Gu/* Motion.Grow.lvl */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_Gy/* lvl4 */ = new T2(0,_Gu/* Motion.Grow.lvl */,_Gx/* Motion.Grow.lvl3 */),
_Gz/* lvl5 */ = new T2(0,_Gy/* Motion.Grow.lvl4 */,_6/* GHC.Types.[] */),
_GA/* $wa1 */ = function(_GB/* s64X */, _GC/* s64Y */, _GD/* s64Z */){
  return function(_/* EXTERNAL */){
    var _GE/* s651 */ = nMV/* EXTERNAL */(_Gz/* Motion.Grow.lvl5 */);
    return new T(function(){
      var _GF/* s654 */ = function(_GG/* s655 */, _GH/* s656 */){
        return 1-B(A1(_GG/* s655 */,new T(function(){
          var _GI/* s659 */ = E(_GH/* s656 */)/0.3-_GB/* s64X *//7*2.3333333333333335;
          if(1>_GI/* s659 */){
            if(0>_GI/* s659 */){
              return E(_Gw/* Motion.Grow.lvl2 */);
            }else{
              var _GJ/* s65i */ = 1-_GI/* s659 */;
              return _GJ/* s65i */*_GJ/* s65i */*(2.70158*_GJ/* s65i */-1.70158);
            }
          }else{
            return E(_Gu/* Motion.Grow.lvl */);
          }
        })));
      },
      _GK/* s65v */ = new T3(0,_Gv/* Motion.Grow.lvl1 */,function(_GL/* s65r */, _GM/* s65s */){
        return new F(function(){return _GF/* s654 */(_GL/* s65r */, _GM/* s65s */);});
      },_GE/* s651 */),
      _GN/* s65w */ = E(_GB/* s64X */);
      if(_GN/* s65w */==7){
        return B(A1(_GD/* s64Z */,new T2(0,new T2(1,_GK/* s65v */,_6/* GHC.Types.[] */),_GC/* s64Y */)));
      }else{
        return new T1(0,B(_GA/* Motion.Grow.$wa1 */(_GN/* s65w */+1|0, _GC/* s64Y */, function(_GO/* s65y */){
          var _GP/* s65z */ = E(_GO/* s65y */);
          return new F(function(){return A1(_GD/* s64Z */,new T2(0,new T2(1,_GK/* s65v */,_GP/* s65z */.a),_GP/* s65z */.b));});
        })));
      }
    });
  };
},
_GQ/* $wcenterRect */ = function(_GR/* stCR */, _GS/* stCS */, _GT/* stCT */, _GU/* stCU */){
  var _GV/* stF0 */ = function(_GW/* stDN */, _GX/* stDO */, _GY/* stDP */, _/* EXTERNAL */){
    var _GZ/* stEZ */ = function(_H0/* stDR */, _H1/* stDS */, _H2/* stDT */, _/* EXTERNAL */){
      var _H3/* stEY */ = function(_H4/* stDV */){
        var _H5/* stDW */ = new T(function(){
          return E(_H4/* stDV */)/2;
        }),
        _H6/* stEX */ = function(_H7/* stE0 */, _H8/* stE1 */, _H9/* stE2 */, _/* EXTERNAL */){
          var _Ha/* stE4 */ = E(_GW/* stDN */),
          _Hb/* stE6 */ = E(_H5/* stDW */),
          _Hc/* stE8 */ = _Ha/* stE4 */+_Hb/* stE6 */,
          _Hd/* stEe */ = _Ha/* stE4 */-_Hb/* stE6 */,
          _He/* stEh */ = E(_H0/* stDR */),
          _Hf/* stEl */ = E(_H7/* stE0 */)/2,
          _Hg/* stEp */ = _He/* stEh */+_Hf/* stEl */,
          _Hh/* stEs */ = _He/* stEh */-_Hf/* stEl */,
          _Hi/* stEv */ = E(_H8/* stE1 */),
          _Hj/* stEz */ = E(_H9/* stE2 */),
          _Hk/* stEC */ = __app4/* EXTERNAL */(E(_kz/* Core.Shape.Internal.bezier_f2 */), _Hd/* stEe */, _Hh/* stEs */, _Hi/* stEv */, _Hj/* stEz */),
          _Hl/* stEF */ = E(_kA/* Core.Shape.Internal.line_f1 */),
          _Hm/* stEI */ = __app4/* EXTERNAL */(_Hl/* stEF */, _Hc/* stE8 */, _He/* stEh */-_Hf/* stEl */, _Hi/* stEv */, _Hj/* stEz */),
          _Hn/* stEM */ = __app4/* EXTERNAL */(_Hl/* stEF */, _Hc/* stE8 */, _Hg/* stEp */, _Hi/* stEv */, _Hj/* stEz */),
          _Ho/* stEQ */ = __app4/* EXTERNAL */(_Hl/* stEF */, _Ha/* stE4 */-_Hb/* stE6 */, _Hg/* stEp */, _Hi/* stEv */, _Hj/* stEz */),
          _Hp/* stEU */ = __app4/* EXTERNAL */(_Hl/* stEF */, _Hd/* stEe */, _Hh/* stEs */, _Hi/* stEv */, _Hj/* stEz */);
          return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        };
        return function(_gd/* _fa_1 */, _ge/* _fa_2 */, _Hq/* _fa_3 */){
          return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_GU/* stCU */, _H6/* stEX */, _gd/* _fa_1 */, _ge/* _fa_2 */, _Hq/* _fa_3 */);});
        };
      };
      return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_GT/* stCT */, _H3/* stEY */, _H1/* stDS */, _H2/* stDT */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_GS/* stCS */, _GZ/* stEZ */, _GX/* stDO */, _GY/* stDP */, _/* EXTERNAL */);});
  },
  _Hr/* stDM */ = function(_Hs/* stCV */, _/* EXTERNAL */){
    var _Ht/* stCX */ = E(_Hs/* stCV */),
    _Hu/* stDL */ = function(_Hv/* stD0 */, _/* EXTERNAL */){
      var _Hw/* stDK */ = function(_Hx/* stD2 */, _/* EXTERNAL */){
        var _Hy/* stDJ */ = function(_Hz/* stD4 */, _/* EXTERNAL */){
          var _HA/* stDI */ = function(_HB/* stD6 */, _/* EXTERNAL */){
            return new T(function(){
              var _HC/* stDc */ = function(_HD/* stDd */){
                if(_HD/* stDd */>=E(_Hz/* stD4 */)/2){
                  return false;
                }else{
                  var _HE/* stDn */ = E(_Ht/* stCX */.b)-E(_Hx/* stD2 */);
                  return (_HE/* stDn */==0) ? 0<E(_HB/* stD6 */)/2 : (_HE/* stDn */<=0) ?  -_HE/* stDn */<E(_HB/* stD6 */)/2 : _HE/* stDn */<E(_HB/* stD6 */)/2;
                }
              },
              _HF/* stDD */ = E(_Ht/* stCX */.a)-E(_Hv/* stD0 */);
              if(!_HF/* stDD */){
                return B(_HC/* stDc */(0));
              }else{
                if(_HF/* stDD */<=0){
                  return B(_HC/* stDc */( -_HF/* stDD */));
                }else{
                  return B(_HC/* stDc */(_HF/* stDD */));
                }
              }
            });
          };
          return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_GU/* stCU */, _HA/* stDI */, _/* EXTERNAL */);});
        };
        return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_GT/* stCT */, _Hy/* stDJ */, _/* EXTERNAL */);});
      };
      return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_GS/* stCS */, _Hw/* stDK */, _/* EXTERNAL */);});
    };
    return new F(function(){return _kn/* Core.Shape.Internal.$fAffineShape3 */(_GR/* stCR */, _Hu/* stDL */, _/* EXTERNAL */);});
  };
  return new T3(0,_Hr/* stDM */,function(_lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _ka/* Core.Shape.Internal.$fAffineShape2 */(_GR/* stCR */, _GV/* stF0 */, _lo/* B3 */, _lp/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_HG/* a2 */ = 20,
_HH/* a3 */ = new T1(0,_/* EXTERNAL */),
_HI/* a4 */ = new T1(0,_6/* GHC.Types.[] */),
_HJ/* a5 */ = new T2(0,E(_HI/* Motion.Grow.a4 */),E(_HH/* Motion.Grow.a3 */)),
_HK/* ds */ = 1,
_HL/* a */ = function(_HM/* s64U */, _HN/* s64V */){
  return new F(function(){return A1(_HN/* s64V */,new T2(0,_7/* GHC.Tuple.() */,_HM/* s64U */));});
},
_HO/* go */ = function(_HP/* s65L */){
  var _HQ/* s65M */ = E(_HP/* s65L */);
  if(!_HQ/* s65M */._){
    return E(_HL/* Motion.Grow.a */);
  }else{
    var _HR/* s65P */ = new T(function(){
      var _HS/* s65Q */ = E(_HQ/* s65M */.a);
      return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _HS/* s65Q */.a, _HS/* s65Q */.b, _HS/* s65Q */.c, _HK/* Motion.Grow.ds */, _Ac/* Core.Ease.easeTo1 */));
    }),
    _HT/* s65U */ = new T(function(){
      return B(_HO/* Motion.Grow.go */(_HQ/* s65M */.b));
    }),
    _HU/* s664 */ = function(_HV/* s65V */){
      var _HW/* s65W */ = new T(function(){
        return B(A1(_HR/* s65P */,_HV/* s65V */));
      }),
      _HX/* s663 */ = function(_HY/* s65X */){
        return new F(function(){return A1(_HW/* s65W */,function(_HZ/* s65Y */){
          return new F(function(){return A2(_HT/* s65U */,E(_HZ/* s65Y */).b, _HY/* s65X */);});
        });});
      };
      return E(_HX/* s663 */);
    };
    return E(_HU/* s664 */);
  }
},
_I0/* go1 */ = function(_I1/* s665 */){
  var _I2/* s666 */ = E(_I1/* s665 */);
  if(!_I2/* s666 */._){
    return E(_HL/* Motion.Grow.a */);
  }else{
    var _I3/* s669 */ = new T(function(){
      var _I4/* s66a */ = E(_I2/* s666 */.a),
      _I5/* s66p */ = function(_I6/* s66e */){
        var _I7/* s66f */ = new T(function(){
          return B(A1(_I4/* s66a */.b,_I6/* s66e */));
        }),
        _I8/* s66o */ = function(_I9/* s66g */){
          return 1-B(A1(_I7/* s66f */,new T(function(){
            return 1-E(_I9/* s66g */);
          })));
        };
        return E(_I8/* s66o */);
      };
      return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _I4/* s66a */.a, _I5/* s66p */, _I4/* s66a */.c, _Gu/* Motion.Grow.lvl */, _Ac/* Core.Ease.easeTo1 */));
    }),
    _Ia/* s66q */ = new T(function(){
      return B(_I0/* Motion.Grow.go1 */(_I2/* s666 */.b));
    }),
    _Ib/* s66A */ = function(_Ic/* s66r */){
      var _Id/* s66s */ = new T(function(){
        return B(A1(_I3/* s669 */,_Ic/* s66r */));
      }),
      _Ie/* s66z */ = function(_If/* s66t */){
        return new F(function(){return A1(_Id/* s66s */,function(_Ig/* s66u */){
          return new F(function(){return A2(_Ia/* s66q */,E(_Ig/* s66u */).b, _If/* s66t */);});
        });});
      };
      return E(_Ie/* s66z */);
    };
    return E(_Ib/* s66A */);
  }
},
_Ih/* eftInt */ = function(_Ii/* smpW */, _Ij/* smpX */){
  if(_Ii/* smpW */<=_Ij/* smpX */){
    var _Ik/* smq0 */ = function(_Il/* smq1 */){
      return new T2(1,_Il/* smq1 */,new T(function(){
        if(_Il/* smq1 */!=_Ij/* smpX */){
          return B(_Ik/* smq0 */(_Il/* smq1 */+1|0));
        }else{
          return __Z/* EXTERNAL */;
        }
      }));
    };
    return new F(function(){return _Ik/* smq0 */(_Ii/* smpW */);});
  }else{
    return __Z/* EXTERNAL */;
  }
},
_Im/* iforM1 */ = new T(function(){
  return B(_Ih/* GHC.Enum.eftInt */(0, 2147483647));
}),
_In/* lvl10 */ = 3,
_Io/* lvl6 */ = new T1(0,_Gv/* Motion.Grow.lvl1 */),
_Ip/* lvl7 */ = new T1(0,_HG/* Motion.Grow.a2 */),
_Iq/* lvl8 */ = -20,
_Ir/* lvl9 */ = 60,
_Is/* morph */ = function(_It/* sb2v */){
  return new T2(2,_It/* sb2v */,_2E/* GHC.Base.id */);
},
_Iu/* $wa */ = function(_Iv/* s66B */, _Iw/* s66C */, _Ix/* s66D */){
  var _Iy/* s66E */ = function(_Iz/* s66F */, _IA/* s66G */){
    var _IB/* s66H */ = E(_Iz/* s66F */);
    if(!_IB/* s66H */._){
      return E(_HJ/* Motion.Grow.a5 */);
    }else{
      var _IC/* s66I */ = _IB/* s66H */.a,
      _ID/* s66K */ = E(_IA/* s66G */);
      if(!_ID/* s66K */._){
        return E(_HJ/* Motion.Grow.a5 */);
      }else{
        var _IE/* s66L */ = _ID/* s66K */.a,
        _IF/* s66N */ = new T(function(){
          var _IG/* s66O */ = E(_IC/* s66I */);
          if(_IG/* s66O */>=4){
            if(_IG/* s66O */<=4){
              return E(_HK/* Motion.Grow.ds */);
            }else{
              return _IG/* s66O */-4|0;
            }
          }else{
            return 4-_IG/* s66O */|0;
          }
        }),
        _IH/* s66Y */ = new T(function(){
          var _II/* s671 */ = E(_IC/* s66I */)-2|0;
          if(1>_II/* s671 */){
            return E(_HK/* Motion.Grow.ds */);
          }else{
            if(3>_II/* s671 */){
              return _II/* s671 */;
            }else{
              return E(_In/* Motion.Grow.lvl10 */);
            }
          }
        }),
        _IJ/* s67G */ = new T(function(){
          var _IK/* s67F */ = new T(function(){
            var _IL/* s67B */ = B(_GQ/* Core.Shape.Internal.$wcenterRect */(new T(function(){
              return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_IH/* s66Y */), _Io/* Motion.Grow.lvl6 */)), _Ip/* Motion.Grow.lvl7 */));
            }), new T(function(){
              return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_IF/* s66N */), _Io/* Motion.Grow.lvl6 */)), _Ip/* Motion.Grow.lvl7 */));
            }), _Io/* Motion.Grow.lvl6 */, _Io/* Motion.Grow.lvl6 */));
            return new T3(0,_IL/* s67B */.a,_IL/* s67B */.b,_IL/* s67B */.c);
          });
          return B(_rB/* Core.Render.Internal.fill1 */(_Iv/* s66B */, _IK/* s67F */));
        }),
        _IM/* s67u */ = new T(function(){
          return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_IF/* s66N */), _Io/* Motion.Grow.lvl6 */)), _Ip/* Motion.Grow.lvl7 */)), new T1(0,new T(function(){
            var _IN/* s67m */ = E(_IC/* s66I */);
            if(_IN/* s67m */>=4){
              if(_IN/* s67m */<=4){
                return E(_Gu/* Motion.Grow.lvl */);
              }else{
                return E(_Iq/* Motion.Grow.lvl8 */);
              }
            }else{
              return E(_HG/* Motion.Grow.a2 */);
            }
          }))));
        }),
        _IO/* s67i */ = new T(function(){
          return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_IH/* s66Y */), _Io/* Motion.Grow.lvl6 */)), _Ip/* Motion.Grow.lvl7 */)), new T1(0,new T(function(){
            switch(E(_IC/* s66I */)){
              case 4:
                return E(_Iq/* Motion.Grow.lvl8 */);
                break;
              case 5:
                return E(_Iq/* Motion.Grow.lvl8 */);
                break;
              default:
                return E(_Gu/* Motion.Grow.lvl */);
            }
          }))));
        }),
        _IP/* s67H */ = B(_G7/* Core.Render.Internal.$fAffineRender1 */(new T2(0,new T(function(){
          return B(_Is/* Core.Ease.morph */(_IE/* s66L */));
        }),new T(function(){
          return B(_Is/* Core.Ease.morph */(_IE/* s66L */));
        })), _IO/* s67i */, _IM/* s67u */, _IJ/* s67G */)),
        _IQ/* s67K */ = new T(function(){
          return B(_Iy/* s66E */(_IB/* s66H */.b, _ID/* s66K */.b));
        }),
        _IR/* s67V */ = function(_IS/* s67L */){
          var _IT/* s67M */ = E(_IQ/* s67K */);
          return new T2(0,E(_IT/* s67M */.a),E(new T2(2,_IT/* s67M */.b,new T1(1,function(_IU/* s67P */){
            return new T2(0,E(new T1(0,new T2(1,_IS/* s67L */,_IU/* s67P */))),E(_HH/* Motion.Grow.a3 */));
          }))));
        };
        return new T2(0,E(_IP/* s67H */.a),E(new T2(2,_IP/* s67H */.b,new T1(1,_IR/* s67V */))));
      }
    }
  },
  _IV/* s68x */ = function(_IW/* s67Y */){
    var _IX/* s67Z */ = E(_IW/* s67Y */),
    _IY/* s680 */ = _IX/* s67Z */.a,
    _IZ/* s682 */ = new T(function(){
      return B(_I0/* Motion.Grow.go1 */(_IY/* s680 */));
    }),
    _J0/* s683 */ = new T(function(){
      return B(_HO/* Motion.Grow.go */(_IY/* s680 */));
    }),
    _J1/* s684 */ = function(_J2/* s685 */){
      var _J3/* s686 */ = new T(function(){
        return B(A1(_J0/* s683 */,_J2/* s685 */));
      }),
      _J4/* s68s */ = function(_J5/* s687 */){
        var _J6/* s688 */ = function(_J7/* s689 */){
          return new F(function(){return A2(_J1/* s684 */,E(_J7/* s689 */).b, _J5/* s687 */);});
        },
        _J8/* s68d */ = function(_J9/* s68e */){
          return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_Ir/* Motion.Grow.lvl9 */, E(_J9/* s68e */).b, _J6/* s688 */);});
        },
        _Ja/* s68i */ = function(_Jb/* s68j */){
          return new F(function(){return A2(_IZ/* s682 */,E(_Jb/* s68j */).b, _J8/* s68d */);});
        };
        return new F(function(){return A1(_J3/* s686 */,function(_Jc/* s68n */){
          return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_Ir/* Motion.Grow.lvl9 */, E(_Jc/* s68n */).b, _Ja/* s68i */);});
        });});
      };
      return E(_J4/* s68s */);
    },
    _Jd/* s68u */ = new T(function(){
      return B(_rp/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
        return B(_Iy/* s66E */(_Im/* Core.Util.iforM1 */, _IY/* s680 */));
      })));
    });
    return new F(function(){return A1(_Ix/* s66D */,new T2(0,new T2(0,_Jd/* s68u */,_J1/* s684 */),_IX/* s67Z */.b));});
  };
  return new F(function(){return _GA/* Motion.Grow.$wa1 */(0, _Iw/* s66C */, _IV/* s68x */);});
},
_Je/* growMot1 */ = function(_Jf/* s68y */, _Jg/* s68z */, _Jh/* s68A */){
  return new T1(0,B(_Iu/* Motion.Grow.$wa */(_Jf/* s68y */, _Jg/* s68z */, _Jh/* s68A */)));
},
_Ji/* lvl42 */ = 0.4,
_Jj/* lvl43 */ = new T1(0,_Ji/* Motion.Main.lvl42 */),
_Jk/* lvl44 */ = 0.8,
_Jl/* lvl45 */ = new T1(0,_Jk/* Motion.Main.lvl44 */),
_Jm/* lvl46 */ = new T4(0,_Jj/* Motion.Main.lvl43 */,_Jl/* Motion.Main.lvl45 */,_yT/* Motion.Main.lvl4 */,_Al/* Motion.Main.lvl11 */),
_Jn/* lvl47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Grow"));
}),
_Jo/* lvl48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sequential easeOutBack"));
}),
_Jp/* lvl49 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_Jm/* Motion.Main.lvl46 */, _Je/* Motion.Grow.growMot1 */, _Jn/* Motion.Main.lvl47 */, _Jo/* Motion.Main.lvl48 */));
}),
_Jq/* lvl50 */ = new T4(0,_Al/* Motion.Main.lvl11 */,_Ai/* Motion.Main.lvl9 */,_yT/* Motion.Main.lvl4 */,_Al/* Motion.Main.lvl11 */),
_Jr/* lvl51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Speed"));
}),
_Js/* lvl52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uniform Distr & Exponential Distr"));
}),
_Jt/* speedMot1 */ = function(_Ju/* sRjo */, _Jv/* sRjp */){
  return new F(function(){return A1(_Jv/* sRjp */,new T2(0,_7/* GHC.Tuple.() */,_Ju/* sRjo */));});
},
_Jw/* speedMot14 */ = 0,
_Jx/* speedMot13 */ = new T1(0,_Jw/* Motion.Speed.speedMot14 */),
_Jy/* speedMot12 */ = new T2(0,_Jx/* Motion.Speed.speedMot13 */,_Jx/* Motion.Speed.speedMot13 */),
_Jz/* intToInt64# */ = function(_JA/* sf6 */){
  var _JB/* sf8 */ = hs_intToInt64/* EXTERNAL */(_JA/* sf6 */);
  return E(_JB/* sf8 */);
},
_JC/* integerToInt64 */ = function(_JD/* s1S1 */){
  var _JE/* s1S2 */ = E(_JD/* s1S1 */);
  if(!_JE/* s1S2 */._){
    return new F(function(){return _Jz/* GHC.IntWord64.intToInt64# */(_JE/* s1S2 */.a);});
  }else{
    return new F(function(){return I_toInt64/* EXTERNAL */(_JE/* s1S2 */.a);});
  }
},
_JF/* $cfromInteger3 */ = function(_JG/* s2dWF */){
  return new F(function(){return _JC/* GHC.Integer.Type.integerToInt64 */(_JG/* s2dWF */);});
},
_JH/* $fNumInt64_$c* */ = function(_JI/* s2dXh */, _JJ/* s2dXi */){
  return new F(function(){return hs_timesInt64/* EXTERNAL */(E(_JI/* s2dXh */), E(_JJ/* s2dXi */));});
},
_JK/* $fNumInt64_$c+ */ = function(_JL/* s2dXB */, _JM/* s2dXC */){
  return new F(function(){return hs_plusInt64/* EXTERNAL */(E(_JL/* s2dXB */), E(_JM/* s2dXC */));});
},
_JN/* $fNumInt64_$c- */ = function(_JO/* s2dXr */, _JP/* s2dXs */){
  return new F(function(){return hs_minusInt64/* EXTERNAL */(E(_JO/* s2dXr */), E(_JP/* s2dXs */));});
},
_JQ/* $w$cabs */ = function(_JR/* s2dWW */){
  var _JS/* s2dWY */ = hs_geInt64/* EXTERNAL */(_JR/* s2dWW */, new Long/* EXTERNAL */(0, 0));
  if(!_JS/* s2dWY */){
    var _JT/* s2dX3 */ = hs_negateInt64/* EXTERNAL */(_JR/* s2dWW */);
    return E(_JT/* s2dX3 */);
  }else{
    return E(_JR/* s2dWW */);
  }
},
_JU/* $fNumInt64_$cabs */ = function(_JV/* s2dX6 */){
  return new F(function(){return _JQ/* GHC.Int.$w$cabs */(E(_JV/* s2dX6 */));});
},
_JW/* $fNumInt64_$cnegate */ = function(_JX/* s2dXa */){
  return new F(function(){return hs_negateInt64/* EXTERNAL */(E(_JX/* s2dXa */));});
},
_JY/* $w$csignum */ = function(_JZ/* s2dWH */){
  var _K0/* s2dWJ */ = hs_gtInt64/* EXTERNAL */(_JZ/* s2dWH */, new Long/* EXTERNAL */(0, 0));
  if(!_K0/* s2dWJ */){
    var _K1/* s2dWO */ = hs_eqInt64/* EXTERNAL */(_JZ/* s2dWH */, new Long/* EXTERNAL */(0, 0));
    if(!_K1/* s2dWO */){
      return new F(function(){return new Long/* EXTERNAL */(4294967295, -1);});
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return new F(function(){return new Long/* EXTERNAL */(1, 0);});
  }
},
_K2/* $fNumInt64_$csignum */ = function(_K3/* s2dWS */){
  return new F(function(){return _JY/* GHC.Int.$w$csignum */(E(_K3/* s2dWS */));});
},
_K4/* $fNumInt64 */ = {_:0,a:_JK/* GHC.Int.$fNumInt64_$c+ */,b:_JN/* GHC.Int.$fNumInt64_$c- */,c:_JH/* GHC.Int.$fNumInt64_$c* */,d:_JW/* GHC.Int.$fNumInt64_$cnegate */,e:_JU/* GHC.Int.$fNumInt64_$cabs */,f:_K2/* GHC.Int.$fNumInt64_$csignum */,g:_JF/* GHC.Int.$cfromInteger3 */},
_K5/* lvl */ = new T1(0,0),
_K6/* orInteger */ = function(_K7/* s1KS */, _K8/* s1KT */){
  while(1){
    var _K9/* s1KU */ = E(_K7/* s1KS */);
    if(!_K9/* s1KU */._){
      var _Ka/* s1KV */ = _K9/* s1KU */.a,
      _Kb/* s1KW */ = E(_K8/* s1KT */);
      if(!_Kb/* s1KW */._){
        return new T1(0,(_Ka/* s1KV */>>>0|_Kb/* s1KW */.a>>>0)>>>0&4294967295);
      }else{
        _K7/* s1KS */ = new T1(1,I_fromInt/* EXTERNAL */(_Ka/* s1KV */));
        _K8/* s1KT */ = _Kb/* s1KW */;
        continue;
      }
    }else{
      var _Kc/* s1L7 */ = E(_K8/* s1KT */);
      if(!_Kc/* s1L7 */._){
        _K7/* s1KS */ = _K9/* s1KU */;
        _K8/* s1KT */ = new T1(1,I_fromInt/* EXTERNAL */(_Kc/* s1L7 */.a));
        continue;
      }else{
        return new T1(1,I_or/* EXTERNAL */(_K9/* s1KU */.a, _Kc/* s1L7 */.a));
      }
    }
  }
},
_Kd/* shiftLInteger */ = function(_Ke/* s1Jk */, _Kf/* s1Jl */){
  while(1){
    var _Kg/* s1Jm */ = E(_Ke/* s1Jk */);
    if(!_Kg/* s1Jm */._){
      _Ke/* s1Jk */ = new T1(1,I_fromInt/* EXTERNAL */(_Kg/* s1Jm */.a));
      continue;
    }else{
      return new T1(1,I_shiftLeft/* EXTERNAL */(_Kg/* s1Jm */.a, _Kf/* s1Jl */));
    }
  }
},
_Kh/* mkInteger_f */ = function(_Ki/* s1S6 */){
  var _Kj/* s1S7 */ = E(_Ki/* s1S6 */);
  if(!_Kj/* s1S7 */._){
    return E(_K5/* GHC.Integer.Type.lvl */);
  }else{
    return new F(function(){return _K6/* GHC.Integer.Type.orInteger */(new T1(0,E(_Kj/* s1S7 */.a)), B(_Kd/* GHC.Integer.Type.shiftLInteger */(B(_Kh/* GHC.Integer.Type.mkInteger_f */(_Kj/* s1S7 */.b)), 31)));});
  }
},
_Kk/* log2I1 */ = new T1(0,1),
_Kl/* lvl2 */ = new T1(0,2147483647),
_Km/* plusInteger */ = function(_Kn/* s1Qe */, _Ko/* s1Qf */){
  while(1){
    var _Kp/* s1Qg */ = E(_Kn/* s1Qe */);
    if(!_Kp/* s1Qg */._){
      var _Kq/* s1Qh */ = _Kp/* s1Qg */.a,
      _Kr/* s1Qi */ = E(_Ko/* s1Qf */);
      if(!_Kr/* s1Qi */._){
        var _Ks/* s1Qj */ = _Kr/* s1Qi */.a,
        _Kt/* s1Qk */ = addC/* EXTERNAL */(_Kq/* s1Qh */, _Ks/* s1Qj */);
        if(!E(_Kt/* s1Qk */.b)){
          return new T1(0,_Kt/* s1Qk */.a);
        }else{
          _Kn/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_Kq/* s1Qh */));
          _Ko/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_Ks/* s1Qj */));
          continue;
        }
      }else{
        _Kn/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_Kq/* s1Qh */));
        _Ko/* s1Qf */ = _Kr/* s1Qi */;
        continue;
      }
    }else{
      var _Ku/* s1Qz */ = E(_Ko/* s1Qf */);
      if(!_Ku/* s1Qz */._){
        _Kn/* s1Qe */ = _Kp/* s1Qg */;
        _Ko/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_Ku/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_Kp/* s1Qg */.a, _Ku/* s1Qz */.a));
      }
    }
  }
},
_Kv/* lvl3 */ = new T(function(){
  return B(_Km/* GHC.Integer.Type.plusInteger */(_Kl/* GHC.Integer.Type.lvl2 */, _Kk/* GHC.Integer.Type.log2I1 */));
}),
_Kw/* negateInteger */ = function(_Kx/* s1QH */){
  var _Ky/* s1QI */ = E(_Kx/* s1QH */);
  if(!_Ky/* s1QI */._){
    var _Kz/* s1QK */ = E(_Ky/* s1QI */.a);
    return (_Kz/* s1QK */==(-2147483648)) ? E(_Kv/* GHC.Integer.Type.lvl3 */) : new T1(0, -_Kz/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_Ky/* s1QI */.a));
  }
},
_KA/* mkInteger */ = function(_KB/* s1Sf */, _KC/* s1Sg */){
  if(!E(_KB/* s1Sf */)){
    return new F(function(){return _Kw/* GHC.Integer.Type.negateInteger */(B(_Kh/* GHC.Integer.Type.mkInteger_f */(_KC/* s1Sg */)));});
  }else{
    return new F(function(){return _Kh/* GHC.Integer.Type.mkInteger_f */(_KC/* s1Sg */);});
  }
},
_KD/* sfn3 */ = 2147483647,
_KE/* sfn4 */ = 2147483647,
_KF/* sfn5 */ = 1,
_KG/* sfn6 */ = new T2(1,_KF/* sfn5 */,_6/* GHC.Types.[] */),
_KH/* sfn7 */ = new T2(1,_KE/* sfn4 */,_KG/* sfn6 */),
_KI/* sfn8 */ = new T2(1,_KD/* sfn3 */,_KH/* sfn7 */),
_KJ/* $fRandomCLLong3 */ = new T(function(){
  return B(_KA/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _KI/* sfn8 */));
}),
_KK/* sfn9 */ = 0,
_KL/* sfna */ = 0,
_KM/* sfnb */ = 2,
_KN/* sfnc */ = new T2(1,_KM/* sfnb */,_6/* GHC.Types.[] */),
_KO/* sfnd */ = new T2(1,_KL/* sfna */,_KN/* sfnc */),
_KP/* sfne */ = new T2(1,_KK/* sfn9 */,_KO/* sfnd */),
_KQ/* $fRandomCLLong4 */ = new T(function(){
  return B(_KA/* GHC.Integer.Type.mkInteger */(_av/* GHC.Types.False */, _KP/* sfne */));
}),
_KR/* $fRandomDouble4 */ = new Long/* EXTERNAL */(2, 0),
_KS/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_KT/* $fRandomDouble5 */ = new T(function(){
  return B(err/* EXTERNAL */(_KS/* System.Random.lvl1 */));
}),
_KU/* $fRandomDouble6 */ = new Long/* EXTERNAL */(1, 0),
_KV/* $fBoundedInt64_$cmaxBound */ = new Long/* EXTERNAL */(4294967295, 2147483647),
_KW/* $fBoundedInt64_$cminBound */ = new Long/* EXTERNAL */(0, -2147483648),
_KX/* $fBoundedInt64 */ = new T2(0,_KW/* GHC.Int.$fBoundedInt64_$cminBound */,_KV/* GHC.Int.$fBoundedInt64_$cmaxBound */),
_KY/* $fEnumRatio1 */ = new T1(0,1),
_KZ/* $p1Integral */ = function(_L0/* sveb */){
  return E(E(_L0/* sveb */).a);
},
_L1/* $p1Real */ = function(_L2/* svfM */){
  return E(E(_L2/* svfM */).a);
},
_L3/* fromInteger */ = function(_L4/* s6Gq */){
  return E(E(_L4/* s6Gq */).g);
},
_L5/* gtInteger */ = function(_L6/* s1G4 */, _L7/* s1G5 */){
  var _L8/* s1G6 */ = E(_L6/* s1G4 */);
  if(!_L8/* s1G6 */._){
    var _L9/* s1G7 */ = _L8/* s1G6 */.a,
    _La/* s1G8 */ = E(_L7/* s1G5 */);
    return (_La/* s1G8 */._==0) ? _L9/* s1G7 */>_La/* s1G8 */.a : I_compareInt/* EXTERNAL */(_La/* s1G8 */.a, _L9/* s1G7 */)<0;
  }else{
    var _Lb/* s1Gf */ = _L8/* s1G6 */.a,
    _Lc/* s1Gg */ = E(_L7/* s1G5 */);
    return (_Lc/* s1Gg */._==0) ? I_compareInt/* EXTERNAL */(_Lb/* s1Gf */, _Lc/* s1Gg */.a)>0 : I_compare/* EXTERNAL */(_Lb/* s1Gf */, _Lc/* s1Gg */.a)>0;
  }
},
_Ld/* maxBound */ = function(_Le/* smmz */){
  return E(E(_Le/* smmz */).b);
},
_Lf/* toInteger */ = function(_Lg/* svfB */){
  return E(E(_Lg/* svfB */).i);
},
_Lh/* integralEnumFrom */ = function(_Li/* svkx */, _Lj/* svky */, _Lk/* svkz */){
  var _Ll/* svkC */ = new T(function(){
    return B(_L3/* GHC.Num.fromInteger */(new T(function(){
      return B(_L1/* GHC.Real.$p1Real */(new T(function(){
        return B(_KZ/* GHC.Real.$p1Integral */(_Li/* svkx */));
      })));
    })));
  }),
  _Lm/* svkE */ = new T(function(){
    return B(_Ld/* GHC.Enum.maxBound */(_Lj/* svky */));
  }),
  _Ln/* svkF */ = function(_Lo/* svkG */){
    return (!B(_L5/* GHC.Integer.Type.gtInteger */(_Lo/* svkG */, B(A2(_Lf/* GHC.Real.toInteger */,_Li/* svkx */, _Lm/* svkE */))))) ? new T2(1,new T(function(){
      return B(A1(_Ll/* svkC */,_Lo/* svkG */));
    }),new T(function(){
      return B(_Ln/* svkF */(B(_Km/* GHC.Integer.Type.plusInteger */(_Lo/* svkG */, _KY/* GHC.Real.$fEnumRatio1 */))));
    })) : __Z/* EXTERNAL */;
  };
  return new F(function(){return _Ln/* svkF */(B(A2(_Lf/* GHC.Real.toInteger */,_Li/* svkx */, _Lk/* svkz */)));});
},
_Lp/* $fEnumInt64_$cenumFrom */ = function(_Lq/* B1 */){
  return new F(function(){return _Lh/* GHC.Real.integralEnumFrom */(_Lr/* GHC.Int.$fIntegralInt64 */, _KX/* GHC.Int.$fBoundedInt64 */, _Lq/* B1 */);});
},
_Ls/* $fEnumInteger1 */ = new T1(0,0),
_Lt/* geInteger */ = function(_Lu/* s1Fo */, _Lv/* s1Fp */){
  var _Lw/* s1Fq */ = E(_Lu/* s1Fo */);
  if(!_Lw/* s1Fq */._){
    var _Lx/* s1Fr */ = _Lw/* s1Fq */.a,
    _Ly/* s1Fs */ = E(_Lv/* s1Fp */);
    return (_Ly/* s1Fs */._==0) ? _Lx/* s1Fr */>=_Ly/* s1Fs */.a : I_compareInt/* EXTERNAL */(_Ly/* s1Fs */.a, _Lx/* s1Fr */)<=0;
  }else{
    var _Lz/* s1Fz */ = _Lw/* s1Fq */.a,
    _LA/* s1FA */ = E(_Lv/* s1Fp */);
    return (_LA/* s1FA */._==0) ? I_compareInt/* EXTERNAL */(_Lz/* s1Fz */, _LA/* s1FA */.a)>=0 : I_compare/* EXTERNAL */(_Lz/* s1Fz */, _LA/* s1FA */.a)>=0;
  }
},
_LB/* ltInteger */ = function(_LC/* s1FJ */, _LD/* s1FK */){
  var _LE/* s1FL */ = E(_LC/* s1FJ */);
  if(!_LE/* s1FL */._){
    var _LF/* s1FM */ = _LE/* s1FL */.a,
    _LG/* s1FN */ = E(_LD/* s1FK */);
    return (_LG/* s1FN */._==0) ? _LF/* s1FM */<_LG/* s1FN */.a : I_compareInt/* EXTERNAL */(_LG/* s1FN */.a, _LF/* s1FM */)>0;
  }else{
    var _LH/* s1FU */ = _LE/* s1FL */.a,
    _LI/* s1FV */ = E(_LD/* s1FK */);
    return (_LI/* s1FV */._==0) ? I_compareInt/* EXTERNAL */(_LH/* s1FU */, _LI/* s1FV */.a)<0 : I_compare/* EXTERNAL */(_LH/* s1FU */, _LI/* s1FV */.a)<0;
  }
},
_LJ/* up_fb */ = function(_LK/* smnV */, _LL/* smnW */, _LM/* smnX */, _LN/* smnY */, _LO/* smnZ */){
  var _LP/* smo0 */ = function(_LQ/* smo1 */){
    if(!B(_L5/* GHC.Integer.Type.gtInteger */(_LQ/* smo1 */, _LO/* smnZ */))){
      return new F(function(){return A2(_LK/* smnV */,_LQ/* smo1 */, new T(function(){
        return B(_LP/* smo0 */(B(_Km/* GHC.Integer.Type.plusInteger */(_LQ/* smo1 */, _LN/* smnY */))));
      }));});
    }else{
      return E(_LL/* smnW */);
    }
  };
  return new F(function(){return _LP/* smo0 */(_LM/* smnX */);});
},
_LR/* enumDeltaToIntegerFB */ = function(_LS/* smK3 */, _LT/* smK4 */, _LU/* smK5 */, _LV/* smK6 */, _LW/* smK7 */){
  if(!B(_Lt/* GHC.Integer.Type.geInteger */(_LV/* smK6 */, _Ls/* GHC.Enum.$fEnumInteger1 */))){
    var _LX/* smK9 */ = function(_LY/* smKa */){
      if(!B(_LB/* GHC.Integer.Type.ltInteger */(_LY/* smKa */, _LW/* smK7 */))){
        return new F(function(){return A2(_LS/* smK3 */,_LY/* smKa */, new T(function(){
          return B(_LX/* smK9 */(B(_Km/* GHC.Integer.Type.plusInteger */(_LY/* smKa */, _LV/* smK6 */))));
        }));});
      }else{
        return E(_LT/* smK4 */);
      }
    };
    return new F(function(){return _LX/* smK9 */(_LU/* smK5 */);});
  }else{
    return new F(function(){return _LJ/* GHC.Enum.up_fb */(_LS/* smK3 */, _LT/* smK4 */, _LU/* smK5 */, _LV/* smK6 */, _LW/* smK7 */);});
  }
},
_LZ/* minBound */ = function(_M0/* smmv */){
  return E(E(_M0/* smmv */).a);
},
_M1/* minusInteger */ = function(_M2/* s1P0 */, _M3/* s1P1 */){
  while(1){
    var _M4/* s1P2 */ = E(_M2/* s1P0 */);
    if(!_M4/* s1P2 */._){
      var _M5/* s1P3 */ = _M4/* s1P2 */.a,
      _M6/* s1P4 */ = E(_M3/* s1P1 */);
      if(!_M6/* s1P4 */._){
        var _M7/* s1P5 */ = _M6/* s1P4 */.a,
        _M8/* s1P6 */ = subC/* EXTERNAL */(_M5/* s1P3 */, _M7/* s1P5 */);
        if(!E(_M8/* s1P6 */.b)){
          return new T1(0,_M8/* s1P6 */.a);
        }else{
          _M2/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_M5/* s1P3 */));
          _M3/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_M7/* s1P5 */));
          continue;
        }
      }else{
        _M2/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_M5/* s1P3 */));
        _M3/* s1P1 */ = _M6/* s1P4 */;
        continue;
      }
    }else{
      var _M9/* s1Pl */ = E(_M3/* s1P1 */);
      if(!_M9/* s1Pl */._){
        _M2/* s1P0 */ = _M4/* s1P2 */;
        _M3/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_M9/* s1Pl */.a));
        continue;
      }else{
        return new T1(1,I_sub/* EXTERNAL */(_M4/* s1P2 */.a, _M9/* s1Pl */.a));
      }
    }
  }
},
_Ma/* integralEnumFromThen */ = function(_Mb/* svk6 */, _Mc/* svk7 */, _Md/* svk8 */, _Me/* svk9 */){
  var _Mf/* svka */ = B(A2(_Lf/* GHC.Real.toInteger */,_Mb/* svk6 */, _Me/* svk9 */)),
  _Mg/* svkb */ = B(A2(_Lf/* GHC.Real.toInteger */,_Mb/* svk6 */, _Md/* svk8 */));
  if(!B(_Lt/* GHC.Integer.Type.geInteger */(_Mf/* svka */, _Mg/* svkb */))){
    var _Mh/* svkf */ = new T(function(){
      return B(_L3/* GHC.Num.fromInteger */(new T(function(){
        return B(_L1/* GHC.Real.$p1Real */(new T(function(){
          return B(_KZ/* GHC.Real.$p1Integral */(_Mb/* svk6 */));
        })));
      })));
    }),
    _Mi/* svkj */ = function(_Mj/* svkg */, _Mk/* svkh */){
      return new T2(1,new T(function(){
        return B(A1(_Mh/* svkf */,_Mj/* svkg */));
      }),_Mk/* svkh */);
    };
    return new F(function(){return _LR/* GHC.Enum.enumDeltaToIntegerFB */(_Mi/* svkj */, _6/* GHC.Types.[] */, _Mg/* svkb */, B(_M1/* GHC.Integer.Type.minusInteger */(_Mf/* svka */, _Mg/* svkb */)), B(A2(_Lf/* GHC.Real.toInteger */,_Mb/* svk6 */, new T(function(){
      return B(_LZ/* GHC.Enum.minBound */(_Mc/* svk7 */));
    }))));});
  }else{
    var _Ml/* svkp */ = new T(function(){
      return B(_L3/* GHC.Num.fromInteger */(new T(function(){
        return B(_L1/* GHC.Real.$p1Real */(new T(function(){
          return B(_KZ/* GHC.Real.$p1Integral */(_Mb/* svk6 */));
        })));
      })));
    }),
    _Mm/* svkt */ = function(_Mn/* svkq */, _Mo/* svkr */){
      return new T2(1,new T(function(){
        return B(A1(_Ml/* svkp */,_Mn/* svkq */));
      }),_Mo/* svkr */);
    };
    return new F(function(){return _LR/* GHC.Enum.enumDeltaToIntegerFB */(_Mm/* svkt */, _6/* GHC.Types.[] */, _Mg/* svkb */, B(_M1/* GHC.Integer.Type.minusInteger */(_Mf/* svka */, _Mg/* svkb */)), B(A2(_Lf/* GHC.Real.toInteger */,_Mb/* svk6 */, new T(function(){
      return B(_Ld/* GHC.Enum.maxBound */(_Mc/* svk7 */));
    }))));});
  }
},
_Mp/* $fEnumInt64_$cenumFromThen */ = function(_Mq/* B2 */, _Lq/* B1 */){
  return new F(function(){return _Ma/* GHC.Real.integralEnumFromThen */(_Lr/* GHC.Int.$fIntegralInt64 */, _KX/* GHC.Int.$fBoundedInt64 */, _Mq/* B2 */, _Lq/* B1 */);});
},
_Mr/* integralEnumFromThenTo */ = function(_Ms/* svjD */, _Mt/* svjE */, _Mu/* svjF */, _Mv/* svjG */){
  var _Mw/* svjH */ = B(A2(_Lf/* GHC.Real.toInteger */,_Ms/* svjD */, _Mt/* svjE */)),
  _Mx/* svjK */ = new T(function(){
    return B(_L3/* GHC.Num.fromInteger */(new T(function(){
      return B(_L1/* GHC.Real.$p1Real */(new T(function(){
        return B(_KZ/* GHC.Real.$p1Integral */(_Ms/* svjD */));
      })));
    })));
  }),
  _My/* svjO */ = function(_Mz/* svjL */, _MA/* svjM */){
    return new T2(1,new T(function(){
      return B(A1(_Mx/* svjK */,_Mz/* svjL */));
    }),_MA/* svjM */);
  };
  return new F(function(){return _LR/* GHC.Enum.enumDeltaToIntegerFB */(_My/* svjO */, _6/* GHC.Types.[] */, _Mw/* svjH */, B(_M1/* GHC.Integer.Type.minusInteger */(B(A2(_Lf/* GHC.Real.toInteger */,_Ms/* svjD */, _Mu/* svjF */)), _Mw/* svjH */)), B(A2(_Lf/* GHC.Real.toInteger */,_Ms/* svjD */, _Mv/* svjG */)));});
},
_MB/* $fEnumInt64_$cenumFromThenTo */ = function(_MC/* B3 */, _Mq/* B2 */, _Lq/* B1 */){
  return new F(function(){return _Mr/* GHC.Real.integralEnumFromThenTo */(_Lr/* GHC.Int.$fIntegralInt64 */, _MC/* B3 */, _Mq/* B2 */, _Lq/* B1 */);});
},
_MD/* integralEnumFromTo */ = function(_ME/* svjS */, _MF/* svjT */, _MG/* svjU */){
  var _MH/* svjX */ = new T(function(){
    return B(_L3/* GHC.Num.fromInteger */(new T(function(){
      return B(_L1/* GHC.Real.$p1Real */(new T(function(){
        return B(_KZ/* GHC.Real.$p1Integral */(_ME/* svjS */));
      })));
    })));
  }),
  _MI/* svjZ */ = function(_MJ/* svk0 */){
    return (!B(_L5/* GHC.Integer.Type.gtInteger */(_MJ/* svk0 */, B(A2(_Lf/* GHC.Real.toInteger */,_ME/* svjS */, _MG/* svjU */))))) ? new T2(1,new T(function(){
      return B(A1(_MH/* svjX */,_MJ/* svk0 */));
    }),new T(function(){
      return B(_MI/* svjZ */(B(_Km/* GHC.Integer.Type.plusInteger */(_MJ/* svk0 */, _KY/* GHC.Real.$fEnumRatio1 */))));
    })) : __Z/* EXTERNAL */;
  };
  return new F(function(){return _MI/* svjZ */(B(A2(_Lf/* GHC.Real.toInteger */,_ME/* svjS */, _MF/* svjT */)));});
},
_MK/* $fEnumInt64_$cenumFromTo */ = function(_Mq/* B2 */, _Lq/* B1 */){
  return new F(function(){return _MD/* GHC.Real.integralEnumFromTo */(_Lr/* GHC.Int.$fIntegralInt64 */, _Mq/* B2 */, _Lq/* B1 */);});
},
_ML/* $fEnumInt6 */ = new T(function(){
  return hs_intToInt64/* EXTERNAL */(2147483647);
}),
_MM/* smallInteger */ = function(_MN/* B1 */){
  return new T1(0,_MN/* B1 */);
},
_MO/* int64ToInteger */ = function(_MP/* s1RA */){
  var _MQ/* s1RC */ = hs_intToInt64/* EXTERNAL */(2147483647),
  _MR/* s1RG */ = hs_leInt64/* EXTERNAL */(_MP/* s1RA */, _MQ/* s1RC */);
  if(!_MR/* s1RG */){
    return new T1(1,I_fromInt64/* EXTERNAL */(_MP/* s1RA */));
  }else{
    var _MS/* s1RN */ = hs_intToInt64/* EXTERNAL */(-2147483648),
    _MT/* s1RR */ = hs_geInt64/* EXTERNAL */(_MP/* s1RA */, _MS/* s1RN */);
    if(!_MT/* s1RR */){
      return new T1(1,I_fromInt64/* EXTERNAL */(_MP/* s1RA */));
    }else{
      var _MU/* s1RY */ = hs_int64ToInt/* EXTERNAL */(_MP/* s1RA */);
      return new F(function(){return _MM/* GHC.Integer.Type.smallInteger */(_MU/* s1RY */);});
    }
  }
},
_MV/* $fIntegralInt64_$ctoInteger */ = function(_MW/* s2dYm */){
  return new F(function(){return _MO/* GHC.Integer.Type.int64ToInteger */(E(_MW/* s2dYm */));});
},
_MX/* integerToJSString */ = function(_MY/* s1Iv */){
  while(1){
    var _MZ/* s1Iw */ = E(_MY/* s1Iv */);
    if(!_MZ/* s1Iw */._){
      _MY/* s1Iv */ = new T1(1,I_fromInt/* EXTERNAL */(_MZ/* s1Iw */.a));
      continue;
    }else{
      return new F(function(){return I_toString/* EXTERNAL */(_MZ/* s1Iw */.a);});
    }
  }
},
_N0/* integerToString */ = function(_N1/* sfbi */, _N2/* sfbj */){
  return new F(function(){return _2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_MX/* GHC.Integer.Type.integerToJSString */(_N1/* sfbi */))), _N2/* sfbj */);});
},
_N3/* shows9 */ = new T1(0,0),
_N4/* $w$cshowsPrec1 */ = function(_N5/* sfcx */, _N6/* sfcy */, _N7/* sfcz */){
  if(_N5/* sfcx */<=6){
    return new F(function(){return _N0/* GHC.Show.integerToString */(_N6/* sfcy */, _N7/* sfcz */);});
  }else{
    if(!B(_LB/* GHC.Integer.Type.ltInteger */(_N6/* sfcy */, _N3/* GHC.Show.shows9 */))){
      return new F(function(){return _N0/* GHC.Show.integerToString */(_N6/* sfcy */, _N7/* sfcz */);});
    }else{
      return new T2(1,_3c/* GHC.Show.shows8 */,new T(function(){
        return B(_2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_MX/* GHC.Integer.Type.integerToJSString */(_N6/* sfcy */))), new T2(1,_3b/* GHC.Show.shows7 */,_N7/* sfcz */)));
      }));
    }
  }
},
_N8/* $fShowInt64_$cshow */ = function(_N9/* s2dYy */){
  return new F(function(){return _N4/* GHC.Show.$w$cshowsPrec1 */(0, B(_MV/* GHC.Int.$fIntegralInt64_$ctoInteger */(_N9/* s2dYy */)), _6/* GHC.Types.[] */);});
},
_Na/* $fShowInt3 */ = function(_Nb/* s2dYA */, _Nc/* s2dYB */){
  return new F(function(){return _N4/* GHC.Show.$w$cshowsPrec1 */(0, B(_MO/* GHC.Integer.Type.int64ToInteger */(E(_Nb/* s2dYA */))), _Nc/* s2dYB */);});
},
_Nd/* $fShowInt64_$cshowList */ = function(_Ne/* s2dYF */, _Nf/* s2dYG */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_Na/* GHC.Int.$fShowInt3 */, _Ne/* s2dYF */, _Nf/* s2dYG */);});
},
_Ng/* $fShowInt64_$cshowsPrec */ = function(_Nh/* s2dYp */, _Ni/* s2dYq */){
  var _Nj/* s2dYr */ = new T(function(){
    return B(_MO/* GHC.Integer.Type.int64ToInteger */(E(_Ni/* s2dYq */)));
  });
  return function(_Nk/* s2dYu */){
    return new F(function(){return _N4/* GHC.Show.$w$cshowsPrec1 */(E(_Nh/* s2dYp */), _Nj/* s2dYr */, _Nk/* s2dYu */);});
  };
},
_Nl/* $fShowInt64 */ = new T3(0,_Ng/* GHC.Int.$fShowInt64_$cshowsPrec */,_N8/* GHC.Int.$fShowInt64_$cshow */,_Nd/* GHC.Int.$fShowInt64_$cshowList */),
_Nm/* lvl */ = new T2(1,_3b/* GHC.Show.shows7 */,_6/* GHC.Types.[] */),
_Nn/* $fShow(,)1 */ = function(_No/* sfg4 */, _Np/* sfg5 */, _Nq/* sfg6 */){
  return new F(function(){return A1(_No/* sfg4 */,new T2(1,_23/* GHC.Show.showList__1 */,new T(function(){
    return B(A1(_Np/* sfg5 */,_Nq/* sfg6 */));
  })));});
},
_Nr/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_Ns/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_Nt/* errorEmptyList */ = function(_Nu/* s9t7 */){
  return new F(function(){return err/* EXTERNAL */(B(_2/* GHC.Base.++ */(_Ns/* GHC.List.prel_list_str */, new T(function(){
    return B(_2/* GHC.Base.++ */(_Nu/* s9t7 */, _Nr/* GHC.List.lvl */));
  },1))));});
},
_Nv/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("foldr1"));
}),
_Nw/* lvl8 */ = new T(function(){
  return B(_Nt/* GHC.List.errorEmptyList */(_Nv/* GHC.List.lvl7 */));
}),
_Nx/* foldr1 */ = function(_Ny/* s9Ah */, _Nz/* s9Ai */){
  var _NA/* s9Aj */ = E(_Nz/* s9Ai */);
  if(!_NA/* s9Aj */._){
    return E(_Nw/* GHC.List.lvl8 */);
  }else{
    var _NB/* s9Ak */ = _NA/* s9Aj */.a,
    _NC/* s9Am */ = E(_NA/* s9Aj */.b);
    if(!_NC/* s9Am */._){
      return E(_NB/* s9Ak */);
    }else{
      return new F(function(){return A2(_Ny/* s9Ah */,_NB/* s9Ak */, new T(function(){
        return B(_Nx/* GHC.List.foldr1 */(_Ny/* s9Ah */, _NC/* s9Am */));
      }));});
    }
  }
},
_ND/* lvl14 */ = function(_NE/* smEb */){
  return new F(function(){return _3d/* GHC.Show.$wshowSignedInt */(0, -2147483648, _NE/* smEb */);});
},
_NF/* lvl15 */ = function(_NG/* smEc */){
  return new F(function(){return _3d/* GHC.Show.$wshowSignedInt */(0, 2147483647, _NG/* smEc */);});
},
_NH/* lvl16 */ = new T2(1,_NF/* GHC.Enum.lvl15 */,_6/* GHC.Types.[] */),
_NI/* lvl17 */ = new T2(1,_ND/* GHC.Enum.lvl14 */,_NH/* GHC.Enum.lvl16 */),
_NJ/* lvl18 */ = new T(function(){
  return B(_Nx/* GHC.List.foldr1 */(_Nn/* GHC.Show.$fShow(,)1 */, _NI/* GHC.Enum.lvl17 */));
}),
_NK/* lvl19 */ = new T(function(){
  return B(A1(_NJ/* GHC.Enum.lvl18 */,_Nm/* GHC.Enum.lvl */));
}),
_NL/* lvl20 */ = new T2(1,_3c/* GHC.Show.shows8 */,_NK/* GHC.Enum.lvl19 */),
_NM/* lvl21 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */(") is outside of Int\'s bounds ", _NL/* GHC.Enum.lvl20 */));
}),
_NN/* show */ = function(_NO/* sfb3 */){
  return E(E(_NO/* sfb3 */).b);
},
_NP/* lvl22 */ = function(_NQ/* smEd */, _NR/* smEe */, _NS/* smEf */){
  var _NT/* smEj */ = new T(function(){
    var _NU/* smEi */ = new T(function(){
      return B(unAppCStr/* EXTERNAL */("}: value (", new T(function(){
        return B(_2/* GHC.Base.++ */(B(A2(_NN/* GHC.Show.show */,_NS/* smEf */, _NR/* smEe */)), _NM/* GHC.Enum.lvl21 */));
      })));
    },1);
    return B(_2/* GHC.Base.++ */(_NQ/* smEd */, _NU/* smEi */));
  });
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.fromEnum{", _NT/* smEj */)));});
},
_NV/* fromEnumError */ = function(_NW/* smEl */, _NX/* smEm */, _NY/* smEn */){
  return new F(function(){return _NP/* GHC.Enum.lvl22 */(_NX/* smEm */, _NY/* smEn */, _NW/* smEl */);});
},
_NZ/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Int64"));
}),
_O0/* lvl13 */ = function(_O1/* s2dYH */){
  return new F(function(){return _NV/* GHC.Enum.fromEnumError */(_Nl/* GHC.Int.$fShowInt64 */, _NZ/* GHC.Int.lvl1 */, _O1/* s2dYH */);});
},
_O2/* $fEnumInt7 */ = function(_O3/* s2dYI */){
  return new F(function(){return _O0/* GHC.Int.lvl13 */(_O3/* s2dYI */);});
},
_O4/* $fEnumInt9 */ = new T(function(){
  return hs_intToInt64/* EXTERNAL */(-2147483648);
}),
_O5/* $w$cfromEnum */ = function(_O6/* s2dYK */){
  var _O7/* s2dYO */ = hs_geInt64/* EXTERNAL */(_O6/* s2dYK */, E(_O4/* GHC.Int.$fEnumInt9 */));
  if(!_O7/* s2dYO */){
    return new F(function(){return _O2/* GHC.Int.$fEnumInt7 */(_O6/* s2dYK */);});
  }else{
    var _O8/* s2dYW */ = hs_leInt64/* EXTERNAL */(_O6/* s2dYK */, E(_ML/* GHC.Int.$fEnumInt6 */));
    if(!_O8/* s2dYW */){
      return new F(function(){return _O2/* GHC.Int.$fEnumInt7 */(_O6/* s2dYK */);});
    }else{
      var _O9/* s2dZ2 */ = hs_int64ToInt/* EXTERNAL */(_O6/* s2dYK */);
      return E(_O9/* s2dZ2 */);
    }
  }
},
_Oa/* $fEnumInt64_$cfromEnum */ = function(_Ob/* s2dZ5 */){
  return new F(function(){return _O5/* GHC.Int.$w$cfromEnum */(E(_Ob/* s2dZ5 */));});
},
_Oc/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}: tried to take `pred\' of minBound"));
}),
_Od/* lvl2 */ = function(_Oe/* smrD */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.pred{", new T(function(){
    return B(_2/* GHC.Base.++ */(_Oe/* smrD */, _Oc/* GHC.Enum.lvl1 */));
  }))));});
},
_Of/* predError */ = function(_Og/* B1 */){
  return new F(function(){return _Od/* GHC.Enum.lvl2 */(_Og/* B1 */);});
},
_Oh/* $fEnumInt10 */ = new T(function(){
  return B(_Of/* GHC.Enum.predError */(_NZ/* GHC.Int.lvl1 */));
}),
_Oi/* $w$cpred */ = function(_Oj/* s2dXS */){
  var _Ok/* s2dXU */ = hs_neInt64/* EXTERNAL */(_Oj/* s2dXS */, new Long/* EXTERNAL */(0, -2147483648));
  if(!_Ok/* s2dXU */){
    return E(_Oh/* GHC.Int.$fEnumInt10 */);
  }else{
    var _Ol/* s2dY0 */ = hs_minusInt64/* EXTERNAL */(_Oj/* s2dXS */, new Long/* EXTERNAL */(1, 0));
    return E(_Ol/* s2dY0 */);
  }
},
_Om/* $fEnumInt64_$cpred */ = function(_On/* s2dY3 */){
  return new F(function(){return _Oi/* GHC.Int.$w$cpred */(E(_On/* s2dY3 */));});
},
_Oo/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}: tried to take `succ\' of maxBound"));
}),
_Op/* lvl4 */ = function(_Oq/* smrG */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Enum.succ{", new T(function(){
    return B(_2/* GHC.Base.++ */(_Oq/* smrG */, _Oo/* GHC.Enum.lvl3 */));
  }))));});
},
_Or/* succError */ = function(_Og/* B1 */){
  return new F(function(){return _Op/* GHC.Enum.lvl4 */(_Og/* B1 */);});
},
_Os/* $fEnumInt11 */ = new T(function(){
  return B(_Or/* GHC.Enum.succError */(_NZ/* GHC.Int.lvl1 */));
}),
_Ot/* $w$csucc */ = function(_Ou/* s2dY7 */){
  var _Ov/* s2dY9 */ = hs_neInt64/* EXTERNAL */(_Ou/* s2dY7 */, new Long/* EXTERNAL */(4294967295, 2147483647));
  if(!_Ov/* s2dY9 */){
    return E(_Os/* GHC.Int.$fEnumInt11 */);
  }else{
    var _Ow/* s2dYf */ = hs_plusInt64/* EXTERNAL */(_Ou/* s2dY7 */, new Long/* EXTERNAL */(1, 0));
    return E(_Ow/* s2dYf */);
  }
},
_Ox/* $fEnumInt64_$csucc */ = function(_Oy/* s2dYi */){
  return new F(function(){return _Ot/* GHC.Int.$w$csucc */(E(_Oy/* s2dYi */));});
},
_Oz/* $fEnumInt64_$ctoEnum */ = function(_OA/* s2dXL */){
  return new F(function(){return hs_intToInt64/* EXTERNAL */(E(_OA/* s2dXL */));});
},
_OB/* $fEnumInt64 */ = new T(function(){
  return {_:0,a:_Ox/* GHC.Int.$fEnumInt64_$csucc */,b:_Om/* GHC.Int.$fEnumInt64_$cpred */,c:_Oz/* GHC.Int.$fEnumInt64_$ctoEnum */,d:_Oa/* GHC.Int.$fEnumInt64_$cfromEnum */,e:_Lp/* GHC.Int.$fEnumInt64_$cenumFrom */,f:_Mp/* GHC.Int.$fEnumInt64_$cenumFromThen */,g:_MK/* GHC.Int.$fEnumInt64_$cenumFromTo */,h:_MB/* GHC.Int.$fEnumInt64_$cenumFromThenTo */};
}),
_OC/* minusInt64# */ = function(_OD/* sdC */, _OE/* sdD */){
  var _OF/* sdF */ = hs_minusInt64/* EXTERNAL */(_OD/* sdC */, _OE/* sdD */);
  return E(_OF/* sdF */);
},
_OG/* quotInt64# */ = function(_OH/* sdk */, _OI/* sdl */){
  var _OJ/* sdn */ = hs_quotInt64/* EXTERNAL */(_OH/* sdk */, _OI/* sdl */);
  return E(_OJ/* sdn */);
},
_OK/* divInt64# */ = function(_OL/* s2dwk */, _OM/* s2dwl */){
  var _ON/* s2dwn */ = hs_intToInt64/* EXTERNAL */(1),
  _OO/* s2dwp */ = _ON/* s2dwn */,
  _OP/* s2dwr */ = hs_intToInt64/* EXTERNAL */(0),
  _OQ/* s2dwt */ = _OP/* s2dwr */,
  _OR/* s2dwv */ = hs_gtInt64/* EXTERNAL */(_OL/* s2dwk */, _OQ/* s2dwt */),
  _OS/* s2dwy */ = function(_OT/* s2dwz */){
    var _OU/* s2dwB */ = hs_ltInt64/* EXTERNAL */(_OL/* s2dwk */, _OQ/* s2dwt */);
    if(!_OU/* s2dwB */){
      return new F(function(){return _OG/* GHC.IntWord64.quotInt64# */(_OL/* s2dwk */, _OM/* s2dwl */);});
    }else{
      var _OV/* s2dwG */ = hs_gtInt64/* EXTERNAL */(_OM/* s2dwl */, _OQ/* s2dwt */);
      if(!_OV/* s2dwG */){
        return new F(function(){return _OG/* GHC.IntWord64.quotInt64# */(_OL/* s2dwk */, _OM/* s2dwl */);});
      }else{
        var _OW/* s2dwL */ = hs_plusInt64/* EXTERNAL */(_OL/* s2dwk */, _OO/* s2dwp */),
        _OX/* s2dwP */ = hs_quotInt64/* EXTERNAL */(_OW/* s2dwL */, _OM/* s2dwl */);
        return new F(function(){return _OC/* GHC.IntWord64.minusInt64# */(_OX/* s2dwP */, _OO/* s2dwp */);});
      }
    }
  };
  if(!_OR/* s2dwv */){
    return new F(function(){return _OS/* s2dwy */(_/* EXTERNAL */);});
  }else{
    var _OY/* s2dwU */ = hs_ltInt64/* EXTERNAL */(_OM/* s2dwl */, _OQ/* s2dwt */);
    if(!_OY/* s2dwU */){
      return new F(function(){return _OS/* s2dwy */(_/* EXTERNAL */);});
    }else{
      var _OZ/* s2dwZ */ = hs_minusInt64/* EXTERNAL */(_OL/* s2dwk */, _OO/* s2dwp */),
      _P0/* s2dx3 */ = hs_quotInt64/* EXTERNAL */(_OZ/* s2dwZ */, _OM/* s2dwl */);
      return new F(function(){return _OC/* GHC.IntWord64.minusInt64# */(_P0/* s2dx3 */, _OO/* s2dwp */);});
    }
  }
},
_P1/* $fExceptionArithException_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_P2/* $fExceptionArithException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.Exception"));
}),
_P3/* $fExceptionArithException_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ArithException"));
}),
_P4/* $fExceptionArithException_wild */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_P1/* GHC.Exception.$fExceptionArithException_ww2 */,_P2/* GHC.Exception.$fExceptionArithException_ww4 */,_P3/* GHC.Exception.$fExceptionArithException_ww5 */),
_P5/* $fExceptionArithException8 */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_P4/* GHC.Exception.$fExceptionArithException_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_P6/* $fExceptionArithException7 */ = function(_P7/* s2S2z */){
  return E(_P5/* GHC.Exception.$fExceptionArithException8 */);
},
_P8/* $fExceptionArithException_$cfromException */ = function(_P9/* s2S35 */){
  var _Pa/* s2S36 */ = E(_P9/* s2S35 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_Pa/* s2S36 */.a)), _P6/* GHC.Exception.$fExceptionArithException7 */, _Pa/* s2S36 */.b);});
},
_Pb/* $fExceptionArithException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ratio has zero denominator"));
}),
_Pc/* $fExceptionArithException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("denormal"));
}),
_Pd/* $fExceptionArithException3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("divide by zero"));
}),
_Pe/* $fExceptionArithException4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("loss of precision"));
}),
_Pf/* $fExceptionArithException5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic underflow"));
}),
_Pg/* $fExceptionArithException6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic overflow"));
}),
_Ph/* $w$cshowsPrec */ = function(_Pi/* s2S3a */, _Pj/* s2S3b */){
  switch(E(_Pi/* s2S3a */)){
    case 0:
      return new F(function(){return _2/* GHC.Base.++ */(_Pg/* GHC.Exception.$fExceptionArithException6 */, _Pj/* s2S3b */);});
      break;
    case 1:
      return new F(function(){return _2/* GHC.Base.++ */(_Pf/* GHC.Exception.$fExceptionArithException5 */, _Pj/* s2S3b */);});
      break;
    case 2:
      return new F(function(){return _2/* GHC.Base.++ */(_Pe/* GHC.Exception.$fExceptionArithException4 */, _Pj/* s2S3b */);});
      break;
    case 3:
      return new F(function(){return _2/* GHC.Base.++ */(_Pd/* GHC.Exception.$fExceptionArithException3 */, _Pj/* s2S3b */);});
      break;
    case 4:
      return new F(function(){return _2/* GHC.Base.++ */(_Pc/* GHC.Exception.$fExceptionArithException2 */, _Pj/* s2S3b */);});
      break;
    default:
      return new F(function(){return _2/* GHC.Base.++ */(_Pb/* GHC.Exception.$fExceptionArithException1 */, _Pj/* s2S3b */);});
  }
},
_Pk/* $fExceptionArithException_$cshow */ = function(_Pl/* s2S3g */){
  return new F(function(){return _Ph/* GHC.Exception.$w$cshowsPrec */(_Pl/* s2S3g */, _6/* GHC.Types.[] */);});
},
_Pm/* $fExceptionArithException_$cshowsPrec */ = function(_Pn/* s2S3d */, _Po/* s2S3e */, _Pp/* s2S3f */){
  return new F(function(){return _Ph/* GHC.Exception.$w$cshowsPrec */(_Po/* s2S3e */, _Pp/* s2S3f */);});
},
_Pq/* $fShowArithException_$cshowList */ = function(_Pr/* s2S3h */, _Ps/* s2S3i */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_Ph/* GHC.Exception.$w$cshowsPrec */, _Pr/* s2S3h */, _Ps/* s2S3i */);});
},
_Pt/* $fShowArithException */ = new T3(0,_Pm/* GHC.Exception.$fExceptionArithException_$cshowsPrec */,_Pk/* GHC.Exception.$fExceptionArithException_$cshow */,_Pq/* GHC.Exception.$fShowArithException_$cshowList */),
_Pu/* $fExceptionArithException */ = new T(function(){
  return new T5(0,_P6/* GHC.Exception.$fExceptionArithException7 */,_Pt/* GHC.Exception.$fShowArithException */,_Pv/* GHC.Exception.$fExceptionArithException_$ctoException */,_P8/* GHC.Exception.$fExceptionArithException_$cfromException */,_Pk/* GHC.Exception.$fExceptionArithException_$cshow */);
}),
_Pv/* $fExceptionArithException_$ctoException */ = function(_Pw/* B1 */){
  return new T2(0,_Pu/* GHC.Exception.$fExceptionArithException */,_Pw/* B1 */);
},
_Px/* DivideByZero */ = 3,
_Py/* divZeroException */ = new T(function(){
  return B(_Pv/* GHC.Exception.$fExceptionArithException_$ctoException */(_Px/* GHC.Exception.DivideByZero */));
}),
_Pz/* divZeroError */ = new T(function(){
  return die/* EXTERNAL */(_Py/* GHC.Exception.divZeroException */);
}),
_PA/* Overflow */ = 0,
_PB/* overflowException */ = new T(function(){
  return B(_Pv/* GHC.Exception.$fExceptionArithException_$ctoException */(_PA/* GHC.Exception.Overflow */));
}),
_PC/* overflowError */ = new T(function(){
  return die/* EXTERNAL */(_PB/* GHC.Exception.overflowException */);
}),
_PD/* $w$cdiv2 */ = function(_PE/* s2e0N */, _PF/* s2e0O */){
  var _PG/* s2e0Q */ = hs_eqInt64/* EXTERNAL */(_PF/* s2e0O */, new Long/* EXTERNAL */(0, 0));
  if(!_PG/* s2e0Q */){
    var _PH/* s2e0V */ = hs_eqInt64/* EXTERNAL */(_PF/* s2e0O */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_PH/* s2e0V */){
      return new F(function(){return _OK/* GHC.Int.divInt64# */(_PE/* s2e0N */, _PF/* s2e0O */);});
    }else{
      var _PI/* s2e10 */ = hs_eqInt64/* EXTERNAL */(_PE/* s2e0N */, new Long/* EXTERNAL */(0, -2147483648));
      if(!_PI/* s2e10 */){
        return new F(function(){return _OK/* GHC.Int.divInt64# */(_PE/* s2e0N */, _PF/* s2e0O */);});
      }else{
        return E(_PC/* GHC.Real.overflowError */);
      }
    }
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_PJ/* $fIntegralInt64_$cdiv */ = function(_PK/* s2e16 */, _PL/* s2e17 */){
  return new F(function(){return _PD/* GHC.Int.$w$cdiv2 */(E(_PK/* s2e16 */), E(_PL/* s2e17 */));});
},
_PM/* $fIntegralInt1 */ = new Long/* EXTERNAL */(0, 0),
_PN/* plusInt64# */ = function(_PO/* sdw */, _PP/* sdx */){
  var _PQ/* sdz */ = hs_plusInt64/* EXTERNAL */(_PO/* sdw */, _PP/* sdx */);
  return E(_PQ/* sdz */);
},
_PR/* modInt64# */ = function(_PS/* s2dvH */, _PT/* s2dvI */){
  var _PU/* s2dvK */ = hs_remInt64/* EXTERNAL */(_PS/* s2dvH */, _PT/* s2dvI */),
  _PV/* s2dvM */ = _PU/* s2dvK */,
  _PW/* s2dvO */ = hs_intToInt64/* EXTERNAL */(0),
  _PX/* s2dvQ */ = _PW/* s2dvO */,
  _PY/* s2dvS */ = hs_gtInt64/* EXTERNAL */(_PS/* s2dvH */, _PX/* s2dvQ */),
  _PZ/* s2dvV */ = function(_Q0/* s2dvW */){
    var _Q1/* s2dvY */ = hs_neInt64/* EXTERNAL */(_PV/* s2dvM */, _PX/* s2dvQ */);
    if(!_Q1/* s2dvY */){
      return E(_PX/* s2dvQ */);
    }else{
      return new F(function(){return _PN/* GHC.IntWord64.plusInt64# */(_PV/* s2dvM */, _PT/* s2dvI */);});
    }
  },
  _Q2/* s2dw2 */ = function(_Q3/* s2dw3 */){
    var _Q4/* s2dw5 */ = hs_ltInt64/* EXTERNAL */(_PS/* s2dvH */, _PX/* s2dvQ */);
    if(!_Q4/* s2dw5 */){
      return E(_PV/* s2dvM */);
    }else{
      var _Q5/* s2dwa */ = hs_gtInt64/* EXTERNAL */(_PT/* s2dvI */, _PX/* s2dvQ */);
      if(!_Q5/* s2dwa */){
        return E(_PV/* s2dvM */);
      }else{
        return new F(function(){return _PZ/* s2dvV */(_/* EXTERNAL */);});
      }
    }
  };
  if(!_PY/* s2dvS */){
    return new F(function(){return _Q2/* s2dw2 */(_/* EXTERNAL */);});
  }else{
    var _Q6/* s2dwg */ = hs_ltInt64/* EXTERNAL */(_PT/* s2dvI */, _PX/* s2dvQ */);
    if(!_Q6/* s2dwg */){
      return new F(function(){return _Q2/* s2dw2 */(_/* EXTERNAL */);});
    }else{
      return new F(function(){return _PZ/* s2dvV */(_/* EXTERNAL */);});
    }
  }
},
_Q7/* $w$cdivMod2 */ = function(_Q8/* s2dZ9 */, _Q9/* s2dZa */){
  var _Qa/* s2dZc */ = hs_eqInt64/* EXTERNAL */(_Q9/* s2dZa */, new Long/* EXTERNAL */(0, 0));
  if(!_Qa/* s2dZc */){
    var _Qb/* s2dZh */ = hs_eqInt64/* EXTERNAL */(_Q9/* s2dZa */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Qb/* s2dZh */){
      return new T2(0,new T(function(){
        return B(_OK/* GHC.Int.divInt64# */(_Q8/* s2dZ9 */, _Q9/* s2dZa */));
      }),new T(function(){
        return B(_PR/* GHC.Int.modInt64# */(_Q8/* s2dZ9 */, _Q9/* s2dZa */));
      }));
    }else{
      var _Qc/* s2dZq */ = hs_eqInt64/* EXTERNAL */(_Q8/* s2dZ9 */, new Long/* EXTERNAL */(0, -2147483648));
      return (!_Qc/* s2dZq */) ? new T2(0,new T(function(){
        return B(_OK/* GHC.Int.divInt64# */(_Q8/* s2dZ9 */, _Q9/* s2dZa */));
      }),new T(function(){
        return B(_PR/* GHC.Int.modInt64# */(_Q8/* s2dZ9 */, _Q9/* s2dZa */));
      })) : new T2(0,_PC/* GHC.Real.overflowError */,_PM/* GHC.Int.$fIntegralInt1 */);
    }
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_Qd/* $fIntegralInt64_$cdivMod */ = function(_Qe/* s2dZz */, _Qf/* s2dZA */){
  var _Qg/* s2dZF */ = B(_Q7/* GHC.Int.$w$cdivMod2 */(E(_Qe/* s2dZz */), E(_Qf/* s2dZA */)));
  return new T2(0,_Qg/* s2dZF */.a,_Qg/* s2dZF */.b);
},
_Qh/* $w$cmod */ = function(_Qi/* s2e0t */, _Qj/* s2e0u */){
  var _Qk/* s2e0w */ = hs_eqInt64/* EXTERNAL */(_Qj/* s2e0u */, new Long/* EXTERNAL */(0, 0));
  if(!_Qk/* s2e0w */){
    var _Ql/* s2e0B */ = hs_eqInt64/* EXTERNAL */(_Qj/* s2e0u */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Ql/* s2e0B */){
      return new F(function(){return _PR/* GHC.Int.modInt64# */(_Qi/* s2e0t */, _Qj/* s2e0u */);});
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_Qm/* $fIntegralInt64_$cmod */ = function(_Qn/* s2e0G */, _Qo/* s2e0H */){
  return new F(function(){return _Qh/* GHC.Int.$w$cmod */(E(_Qn/* s2e0G */), E(_Qo/* s2e0H */));});
},
_Qp/* $w$cquot */ = function(_Qq/* s2e1B */, _Qr/* s2e1C */){
  var _Qs/* s2e1E */ = hs_eqInt64/* EXTERNAL */(_Qr/* s2e1C */, new Long/* EXTERNAL */(0, 0));
  if(!_Qs/* s2e1E */){
    var _Qt/* s2e1J */ = hs_eqInt64/* EXTERNAL */(_Qr/* s2e1C */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_Qt/* s2e1J */){
      var _Qu/* s2e1O */ = hs_quotInt64/* EXTERNAL */(_Qq/* s2e1B */, _Qr/* s2e1C */);
      return E(_Qu/* s2e1O */);
    }else{
      var _Qv/* s2e1S */ = hs_eqInt64/* EXTERNAL */(_Qq/* s2e1B */, new Long/* EXTERNAL */(0, -2147483648));
      if(!_Qv/* s2e1S */){
        var _Qw/* s2e1X */ = hs_quotInt64/* EXTERNAL */(_Qq/* s2e1B */, _Qr/* s2e1C */);
        return E(_Qw/* s2e1X */);
      }else{
        return E(_PC/* GHC.Real.overflowError */);
      }
    }
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_Qx/* $fIntegralInt64_$cquot */ = function(_Qy/* s2e22 */, _Qz/* s2e23 */){
  return new F(function(){return _Qp/* GHC.Int.$w$cquot */(E(_Qy/* s2e22 */), E(_Qz/* s2e23 */));});
},
_QA/* $w$cquotRem */ = function(_QB/* s2dZI */, _QC/* s2dZJ */){
  var _QD/* s2dZL */ = hs_eqInt64/* EXTERNAL */(_QC/* s2dZJ */, new Long/* EXTERNAL */(0, 0));
  if(!_QD/* s2dZL */){
    var _QE/* s2dZQ */ = hs_eqInt64/* EXTERNAL */(_QC/* s2dZJ */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_QE/* s2dZQ */){
      return new T2(0,new T(function(){
        return hs_quotInt64/* EXTERNAL */(_QB/* s2dZI */, _QC/* s2dZJ */);
      }),new T(function(){
        return hs_remInt64/* EXTERNAL */(_QB/* s2dZI */, _QC/* s2dZJ */);
      }));
    }else{
      var _QF/* s2e05 */ = hs_eqInt64/* EXTERNAL */(_QB/* s2dZI */, new Long/* EXTERNAL */(0, -2147483648));
      return (!_QF/* s2e05 */) ? new T2(0,new T(function(){
        return hs_quotInt64/* EXTERNAL */(_QB/* s2dZI */, _QC/* s2dZJ */);
      }),new T(function(){
        return hs_remInt64/* EXTERNAL */(_QB/* s2dZI */, _QC/* s2dZJ */);
      })) : new T2(0,_PC/* GHC.Real.overflowError */,_PM/* GHC.Int.$fIntegralInt1 */);
    }
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_QG/* $fIntegralInt64_$cquotRem */ = function(_QH/* s2e0k */, _QI/* s2e0l */){
  var _QJ/* s2e0q */ = B(_QA/* GHC.Int.$w$cquotRem */(E(_QH/* s2e0k */), E(_QI/* s2e0l */)));
  return new T2(0,_QJ/* s2e0q */.a,_QJ/* s2e0q */.b);
},
_QK/* $w$crem */ = function(_QL/* s2e1d */, _QM/* s2e1e */){
  var _QN/* s2e1g */ = hs_eqInt64/* EXTERNAL */(_QM/* s2e1e */, new Long/* EXTERNAL */(0, 0));
  if(!_QN/* s2e1g */){
    var _QO/* s2e1l */ = hs_eqInt64/* EXTERNAL */(_QM/* s2e1e */, new Long/* EXTERNAL */(4294967295, -1));
    if(!_QO/* s2e1l */){
      var _QP/* s2e1q */ = hs_remInt64/* EXTERNAL */(_QL/* s2e1d */, _QM/* s2e1e */);
      return E(_QP/* s2e1q */);
    }else{
      return new F(function(){return new Long/* EXTERNAL */(0, 0);});
    }
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_QQ/* $fIntegralInt64_$crem */ = function(_QR/* s2e1u */, _QS/* s2e1v */){
  return new F(function(){return _QK/* GHC.Int.$w$crem */(E(_QR/* s2e1u */), E(_QS/* s2e1v */));});
},
_QT/* $fBitsInt64_$c/= */ = function(_QU/* s2dV3 */, _QV/* s2dV4 */){
  return new F(function(){return hs_neInt64/* EXTERNAL */(E(_QU/* s2dV3 */), E(_QV/* s2dV4 */));});
},
_QW/* $fEqInt64_$c== */ = function(_QX/* s2dVd */, _QY/* s2dVe */){
  return new F(function(){return hs_eqInt64/* EXTERNAL */(E(_QX/* s2dVd */), E(_QY/* s2dVe */));});
},
_QZ/* $fEqInt64 */ = new T2(0,_QW/* GHC.Int.$fEqInt64_$c== */,_QT/* GHC.Int.$fBitsInt64_$c/= */),
_R0/* $fOrdInt64_$c< */ = function(_R1/* s2dWd */, _R2/* s2dWe */){
  return new F(function(){return hs_ltInt64/* EXTERNAL */(E(_R1/* s2dWd */), E(_R2/* s2dWe */));});
},
_R3/* $fOrdInt64_$c<= */ = function(_R4/* s2dW3 */, _R5/* s2dW4 */){
  return new F(function(){return hs_leInt64/* EXTERNAL */(E(_R4/* s2dW3 */), E(_R5/* s2dW4 */));});
},
_R6/* $fOrdInt64_$c> */ = function(_R7/* s2dVT */, _R8/* s2dVU */){
  return new F(function(){return hs_gtInt64/* EXTERNAL */(E(_R7/* s2dVT */), E(_R8/* s2dVU */));});
},
_R9/* $fOrdInt64_$c>= */ = function(_Ra/* s2dVJ */, _Rb/* s2dVK */){
  return new F(function(){return hs_geInt64/* EXTERNAL */(E(_Ra/* s2dVJ */), E(_Rb/* s2dVK */));});
},
_Rc/* $w$ccompare */ = function(_Rd/* s2dWn */, _Re/* s2dWo */){
  var _Rf/* s2dWq */ = hs_eqInt64/* EXTERNAL */(_Rd/* s2dWn */, _Re/* s2dWo */);
  if(!_Rf/* s2dWq */){
    var _Rg/* s2dWv */ = hs_leInt64/* EXTERNAL */(_Rd/* s2dWn */, _Re/* s2dWo */);
    return (!_Rg/* s2dWv */) ? 2 : 0;
  }else{
    return 1;
  }
},
_Rh/* $fOrdInt64_$ccompare */ = function(_Ri/* s2dWz */, _Rj/* s2dWA */){
  return new F(function(){return _Rc/* GHC.Int.$w$ccompare */(E(_Ri/* s2dWz */), E(_Rj/* s2dWA */));});
},
_Rk/* $fOrdInt64_$cmax */ = function(_Rl/* s2dVy */, _Rm/* s2dVz */){
  var _Rn/* s2dVA */ = E(_Rl/* s2dVy */),
  _Ro/* s2dVC */ = E(_Rm/* s2dVz */),
  _Rp/* s2dVF */ = hs_leInt64/* EXTERNAL */(_Rn/* s2dVA */, _Ro/* s2dVC */);
  return (!_Rp/* s2dVF */) ? E(_Rn/* s2dVA */) : E(_Ro/* s2dVC */);
},
_Rq/* $fOrdInt64_$cmin */ = function(_Rr/* s2dVn */, _Rs/* s2dVo */){
  var _Rt/* s2dVp */ = E(_Rr/* s2dVn */),
  _Ru/* s2dVr */ = E(_Rs/* s2dVo */),
  _Rv/* s2dVu */ = hs_leInt64/* EXTERNAL */(_Rt/* s2dVp */, _Ru/* s2dVr */);
  return (!_Rv/* s2dVu */) ? E(_Ru/* s2dVr */) : E(_Rt/* s2dVp */);
},
_Rw/* $fOrdInt64 */ = {_:0,a:_QZ/* GHC.Int.$fEqInt64 */,b:_Rh/* GHC.Int.$fOrdInt64_$ccompare */,c:_R0/* GHC.Int.$fOrdInt64_$c< */,d:_R3/* GHC.Int.$fOrdInt64_$c<= */,e:_R6/* GHC.Int.$fOrdInt64_$c> */,f:_R9/* GHC.Int.$fOrdInt64_$c>= */,g:_Rk/* GHC.Int.$fOrdInt64_$cmax */,h:_Rq/* GHC.Int.$fOrdInt64_$cmin */},
_Rx/* $fRealInt1 */ = new T1(0,1),
_Ry/* eqInteger */ = function(_Rz/* s1H2 */, _RA/* s1H3 */){
  var _RB/* s1H4 */ = E(_Rz/* s1H2 */);
  if(!_RB/* s1H4 */._){
    var _RC/* s1H5 */ = _RB/* s1H4 */.a,
    _RD/* s1H6 */ = E(_RA/* s1H3 */);
    return (_RD/* s1H6 */._==0) ? _RC/* s1H5 */==_RD/* s1H6 */.a : (I_compareInt/* EXTERNAL */(_RD/* s1H6 */.a, _RC/* s1H5 */)==0) ? true : false;
  }else{
    var _RE/* s1Hc */ = _RB/* s1H4 */.a,
    _RF/* s1Hd */ = E(_RA/* s1H3 */);
    return (_RF/* s1Hd */._==0) ? (I_compareInt/* EXTERNAL */(_RE/* s1Hc */, _RF/* s1Hd */.a)==0) ? true : false : (I_compare/* EXTERNAL */(_RE/* s1Hc */, _RF/* s1Hd */.a)==0) ? true : false;
  }
},
_RG/* even1 */ = new T1(0,0),
_RH/* remInteger */ = function(_RI/* s1NY */, _RJ/* s1NZ */){
  while(1){
    var _RK/* s1O0 */ = E(_RI/* s1NY */);
    if(!_RK/* s1O0 */._){
      var _RL/* s1O2 */ = E(_RK/* s1O0 */.a);
      if(_RL/* s1O2 */==(-2147483648)){
        _RI/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _RM/* s1O3 */ = E(_RJ/* s1NZ */);
        if(!_RM/* s1O3 */._){
          return new T1(0,_RL/* s1O2 */%_RM/* s1O3 */.a);
        }else{
          _RI/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(_RL/* s1O2 */));
          _RJ/* s1NZ */ = _RM/* s1O3 */;
          continue;
        }
      }
    }else{
      var _RN/* s1Od */ = _RK/* s1O0 */.a,
      _RO/* s1Oe */ = E(_RJ/* s1NZ */);
      return (_RO/* s1Oe */._==0) ? new T1(1,I_rem/* EXTERNAL */(_RN/* s1Od */, I_fromInt/* EXTERNAL */(_RO/* s1Oe */.a))) : new T1(1,I_rem/* EXTERNAL */(_RN/* s1Od */, _RO/* s1Oe */.a));
    }
  }
},
_RP/* $fIntegralInteger_$crem */ = function(_RQ/* svus */, _RR/* svut */){
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_RR/* svut */, _RG/* GHC.Real.even1 */))){
    return new F(function(){return _RH/* GHC.Integer.Type.remInteger */(_RQ/* svus */, _RR/* svut */);});
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_RS/* $fEnumRatio_gcd' */ = function(_RT/* svuv */, _RU/* svuw */){
  while(1){
    if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_RU/* svuw */, _RG/* GHC.Real.even1 */))){
      var _RV/*  svuv */ = _RU/* svuw */,
      _RW/*  svuw */ = B(_RP/* GHC.Real.$fIntegralInteger_$crem */(_RT/* svuv */, _RU/* svuw */));
      _RT/* svuv */ = _RV/*  svuv */;
      _RU/* svuw */ = _RW/*  svuw */;
      continue;
    }else{
      return E(_RT/* svuv */);
    }
  }
},
_RX/* absInteger */ = function(_RY/* s1QP */){
  var _RZ/* s1QQ */ = E(_RY/* s1QP */);
  if(!_RZ/* s1QQ */._){
    var _S0/* s1QS */ = E(_RZ/* s1QQ */.a);
    return (_S0/* s1QS */==(-2147483648)) ? E(_Kv/* GHC.Integer.Type.lvl3 */) : (_S0/* s1QS */<0) ? new T1(0, -_S0/* s1QS */) : E(_RZ/* s1QQ */);
  }else{
    var _S1/* s1QW */ = _RZ/* s1QQ */.a;
    return (I_compareInt/* EXTERNAL */(_S1/* s1QW */, 0)>=0) ? E(_RZ/* s1QQ */) : new T1(1,I_negate/* EXTERNAL */(_S1/* s1QW */));
  }
},
_S2/* quotInteger */ = function(_S3/* s1On */, _S4/* s1Oo */){
  while(1){
    var _S5/* s1Op */ = E(_S3/* s1On */);
    if(!_S5/* s1Op */._){
      var _S6/* s1Or */ = E(_S5/* s1Op */.a);
      if(_S6/* s1Or */==(-2147483648)){
        _S3/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _S7/* s1Os */ = E(_S4/* s1Oo */);
        if(!_S7/* s1Os */._){
          return new T1(0,quot/* EXTERNAL */(_S6/* s1Or */, _S7/* s1Os */.a));
        }else{
          _S3/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(_S6/* s1Or */));
          _S4/* s1Oo */ = _S7/* s1Os */;
          continue;
        }
      }
    }else{
      var _S8/* s1OC */ = _S5/* s1Op */.a,
      _S9/* s1OD */ = E(_S4/* s1Oo */);
      return (_S9/* s1OD */._==0) ? new T1(0,I_toInt/* EXTERNAL */(I_quot/* EXTERNAL */(_S8/* s1OC */, I_fromInt/* EXTERNAL */(_S9/* s1OD */.a)))) : new T1(1,I_quot/* EXTERNAL */(_S8/* s1OC */, _S9/* s1OD */.a));
    }
  }
},
_Sa/* RatioZeroDenominator */ = 5,
_Sb/* ratioZeroDenomException */ = new T(function(){
  return B(_Pv/* GHC.Exception.$fExceptionArithException_$ctoException */(_Sa/* GHC.Exception.RatioZeroDenominator */));
}),
_Sc/* ratioZeroDenominatorError */ = new T(function(){
  return die/* EXTERNAL */(_Sb/* GHC.Exception.ratioZeroDenomException */);
}),
_Sd/* $w$sreduce */ = function(_Se/* svvD */, _Sf/* svvE */){
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_Sf/* svvE */, _RG/* GHC.Real.even1 */))){
    var _Sg/* svvG */ = B(_RS/* GHC.Real.$fEnumRatio_gcd' */(B(_RX/* GHC.Integer.Type.absInteger */(_Se/* svvD */)), B(_RX/* GHC.Integer.Type.absInteger */(_Sf/* svvE */))));
    return (!B(_Ry/* GHC.Integer.Type.eqInteger */(_Sg/* svvG */, _RG/* GHC.Real.even1 */))) ? new T2(0,B(_S2/* GHC.Integer.Type.quotInteger */(_Se/* svvD */, _Sg/* svvG */)),B(_S2/* GHC.Integer.Type.quotInteger */(_Sf/* svvE */, _Sg/* svvG */))) : E(_Pz/* GHC.Real.divZeroError */);
  }else{
    return E(_Sc/* GHC.Real.ratioZeroDenominatorError */);
  }
},
_Sh/* timesInteger */ = function(_Si/* s1PN */, _Sj/* s1PO */){
  while(1){
    var _Sk/* s1PP */ = E(_Si/* s1PN */);
    if(!_Sk/* s1PP */._){
      var _Sl/* s1PQ */ = _Sk/* s1PP */.a,
      _Sm/* s1PR */ = E(_Sj/* s1PO */);
      if(!_Sm/* s1PR */._){
        var _Sn/* s1PS */ = _Sm/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_Sl/* s1PQ */, _Sn/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_Sl/* s1PQ */, _Sn/* s1PS */)|0);
        }else{
          _Si/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Sl/* s1PQ */));
          _Sj/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Sn/* s1PS */));
          continue;
        }
      }else{
        _Si/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Sl/* s1PQ */));
        _Sj/* s1PO */ = _Sm/* s1PR */;
        continue;
      }
    }else{
      var _So/* s1Q6 */ = E(_Sj/* s1PO */);
      if(!_So/* s1Q6 */._){
        _Si/* s1PN */ = _Sk/* s1PP */;
        _Sj/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_So/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_Sk/* s1PP */.a, _So/* s1Q6 */.a));
      }
    }
  }
},
_Sp/* $fRealInt64_$ctoRational */ = function(_Sq/* s2e6O */){
  var _Sr/* s2e6T */ = B(_Sd/* GHC.Real.$w$sreduce */(B(_Sh/* GHC.Integer.Type.timesInteger */(B(_MO/* GHC.Integer.Type.int64ToInteger */(E(_Sq/* s2e6O */))), _Rx/* GHC.Int.$fRealInt1 */)), _Rx/* GHC.Int.$fRealInt1 */));
  return new T2(0,E(_Sr/* s2e6T */.a),E(_Sr/* s2e6T */.b));
},
_Ss/* $fRealInt64 */ = new T3(0,_K4/* GHC.Int.$fNumInt64 */,_Rw/* GHC.Int.$fOrdInt64 */,_Sp/* GHC.Int.$fRealInt64_$ctoRational */),
_Lr/* $fIntegralInt64 */ = new T(function(){
  return {_:0,a:_Ss/* GHC.Int.$fRealInt64 */,b:_OB/* GHC.Int.$fEnumInt64 */,c:_Qx/* GHC.Int.$fIntegralInt64_$cquot */,d:_QQ/* GHC.Int.$fIntegralInt64_$crem */,e:_PJ/* GHC.Int.$fIntegralInt64_$cdiv */,f:_Qm/* GHC.Int.$fIntegralInt64_$cmod */,g:_QG/* GHC.Int.$fIntegralInt64_$cquotRem */,h:_Qd/* GHC.Int.$fIntegralInt64_$cdivMod */,i:_MV/* GHC.Int.$fIntegralInt64_$ctoInteger */};
}),
_St/* $p1Ord */ = function(_Su/* scBR */){
  return E(E(_Su/* scBR */).a);
},
_Sv/* $p2Real */ = function(_Sw/* svfR */){
  return E(E(_Sw/* svfR */).b);
},
_Sx/* == */ = function(_Sy/* scBJ */){
  return E(E(_Sy/* scBJ */).a);
},
_Sz/* even2 */ = new T1(0,2),
_SA/* rem */ = function(_SB/* sveI */){
  return E(E(_SB/* sveI */).d);
},
_SC/* even */ = function(_SD/* svre */, _SE/* svrf */){
  var _SF/* svrg */ = B(_KZ/* GHC.Real.$p1Integral */(_SD/* svre */)),
  _SG/* svrh */ = new T(function(){
    return B(_L1/* GHC.Real.$p1Real */(_SF/* svrg */));
  }),
  _SH/* svrl */ = new T(function(){
    return B(A3(_SA/* GHC.Real.rem */,_SD/* svre */, _SE/* svrf */, new T(function(){
      return B(A2(_L3/* GHC.Num.fromInteger */,_SG/* svrh */, _Sz/* GHC.Real.even2 */));
    })));
  });
  return new F(function(){return A3(_Sx/* GHC.Classes.== */,B(_St/* GHC.Classes.$p1Ord */(B(_Sv/* GHC.Real.$p2Real */(_SF/* svrg */)))), _SH/* svrl */, new T(function(){
    return B(A2(_L3/* GHC.Num.fromInteger */,_SG/* svrh */, _RG/* GHC.Real.even1 */));
  }));});
},
_SI/* $wg1 */ = function(_SJ/*  sfnl */, _SK/*  sfnm */, _SL/*  sfnn */){
  while(1){
    var _SM/*  $wg1 */ = B((function(_SN/* sfnl */, _SO/* sfnm */, _SP/* sfnn */){
      if(!B(_SC/* GHC.Real.even */(_Lr/* GHC.Int.$fIntegralInt64 */, _SO/* sfnm */))){
        var _SQ/* sfnr */ = hs_eqInt64/* EXTERNAL */(_SO/* sfnm */, new Long/* EXTERNAL */(1, 0));
        if(!_SQ/* sfnr */){
          var _SR/* sfnw */ = hs_minusInt64/* EXTERNAL */(_SO/* sfnm */, new Long/* EXTERNAL */(1, 0));
          _SJ/*  sfnl */ = new T(function(){
            return B(_JH/* GHC.Int.$fNumInt64_$c* */(_SN/* sfnl */, _SN/* sfnl */));
          });
          _SK/*  sfnm */ = B(_Qp/* GHC.Int.$w$cquot */(_SR/* sfnw */, new Long/* EXTERNAL */(2, 0)));
          _SL/*  sfnn */ = new T(function(){
            return B(_JH/* GHC.Int.$fNumInt64_$c* */(_SN/* sfnl */, _SP/* sfnn */));
          },1);
          return __continue/* EXTERNAL */;
        }else{
          var _SS/* sfnH */ = hs_timesInt64/* EXTERNAL */(E(_SN/* sfnl */), E(_SP/* sfnn */));
          return E(_SS/* sfnH */);
        }
      }else{
        var _ST/*   sfnm */ = B(_Qp/* GHC.Int.$w$cquot */(_SO/* sfnm */, new Long/* EXTERNAL */(2, 0))),
        _SU/*   sfnn */ = _SP/* sfnn */;
        _SJ/*  sfnl */ = new T(function(){
          return B(_JH/* GHC.Int.$fNumInt64_$c* */(_SN/* sfnl */, _SN/* sfnl */));
        });
        _SK/*  sfnm */ = _ST/*   sfnm */;
        _SL/*  sfnn */ = _SU/*   sfnn */;
        return __continue/* EXTERNAL */;
      }
    })(_SJ/*  sfnl */, _SK/*  sfnm */, _SL/*  sfnn */));
    if(_SM/*  $wg1 */!=__continue/* EXTERNAL */){
      return _SM/*  $wg1 */;
    }
  }
},
_SV/* $wf1 */ = function(_SW/*  sfnM */, _SX/*  sfnN */){
  while(1){
    var _SY/*  $wf1 */ = B((function(_SZ/* sfnM */, _T0/* sfnN */){
      if(!B(_SC/* GHC.Real.even */(_Lr/* GHC.Int.$fIntegralInt64 */, _T0/* sfnN */))){
        var _T1/* sfnR */ = hs_eqInt64/* EXTERNAL */(_T0/* sfnN */, new Long/* EXTERNAL */(1, 0));
        if(!_T1/* sfnR */){
          var _T2/* sfnW */ = hs_minusInt64/* EXTERNAL */(_T0/* sfnN */, new Long/* EXTERNAL */(1, 0));
          return new F(function(){return _SI/* System.Random.$wg1 */(new T(function(){
            return B(_JH/* GHC.Int.$fNumInt64_$c* */(_SZ/* sfnM */, _SZ/* sfnM */));
          }), B(_Qp/* GHC.Int.$w$cquot */(_T2/* sfnW */, new Long/* EXTERNAL */(2, 0))), _SZ/* sfnM */);});
        }else{
          return E(_SZ/* sfnM */);
        }
      }else{
        var _T3/*   sfnN */ = B(_Qp/* GHC.Int.$w$cquot */(_T0/* sfnN */, new Long/* EXTERNAL */(2, 0)));
        _SW/*  sfnM */ = new T(function(){
          return B(_JH/* GHC.Int.$fNumInt64_$c* */(_SZ/* sfnM */, _SZ/* sfnM */));
        });
        _SX/*  sfnN */ = _T3/*   sfnN */;
        return __continue/* EXTERNAL */;
      }
    })(_SW/*  sfnM */, _SX/*  sfnN */));
    if(_SY/*  $wf1 */!=__continue/* EXTERNAL */){
      return _SY/*  $wf1 */;
    }
  }
},
_T4/* $w$s^ */ = function(_T5/* sfoq */, _T6/* sfor */){
  var _T7/* sfot */ = hs_ltInt64/* EXTERNAL */(_T6/* sfor */, new Long/* EXTERNAL */(0, 0));
  if(!_T7/* sfot */){
    var _T8/* sfoy */ = hs_eqInt64/* EXTERNAL */(_T6/* sfor */, new Long/* EXTERNAL */(0, 0));
    if(!_T8/* sfoy */){
      return new F(function(){return _SV/* System.Random.$wf1 */(_T5/* sfoq */, _T6/* sfor */);});
    }else{
      return E(_KU/* System.Random.$fRandomDouble6 */);
    }
  }else{
    return E(_KT/* System.Random.$fRandomDouble5 */);
  }
},
_T9/* $fRandomDouble_twoto53 */ = new T(function(){
  return B(_T4/* System.Random.$w$s^ */(_KR/* System.Random.$fRandomDouble4 */, new Long/* EXTERNAL */(53, 0)));
}),
_Ta/* doubleFromInteger */ = function(_Tb/* s1M0 */){
  var _Tc/* s1M1 */ = E(_Tb/* s1M0 */);
  if(!_Tc/* s1M1 */._){
    return _Tc/* s1M1 */.a;
  }else{
    return new F(function(){return I_toNumber/* EXTERNAL */(_Tc/* s1M1 */.a);});
  }
},
_Td/* $fRandomDouble3 */ = new T(function(){
  return B(_Ta/* GHC.Integer.Type.doubleFromInteger */(B(_MO/* GHC.Integer.Type.int64ToInteger */(E(_T9/* System.Random.$fRandomDouble_twoto53 */)))));
}),
_Te/* $fRandomDouble7 */ = new T(function(){
  return hs_minusInt64/* EXTERNAL */(E(_T9/* System.Random.$fRandomDouble_twoto53 */), new Long/* EXTERNAL */(1, 0));
}),
_Tf/* $w$c.&. */ = function(_Tg/* s2e5n */, _Th/* s2e5o */){
  var _Ti/* s2e5q */ = hs_int64ToWord64/* EXTERNAL */(_Th/* s2e5o */),
  _Tj/* s2e5u */ = hs_int64ToWord64/* EXTERNAL */(_Tg/* s2e5n */),
  _Tk/* s2e5y */ = hs_and64/* EXTERNAL */(_Tj/* s2e5u */, _Ti/* s2e5q */),
  _Tl/* s2e5C */ = hs_word64ToInt64/* EXTERNAL */(_Tk/* s2e5y */);
  return E(_Tl/* s2e5C */);
},
_Tm/* $fRandomBool3 */ = new T1(0,1),
_Tn/* $WStdGen */ = function(_To/* sfmR */, _Tp/* sfmS */){
  return new T2(0,E(_To/* sfmR */),E(_Tp/* sfmS */));
},
_Tq/* $w$cnext */ = function(_Tr/* sfqJ */, _Ts/* sfqK */){
  var _Tt/* sfqL */ = quot/* EXTERNAL */(_Ts/* sfqK */, 52774),
  _Tu/* sfqM */ = (imul/* EXTERNAL */(40692, _Ts/* sfqK */-(imul/* EXTERNAL */(_Tt/* sfqL */, 52774)|0)|0)|0)-(imul/* EXTERNAL */(_Tt/* sfqL */, 3791)|0)|0,
  _Tv/* sfqR */ = new T(function(){
    if(_Tu/* sfqM */>=0){
      return _Tu/* sfqM */;
    }else{
      return _Tu/* sfqM */+2147483399|0;
    }
  }),
  _Tw/* sfqV */ = quot/* EXTERNAL */(_Tr/* sfqJ */, 53668),
  _Tx/* sfqW */ = (imul/* EXTERNAL */(40014, _Tr/* sfqJ */-(imul/* EXTERNAL */(_Tw/* sfqV */, 53668)|0)|0)|0)-(imul/* EXTERNAL */(_Tw/* sfqV */, 12211)|0)|0,
  _Ty/* sfr1 */ = new T(function(){
    if(_Tx/* sfqW */>=0){
      return _Tx/* sfqW */;
    }else{
      return _Tx/* sfqW */+2147483563|0;
    }
  });
  return new T2(0,new T(function(){
    var _Tz/* sfr9 */ = E(_Ty/* sfr1 */)-E(_Tv/* sfqR */)|0;
    if(_Tz/* sfr9 */>=1){
      return _Tz/* sfr9 */;
    }else{
      return _Tz/* sfr9 */+2147483562|0;
    }
  }),new T(function(){
    return B(_Tn/* System.Random.$WStdGen */(_Ty/* sfr1 */, _Tv/* sfqR */));
  }));
},
_TA/* b */ = new T1(0,2147483562),
_TB/* getStdRandom4 */ = new T1(0,0),
_TC/* lvl5 */ = new T1(0,1000),
_TD/* modInt# */ = function(_TE/* scEd */, _TF/* scEe */){
  var _TG/* scEf */ = _TE/* scEd */%_TF/* scEe */;
  if(_TE/* scEd */<=0){
    if(_TE/* scEd */>=0){
      return E(_TG/* scEf */);
    }else{
      if(_TF/* scEe */<=0){
        return E(_TG/* scEf */);
      }else{
        var _TH/* scEm */ = E(_TG/* scEf */);
        return (_TH/* scEm */==0) ? 0 : _TH/* scEm */+_TF/* scEe */|0;
      }
    }
  }else{
    if(_TF/* scEe */>=0){
      if(_TE/* scEd */>=0){
        return E(_TG/* scEf */);
      }else{
        if(_TF/* scEe */<=0){
          return E(_TG/* scEf */);
        }else{
          var _TI/* scEt */ = E(_TG/* scEf */);
          return (_TI/* scEt */==0) ? 0 : _TI/* scEt */+_TF/* scEe */|0;
        }
      }
    }else{
      var _TJ/* scEu */ = E(_TG/* scEf */);
      return (_TJ/* scEu */==0) ? 0 : _TJ/* scEu */+_TF/* scEe */|0;
    }
  }
},
_TK/* modInteger */ = function(_TL/* s1Na */, _TM/* s1Nb */){
  while(1){
    var _TN/* s1Nc */ = E(_TL/* s1Na */);
    if(!_TN/* s1Nc */._){
      var _TO/* s1Ne */ = E(_TN/* s1Nc */.a);
      if(_TO/* s1Ne */==(-2147483648)){
        _TL/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _TP/* s1Nf */ = E(_TM/* s1Nb */);
        if(!_TP/* s1Nf */._){
          return new T1(0,B(_TD/* GHC.Classes.modInt# */(_TO/* s1Ne */, _TP/* s1Nf */.a)));
        }else{
          _TL/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(_TO/* s1Ne */));
          _TM/* s1Nb */ = _TP/* s1Nf */;
          continue;
        }
      }
    }else{
      var _TQ/* s1Np */ = _TN/* s1Nc */.a,
      _TR/* s1Nq */ = E(_TM/* s1Nb */);
      return (_TR/* s1Nq */._==0) ? new T1(1,I_mod/* EXTERNAL */(_TQ/* s1Np */, I_fromInt/* EXTERNAL */(_TR/* s1Nq */.a))) : new T1(1,I_mod/* EXTERNAL */(_TQ/* s1Np */, _TR/* s1Nq */.a));
    }
  }
},
_TS/* $w$srandomIvalInteger */ = function(_TT/*  sfs7 */, _TU/*  sfs8 */, _TV/*  sfs9 */, _TW/*  sfsa */){
  while(1){
    var _TX/*  $w$srandomIvalInteger */ = B((function(_TY/* sfs7 */, _TZ/* sfs8 */, _U0/* sfs9 */, _U1/* sfsa */){
      if(!B(_L5/* GHC.Integer.Type.gtInteger */(_TZ/* sfs8 */, _U0/* sfs9 */))){
        var _U2/* sfsc */ = B(_Km/* GHC.Integer.Type.plusInteger */(B(_M1/* GHC.Integer.Type.minusInteger */(_U0/* sfs9 */, _TZ/* sfs8 */)), _Tm/* System.Random.$fRandomBool3 */)),
        _U3/* sfsf */ = function(_U4/* sfsg */, _U5/* sfsh */, _U6/* sfsi */){
          while(1){
            if(!B(_Lt/* GHC.Integer.Type.geInteger */(_U4/* sfsg */, B(_Sh/* GHC.Integer.Type.timesInteger */(_U2/* sfsc */, _TC/* System.Random.lvl5 */))))){
              var _U7/* sfsk */ = E(_U6/* sfsi */),
              _U8/* sfsn */ = B(_Tq/* System.Random.$w$cnext */(_U7/* sfsk */.a, _U7/* sfsk */.b)),
              _U9/*  sfsg */ = B(_Sh/* GHC.Integer.Type.timesInteger */(_U4/* sfsg */, _TA/* System.Random.b */)),
              _Ua/*  sfsh */ = B(_Km/* GHC.Integer.Type.plusInteger */(B(_Sh/* GHC.Integer.Type.timesInteger */(_U5/* sfsh */, _TA/* System.Random.b */)), B(_M1/* GHC.Integer.Type.minusInteger */(B(_MM/* GHC.Integer.Type.smallInteger */(E(_U8/* sfsn */.a))), _Tm/* System.Random.$fRandomBool3 */))));
              _U4/* sfsg */ = _U9/*  sfsg */;
              _U5/* sfsh */ = _Ua/*  sfsh */;
              _U6/* sfsi */ = _U8/* sfsn */.b;
              continue;
            }else{
              return new T2(0,_U5/* sfsh */,_U6/* sfsi */);
            }
          }
        },
        _Ub/* sfsx */ = B(_U3/* sfsf */(_Tm/* System.Random.$fRandomBool3 */, _TB/* System.Random.getStdRandom4 */, _U1/* sfsa */)),
        _Uc/* sfsE */ = new T(function(){
          return B(A2(_L3/* GHC.Num.fromInteger */,_TY/* sfs7 */, new T(function(){
            if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_U2/* sfsc */, _TB/* System.Random.getStdRandom4 */))){
              return B(_Km/* GHC.Integer.Type.plusInteger */(_TZ/* sfs8 */, B(_TK/* GHC.Integer.Type.modInteger */(_Ub/* sfsx */.a, _U2/* sfsc */))));
            }else{
              return E(_Pz/* GHC.Real.divZeroError */);
            }
          })));
        });
        return new T2(0,_Uc/* sfsE */,_Ub/* sfsx */.b);
      }else{
        var _Ud/*   sfs7 */ = _TY/* sfs7 */,
        _Ue/*   sfs8 */ = _U0/* sfs9 */,
        _Uf/*   sfs9 */ = _TZ/* sfs8 */,
        _Ug/*   sfsa */ = _U1/* sfsa */;
        _TT/*  sfs7 */ = _Ud/*   sfs7 */;
        _TU/*  sfs8 */ = _Ue/*   sfs8 */;
        _TV/*  sfs9 */ = _Uf/*   sfs9 */;
        _TW/*  sfsa */ = _Ug/*   sfsa */;
        return __continue/* EXTERNAL */;
      }
    })(_TT/*  sfs7 */, _TU/*  sfs8 */, _TV/*  sfs9 */, _TW/*  sfsa */));
    if(_TX/*  $w$srandomIvalInteger */!=__continue/* EXTERNAL */){
      return _TX/*  $w$srandomIvalInteger */;
    }
  }
},
_Uh/* $w$s$crandom */ = function(_Ui/* sfSt */){
  var _Uj/* sfSu */ = B(_TS/* System.Random.$w$srandomIvalInteger */(_K4/* GHC.Int.$fNumInt64 */, _KQ/* System.Random.$fRandomCLLong4 */, _KJ/* System.Random.$fRandomCLLong3 */, _Ui/* sfSt */));
  return new T2(0,new T(function(){
    return B(_Ta/* GHC.Integer.Type.doubleFromInteger */(B(_MO/* GHC.Integer.Type.int64ToInteger */(B(_Tf/* GHC.Int.$w$c.&. */(E(_Te/* System.Random.$fRandomDouble7 */), E(_Uj/* sfSu */.a)))))))/E(_Td/* System.Random.$fRandomDouble3 */);
  }),_Uj/* sfSu */.b);
},
_Uk/* $w$srandomRFloating2 */ = function(_Ul/*  sfSX */, _Um/*  sfSY */, _Un/*  sfSZ */){
  while(1){
    var _Uo/*  $w$srandomRFloating2 */ = B((function(_Up/* sfSX */, _Uq/* sfSY */, _Ur/* sfSZ */){
      if(_Up/* sfSX */<=_Uq/* sfSY */){
        var _Us/* sfT2 */ = new T(function(){
          var _Ut/* sfT3 */ = B(_Uh/* System.Random.$w$s$crandom */(_Ur/* sfSZ */));
          return new T2(0,_Ut/* sfT3 */.a,_Ut/* sfT3 */.b);
        });
        return new T2(0,new T(function(){
          var _Uu/* sfT9 */ = E(E(_Us/* sfT2 */).a);
          return 0.5*_Up/* sfSX */+_Uu/* sfT9 */*(0.5*_Uq/* sfSY */-0.5*_Up/* sfSX */)+0.5*_Up/* sfSX */+_Uu/* sfT9 */*(0.5*_Uq/* sfSY */-0.5*_Up/* sfSX */);
        }),new T(function(){
          return E(E(_Us/* sfT2 */).b);
        }));
      }else{
        var _Uv/*   sfSX */ = _Uq/* sfSY */,
        _Uw/*   sfSY */ = _Up/* sfSX */,
        _Ux/*   sfSZ */ = _Ur/* sfSZ */;
        _Ul/*  sfSX */ = _Uv/*   sfSX */;
        _Um/*  sfSY */ = _Uw/*   sfSY */;
        _Un/*  sfSZ */ = _Ux/*   sfSZ */;
        return __continue/* EXTERNAL */;
      }
    })(_Ul/*  sfSX */, _Um/*  sfSY */, _Un/*  sfSZ */));
    if(_Uo/*  $w$srandomRFloating2 */!=__continue/* EXTERNAL */){
      return _Uo/*  $w$srandomRFloating2 */;
    }
  }
},
_Uy/* s6SwZ */ = 1420103680,
_Uz/* s6Sx0 */ = 465,
_UA/* s6Sx1 */ = new T2(1,_Uz/* s6Sx0 */,_6/* GHC.Types.[] */),
_UB/* s6Sx2 */ = new T2(1,_Uy/* s6SwZ */,_UA/* s6Sx1 */),
_UC/* $fHasResolutionE5 */ = new T(function(){
  return B(_KA/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _UB/* s6Sx2 */));
}),
_UD/* $fBitsInt4 */ = 0,
_UE/* $w$cdivMod1 */ = function(_UF/* s2dPw */, _UG/* s2dPx */){
  var _UH/* s2dPy */ = E(_UG/* s2dPx */);
  if(!_UH/* s2dPy */){
    return E(_Pz/* GHC.Real.divZeroError */);
  }else{
    var _UI/* s2dPz */ = function(_UJ/* s2dPA */){
      if(_UF/* s2dPw */<=0){
        if(_UF/* s2dPw */>=0){
          var _UK/* s2dPF */ = quotRemI/* EXTERNAL */(_UF/* s2dPw */, _UH/* s2dPy */);
          return new T2(0,_UK/* s2dPF */.a,_UK/* s2dPF */.b);
        }else{
          if(_UH/* s2dPy */<=0){
            var _UL/* s2dPM */ = quotRemI/* EXTERNAL */(_UF/* s2dPw */, _UH/* s2dPy */);
            return new T2(0,_UL/* s2dPM */.a,_UL/* s2dPM */.b);
          }else{
            var _UM/* s2dPS */ = quotRemI/* EXTERNAL */(_UF/* s2dPw */+1|0, _UH/* s2dPy */);
            return new T2(0,_UM/* s2dPS */.a-1|0,(_UM/* s2dPS */.b+_UH/* s2dPy */|0)-1|0);
          }
        }
      }else{
        if(_UH/* s2dPy */>=0){
          if(_UF/* s2dPw */>=0){
            var _UN/* s2dQ4 */ = quotRemI/* EXTERNAL */(_UF/* s2dPw */, _UH/* s2dPy */);
            return new T2(0,_UN/* s2dQ4 */.a,_UN/* s2dQ4 */.b);
          }else{
            if(_UH/* s2dPy */<=0){
              var _UO/* s2dQb */ = quotRemI/* EXTERNAL */(_UF/* s2dPw */, _UH/* s2dPy */);
              return new T2(0,_UO/* s2dQb */.a,_UO/* s2dQb */.b);
            }else{
              var _UP/* s2dQh */ = quotRemI/* EXTERNAL */(_UF/* s2dPw */+1|0, _UH/* s2dPy */);
              return new T2(0,_UP/* s2dQh */.a-1|0,(_UP/* s2dQh */.b+_UH/* s2dPy */|0)-1|0);
            }
          }
        }else{
          var _UQ/* s2dQq */ = quotRemI/* EXTERNAL */(_UF/* s2dPw */-1|0, _UH/* s2dPy */);
          return new T2(0,_UQ/* s2dQq */.a-1|0,(_UQ/* s2dQq */.b+_UH/* s2dPy */|0)+1|0);
        }
      }
    };
    if(E(_UH/* s2dPy */)==(-1)){
      if(E(_UF/* s2dPw */)==(-2147483648)){
        return new T2(0,_PC/* GHC.Real.overflowError */,_UD/* GHC.Int.$fBitsInt4 */);
      }else{
        return new F(function(){return _UI/* s2dPz */(_/* EXTERNAL */);});
      }
    }else{
      return new F(function(){return _UI/* s2dPz */(_/* EXTERNAL */);});
    }
  }
},
_UR/* lvl1 */ = new T1(0,-1),
_US/* signumInteger */ = function(_UT/* s1OO */){
  var _UU/* s1OP */ = E(_UT/* s1OO */);
  if(!_UU/* s1OP */._){
    var _UV/* s1OQ */ = _UU/* s1OP */.a;
    return (_UV/* s1OQ */>=0) ? (E(_UV/* s1OQ */)==0) ? E(_K5/* GHC.Integer.Type.lvl */) : E(_Kk/* GHC.Integer.Type.log2I1 */) : E(_UR/* GHC.Integer.Type.lvl1 */);
  }else{
    var _UW/* s1OW */ = I_compareInt/* EXTERNAL */(_UU/* s1OP */.a, 0);
    return (_UW/* s1OW */<=0) ? (E(_UW/* s1OW */)==0) ? E(_K5/* GHC.Integer.Type.lvl */) : E(_UR/* GHC.Integer.Type.lvl1 */) : E(_Kk/* GHC.Integer.Type.log2I1 */);
  }
},
_UX/* $w$s$c/ */ = function(_UY/* svwb */, _UZ/* svwc */, _V0/* svwd */, _V1/* svwe */){
  var _V2/* svwf */ = B(_Sh/* GHC.Integer.Type.timesInteger */(_UZ/* svwc */, _V0/* svwd */));
  return new F(function(){return _Sd/* GHC.Real.$w$sreduce */(B(_Sh/* GHC.Integer.Type.timesInteger */(B(_Sh/* GHC.Integer.Type.timesInteger */(_UY/* svwb */, _V1/* svwe */)), B(_US/* GHC.Integer.Type.signumInteger */(_V2/* svwf */)))), B(_RX/* GHC.Integer.Type.absInteger */(_V2/* svwf */)));});
},
_V3/* $fHasResolutionE12_$cresolution */ = function(_V4/* s6Sx3 */){
  return E(_UC/* Data.Fixed.$fHasResolutionE5 */);
},
_V5/* $fEnumInteger2 */ = new T1(0,1),
_V6/* $wenumDeltaInteger */ = function(_V7/* smJm */, _V8/* smJn */){
  var _V9/* smJo */ = E(_V7/* smJm */);
  return new T2(0,_V9/* smJo */,new T(function(){
    var _Va/* smJq */ = B(_V6/* GHC.Enum.$wenumDeltaInteger */(B(_Km/* GHC.Integer.Type.plusInteger */(_V9/* smJo */, _V8/* smJn */)), _V8/* smJn */));
    return new T2(1,_Va/* smJq */.a,_Va/* smJq */.b);
  }));
},
_Vb/* $fEnumInteger_$cenumFrom */ = function(_Vc/* smJF */){
  var _Vd/* smJG */ = B(_V6/* GHC.Enum.$wenumDeltaInteger */(_Vc/* smJF */, _V5/* GHC.Enum.$fEnumInteger2 */));
  return new T2(1,_Vd/* smJG */.a,_Vd/* smJG */.b);
},
_Ve/* $fEnumInteger_$cenumFromThen */ = function(_Vf/* smJJ */, _Vg/* smJK */){
  var _Vh/* smJM */ = B(_V6/* GHC.Enum.$wenumDeltaInteger */(_Vf/* smJJ */, new T(function(){
    return B(_M1/* GHC.Integer.Type.minusInteger */(_Vg/* smJK */, _Vf/* smJJ */));
  })));
  return new T2(1,_Vh/* smJM */.a,_Vh/* smJM */.b);
},
_Vi/* enumDeltaToInteger */ = function(_Vj/* smJP */, _Vk/* smJQ */, _Vl/* smJR */){
  if(!B(_Lt/* GHC.Integer.Type.geInteger */(_Vk/* smJQ */, _Ls/* GHC.Enum.$fEnumInteger1 */))){
    var _Vm/* smJT */ = function(_Vn/* smJU */){
      return (!B(_LB/* GHC.Integer.Type.ltInteger */(_Vn/* smJU */, _Vl/* smJR */))) ? new T2(1,_Vn/* smJU */,new T(function(){
        return B(_Vm/* smJT */(B(_Km/* GHC.Integer.Type.plusInteger */(_Vn/* smJU */, _Vk/* smJQ */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _Vm/* smJT */(_Vj/* smJP */);});
  }else{
    var _Vo/* smJY */ = function(_Vp/* smJZ */){
      return (!B(_L5/* GHC.Integer.Type.gtInteger */(_Vp/* smJZ */, _Vl/* smJR */))) ? new T2(1,_Vp/* smJZ */,new T(function(){
        return B(_Vo/* smJY */(B(_Km/* GHC.Integer.Type.plusInteger */(_Vp/* smJZ */, _Vk/* smJQ */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _Vo/* smJY */(_Vj/* smJP */);});
  }
},
_Vq/* $fEnumInteger_$cenumFromThenTo */ = function(_Vr/* smKg */, _Vs/* smKh */, _Vt/* smKi */){
  return new F(function(){return _Vi/* GHC.Enum.enumDeltaToInteger */(_Vr/* smKg */, B(_M1/* GHC.Integer.Type.minusInteger */(_Vs/* smKh */, _Vr/* smKg */)), _Vt/* smKi */);});
},
_Vu/* $fEnumInteger_$cenumFromTo */ = function(_Vv/* smKe */, _Vw/* smKf */){
  return new F(function(){return _Vi/* GHC.Enum.enumDeltaToInteger */(_Vv/* smKe */, _V5/* GHC.Enum.$fEnumInteger2 */, _Vw/* smKf */);});
},
_Vx/* integerToInt */ = function(_Vy/* s1Rv */){
  var _Vz/* s1Rw */ = E(_Vy/* s1Rv */);
  if(!_Vz/* s1Rw */._){
    return E(_Vz/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_Vz/* s1Rw */.a);});
  }
},
_VA/* $fEnumInteger_$cfromEnum */ = function(_VB/* smJf */){
  return new F(function(){return _Vx/* GHC.Integer.Type.integerToInt */(_VB/* smJf */);});
},
_VC/* $fEnumInteger_$cpred */ = function(_VD/* smJl */){
  return new F(function(){return _M1/* GHC.Integer.Type.minusInteger */(_VD/* smJl */, _V5/* GHC.Enum.$fEnumInteger2 */);});
},
_VE/* $fEnumInteger_$csucc */ = function(_VF/* smJk */){
  return new F(function(){return _Km/* GHC.Integer.Type.plusInteger */(_VF/* smJk */, _V5/* GHC.Enum.$fEnumInteger2 */);});
},
_VG/* $fEnumInteger_$ctoEnum */ = function(_VH/* smJh */){
  return new F(function(){return _MM/* GHC.Integer.Type.smallInteger */(E(_VH/* smJh */));});
},
_VI/* $fEnumInteger */ = {_:0,a:_VE/* GHC.Enum.$fEnumInteger_$csucc */,b:_VC/* GHC.Enum.$fEnumInteger_$cpred */,c:_VG/* GHC.Enum.$fEnumInteger_$ctoEnum */,d:_VA/* GHC.Enum.$fEnumInteger_$cfromEnum */,e:_Vb/* GHC.Enum.$fEnumInteger_$cenumFrom */,f:_Ve/* GHC.Enum.$fEnumInteger_$cenumFromThen */,g:_Vu/* GHC.Enum.$fEnumInteger_$cenumFromTo */,h:_Vq/* GHC.Enum.$fEnumInteger_$cenumFromThenTo */},
_VJ/* divInt# */ = function(_VK/* scDT */, _VL/* scDU */){
  if(_VK/* scDT */<=0){
    if(_VK/* scDT */>=0){
      return new F(function(){return quot/* EXTERNAL */(_VK/* scDT */, _VL/* scDU */);});
    }else{
      if(_VL/* scDU */<=0){
        return new F(function(){return quot/* EXTERNAL */(_VK/* scDT */, _VL/* scDU */);});
      }else{
        return quot/* EXTERNAL */(_VK/* scDT */+1|0, _VL/* scDU */)-1|0;
      }
    }
  }else{
    if(_VL/* scDU */>=0){
      if(_VK/* scDT */>=0){
        return new F(function(){return quot/* EXTERNAL */(_VK/* scDT */, _VL/* scDU */);});
      }else{
        if(_VL/* scDU */<=0){
          return new F(function(){return quot/* EXTERNAL */(_VK/* scDT */, _VL/* scDU */);});
        }else{
          return quot/* EXTERNAL */(_VK/* scDT */+1|0, _VL/* scDU */)-1|0;
        }
      }
    }else{
      return quot/* EXTERNAL */(_VK/* scDT */-1|0, _VL/* scDU */)-1|0;
    }
  }
},
_VM/* divInteger */ = function(_VN/* s1Nz */, _VO/* s1NA */){
  while(1){
    var _VP/* s1NB */ = E(_VN/* s1Nz */);
    if(!_VP/* s1NB */._){
      var _VQ/* s1ND */ = E(_VP/* s1NB */.a);
      if(_VQ/* s1ND */==(-2147483648)){
        _VN/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _VR/* s1NE */ = E(_VO/* s1NA */);
        if(!_VR/* s1NE */._){
          return new T1(0,B(_VJ/* GHC.Classes.divInt# */(_VQ/* s1ND */, _VR/* s1NE */.a)));
        }else{
          _VN/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(_VQ/* s1ND */));
          _VO/* s1NA */ = _VR/* s1NE */;
          continue;
        }
      }
    }else{
      var _VS/* s1NO */ = _VP/* s1NB */.a,
      _VT/* s1NP */ = E(_VO/* s1NA */);
      return (_VT/* s1NP */._==0) ? new T1(1,I_div/* EXTERNAL */(_VS/* s1NO */, I_fromInt/* EXTERNAL */(_VT/* s1NP */.a))) : new T1(1,I_div/* EXTERNAL */(_VS/* s1NO */, _VT/* s1NP */.a));
    }
  }
},
_VU/* $fIntegralInteger_$cdiv */ = function(_VV/* svup */, _VW/* svuq */){
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_VW/* svuq */, _RG/* GHC.Real.even1 */))){
    return new F(function(){return _VM/* GHC.Integer.Type.divInteger */(_VV/* svup */, _VW/* svuq */);});
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_VX/* divModInteger */ = function(_VY/* s1MF */, _VZ/* s1MG */){
  while(1){
    var _W0/* s1MH */ = E(_VY/* s1MF */);
    if(!_W0/* s1MH */._){
      var _W1/* s1MJ */ = E(_W0/* s1MH */.a);
      if(_W1/* s1MJ */==(-2147483648)){
        _VY/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _W2/* s1MK */ = E(_VZ/* s1MG */);
        if(!_W2/* s1MK */._){
          var _W3/* s1ML */ = _W2/* s1MK */.a;
          return new T2(0,new T1(0,B(_VJ/* GHC.Classes.divInt# */(_W1/* s1MJ */, _W3/* s1ML */))),new T1(0,B(_TD/* GHC.Classes.modInt# */(_W1/* s1MJ */, _W3/* s1ML */))));
        }else{
          _VY/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(_W1/* s1MJ */));
          _VZ/* s1MG */ = _W2/* s1MK */;
          continue;
        }
      }
    }else{
      var _W4/* s1MY */ = E(_VZ/* s1MG */);
      if(!_W4/* s1MY */._){
        _VY/* s1MF */ = _W0/* s1MH */;
        _VZ/* s1MG */ = new T1(1,I_fromInt/* EXTERNAL */(_W4/* s1MY */.a));
        continue;
      }else{
        var _W5/* s1N5 */ = I_divMod/* EXTERNAL */(_W0/* s1MH */.a, _W4/* s1MY */.a);
        return new T2(0,new T1(1,_W5/* s1N5 */.a),new T1(1,_W5/* s1N5 */.b));
      }
    }
  }
},
_W6/* $fIntegralInteger_$cdivMod */ = function(_W7/* svua */, _W8/* svub */){
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_W8/* svub */, _RG/* GHC.Real.even1 */))){
    var _W9/* svud */ = B(_VX/* GHC.Integer.Type.divModInteger */(_W7/* svua */, _W8/* svub */));
    return new T2(0,_W9/* svud */.a,_W9/* svud */.b);
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_Wa/* $fIntegralInteger_$cmod */ = function(_Wb/* svum */, _Wc/* svun */){
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_Wc/* svun */, _RG/* GHC.Real.even1 */))){
    return new F(function(){return _TK/* GHC.Integer.Type.modInteger */(_Wb/* svum */, _Wc/* svun */);});
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_Wd/* $fIntegralInteger_$cquot */ = function(_We/* svvA */, _Wf/* svvB */){
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_Wf/* svvB */, _RG/* GHC.Real.even1 */))){
    return new F(function(){return _S2/* GHC.Integer.Type.quotInteger */(_We/* svvA */, _Wf/* svvB */);});
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_Wg/* quotRemInteger */ = function(_Wh/* s1Ma */, _Wi/* s1Mb */){
  while(1){
    var _Wj/* s1Mc */ = E(_Wh/* s1Ma */);
    if(!_Wj/* s1Mc */._){
      var _Wk/* s1Me */ = E(_Wj/* s1Mc */.a);
      if(_Wk/* s1Me */==(-2147483648)){
        _Wh/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _Wl/* s1Mf */ = E(_Wi/* s1Mb */);
        if(!_Wl/* s1Mf */._){
          var _Wm/* s1Mg */ = _Wl/* s1Mf */.a;
          return new T2(0,new T1(0,quot/* EXTERNAL */(_Wk/* s1Me */, _Wm/* s1Mg */)),new T1(0,_Wk/* s1Me */%_Wm/* s1Mg */));
        }else{
          _Wh/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(_Wk/* s1Me */));
          _Wi/* s1Mb */ = _Wl/* s1Mf */;
          continue;
        }
      }
    }else{
      var _Wn/* s1Mt */ = E(_Wi/* s1Mb */);
      if(!_Wn/* s1Mt */._){
        _Wh/* s1Ma */ = _Wj/* s1Mc */;
        _Wi/* s1Mb */ = new T1(1,I_fromInt/* EXTERNAL */(_Wn/* s1Mt */.a));
        continue;
      }else{
        var _Wo/* s1MA */ = I_quotRem/* EXTERNAL */(_Wj/* s1Mc */.a, _Wn/* s1Mt */.a);
        return new T2(0,new T1(1,_Wo/* s1MA */.a),new T1(1,_Wo/* s1MA */.b));
      }
    }
  }
},
_Wp/* $fIntegralInteger_$cquotRem */ = function(_Wq/* svug */, _Wr/* svuh */){
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_Wr/* svuh */, _RG/* GHC.Real.even1 */))){
    var _Ws/* svuj */ = B(_Wg/* GHC.Integer.Type.quotRemInteger */(_Wq/* svug */, _Wr/* svuh */));
    return new T2(0,_Ws/* svuj */.a,_Ws/* svuj */.b);
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_Wt/* $fIntegralInteger_$ctoInteger */ = function(_Wu/* svu9 */){
  return E(_Wu/* svu9 */);
},
_Wv/* $fNumInteger_$cfromInteger */ = function(_Ww/* s6HU */){
  return E(_Ww/* s6HU */);
},
_Wx/* $fNumInteger */ = {_:0,a:_Km/* GHC.Integer.Type.plusInteger */,b:_M1/* GHC.Integer.Type.minusInteger */,c:_Sh/* GHC.Integer.Type.timesInteger */,d:_Kw/* GHC.Integer.Type.negateInteger */,e:_RX/* GHC.Integer.Type.absInteger */,f:_US/* GHC.Integer.Type.signumInteger */,g:_Wv/* GHC.Num.$fNumInteger_$cfromInteger */},
_Wy/* neqInteger */ = function(_Wz/* s1GK */, _WA/* s1GL */){
  var _WB/* s1GM */ = E(_Wz/* s1GK */);
  if(!_WB/* s1GM */._){
    var _WC/* s1GN */ = _WB/* s1GM */.a,
    _WD/* s1GO */ = E(_WA/* s1GL */);
    return (_WD/* s1GO */._==0) ? _WC/* s1GN */!=_WD/* s1GO */.a : (I_compareInt/* EXTERNAL */(_WD/* s1GO */.a, _WC/* s1GN */)==0) ? false : true;
  }else{
    var _WE/* s1GU */ = _WB/* s1GM */.a,
    _WF/* s1GV */ = E(_WA/* s1GL */);
    return (_WF/* s1GV */._==0) ? (I_compareInt/* EXTERNAL */(_WE/* s1GU */, _WF/* s1GV */.a)==0) ? false : true : (I_compare/* EXTERNAL */(_WE/* s1GU */, _WF/* s1GV */.a)==0) ? false : true;
  }
},
_WG/* $fEqInteger */ = new T2(0,_Ry/* GHC.Integer.Type.eqInteger */,_Wy/* GHC.Integer.Type.neqInteger */),
_WH/* leInteger */ = function(_WI/* s1Gp */, _WJ/* s1Gq */){
  var _WK/* s1Gr */ = E(_WI/* s1Gp */);
  if(!_WK/* s1Gr */._){
    var _WL/* s1Gs */ = _WK/* s1Gr */.a,
    _WM/* s1Gt */ = E(_WJ/* s1Gq */);
    return (_WM/* s1Gt */._==0) ? _WL/* s1Gs */<=_WM/* s1Gt */.a : I_compareInt/* EXTERNAL */(_WM/* s1Gt */.a, _WL/* s1Gs */)>=0;
  }else{
    var _WN/* s1GA */ = _WK/* s1Gr */.a,
    _WO/* s1GB */ = E(_WJ/* s1Gq */);
    return (_WO/* s1GB */._==0) ? I_compareInt/* EXTERNAL */(_WN/* s1GA */, _WO/* s1GB */.a)<=0 : I_compare/* EXTERNAL */(_WN/* s1GA */, _WO/* s1GB */.a)<=0;
  }
},
_WP/* $fOrdInteger_$cmax */ = function(_WQ/* s1HU */, _WR/* s1HV */){
  return (!B(_WH/* GHC.Integer.Type.leInteger */(_WQ/* s1HU */, _WR/* s1HV */))) ? E(_WQ/* s1HU */) : E(_WR/* s1HV */);
},
_WS/* $fOrdInteger_$cmin */ = function(_WT/* s1HR */, _WU/* s1HS */){
  return (!B(_WH/* GHC.Integer.Type.leInteger */(_WT/* s1HR */, _WU/* s1HS */))) ? E(_WU/* s1HS */) : E(_WT/* s1HR */);
},
_WV/* compareInteger */ = function(_WW/* s1Hk */, _WX/* s1Hl */){
  var _WY/* s1Hm */ = E(_WW/* s1Hk */);
  if(!_WY/* s1Hm */._){
    var _WZ/* s1Hn */ = _WY/* s1Hm */.a,
    _X0/* s1Ho */ = E(_WX/* s1Hl */);
    if(!_X0/* s1Ho */._){
      var _X1/* s1Hp */ = _X0/* s1Ho */.a;
      return (_WZ/* s1Hn */!=_X1/* s1Hp */) ? (_WZ/* s1Hn */>_X1/* s1Hp */) ? 2 : 0 : 1;
    }else{
      var _X2/* s1Hw */ = I_compareInt/* EXTERNAL */(_X0/* s1Ho */.a, _WZ/* s1Hn */);
      return (_X2/* s1Hw */<=0) ? (_X2/* s1Hw */>=0) ? 1 : 2 : 0;
    }
  }else{
    var _X3/* s1HB */ = _WY/* s1Hm */.a,
    _X4/* s1HC */ = E(_WX/* s1Hl */);
    if(!_X4/* s1HC */._){
      var _X5/* s1HF */ = I_compareInt/* EXTERNAL */(_X3/* s1HB */, _X4/* s1HC */.a);
      return (_X5/* s1HF */>=0) ? (_X5/* s1HF */<=0) ? 1 : 2 : 0;
    }else{
      var _X6/* s1HM */ = I_compare/* EXTERNAL */(_X3/* s1HB */, _X4/* s1HC */.a);
      return (_X6/* s1HM */>=0) ? (_X6/* s1HM */<=0) ? 1 : 2 : 0;
    }
  }
},
_X7/* $fOrdInteger */ = {_:0,a:_WG/* GHC.Integer.Type.$fEqInteger */,b:_WV/* GHC.Integer.Type.compareInteger */,c:_LB/* GHC.Integer.Type.ltInteger */,d:_WH/* GHC.Integer.Type.leInteger */,e:_L5/* GHC.Integer.Type.gtInteger */,f:_Lt/* GHC.Integer.Type.geInteger */,g:_WP/* GHC.Integer.Type.$fOrdInteger_$cmax */,h:_WS/* GHC.Integer.Type.$fOrdInteger_$cmin */},
_X8/* $fRealInteger_$s$cfromInteger */ = function(_X9/* svmz */){
  return new T2(0,E(_X9/* svmz */),E(_KY/* GHC.Real.$fEnumRatio1 */));
},
_Xa/* $fRealInteger */ = new T3(0,_Wx/* GHC.Num.$fNumInteger */,_X7/* GHC.Integer.Type.$fOrdInteger */,_X8/* GHC.Real.$fRealInteger_$s$cfromInteger */),
_Xb/* $fIntegralInteger */ = {_:0,a:_Xa/* GHC.Real.$fRealInteger */,b:_VI/* GHC.Enum.$fEnumInteger */,c:_Wd/* GHC.Real.$fIntegralInteger_$cquot */,d:_RP/* GHC.Real.$fIntegralInteger_$crem */,e:_VU/* GHC.Real.$fIntegralInteger_$cdiv */,f:_Wa/* GHC.Real.$fIntegralInteger_$cmod */,g:_Wp/* GHC.Real.$fIntegralInteger_$cquotRem */,h:_W6/* GHC.Real.$fIntegralInteger_$cdivMod */,i:_Wt/* GHC.Real.$fIntegralInteger_$ctoInteger */},
_Xc/* $fFractionalFixed1 */ = new T1(0,0),
_Xd/* $fNumFixed5 */ = function(_Xe/* s6SxT */, _Xf/* s6SxU */, _Xg/* s6SxV */){
  var _Xh/* s6SxW */ = B(A1(_Xe/* s6SxT */,_Xf/* s6SxU */));
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_Xh/* s6SxW */, _Xc/* Data.Fixed.$fFractionalFixed1 */))){
    return new F(function(){return _VM/* GHC.Integer.Type.divInteger */(B(_Sh/* GHC.Integer.Type.timesInteger */(_Xf/* s6SxU */, _Xg/* s6SxV */)), _Xh/* s6SxW */);});
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_Xi/* $w$s$cproperFraction */ = function(_Xj/* svn0 */, _Xk/* svn1 */, _Xl/* svn2 */){
  var _Xm/* svn3 */ = new T(function(){
    if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_Xl/* svn2 */, _RG/* GHC.Real.even1 */))){
      var _Xn/* svn5 */ = B(_Wg/* GHC.Integer.Type.quotRemInteger */(_Xk/* svn1 */, _Xl/* svn2 */));
      return new T2(0,_Xn/* svn5 */.a,_Xn/* svn5 */.b);
    }else{
      return E(_Pz/* GHC.Real.divZeroError */);
    }
  }),
  _Xo/* svne */ = new T(function(){
    return B(A2(_L3/* GHC.Num.fromInteger */,B(_L1/* GHC.Real.$p1Real */(B(_KZ/* GHC.Real.$p1Integral */(_Xj/* svn0 */)))), new T(function(){
      return E(E(_Xm/* svn3 */).a);
    })));
  });
  return new T2(0,_Xo/* svne */,new T(function(){
    return new T2(0,E(E(_Xm/* svn3 */).b),E(_Xl/* svn2 */));
  }));
},
_Xp/* - */ = function(_Xq/* s6FH */){
  return E(E(_Xq/* s6FH */).b);
},
_Xr/* $w$s$cfloor */ = function(_Xs/* svJO */, _Xt/* svJP */, _Xu/* svJQ */){
  var _Xv/* svJR */ = B(_Xi/* GHC.Real.$w$s$cproperFraction */(_Xs/* svJO */, _Xt/* svJP */, _Xu/* svJQ */)),
  _Xw/* svJS */ = _Xv/* svJR */.a,
  _Xx/* svJU */ = E(_Xv/* svJR */.b);
  if(!B(_LB/* GHC.Integer.Type.ltInteger */(B(_Sh/* GHC.Integer.Type.timesInteger */(_Xx/* svJU */.a, _KY/* GHC.Real.$fEnumRatio1 */)), B(_Sh/* GHC.Integer.Type.timesInteger */(_RG/* GHC.Real.even1 */, _Xx/* svJU */.b))))){
    return E(_Xw/* svJS */);
  }else{
    var _Xy/* svK1 */ = B(_L1/* GHC.Real.$p1Real */(B(_KZ/* GHC.Real.$p1Integral */(_Xs/* svJO */))));
    return new F(function(){return A3(_Xp/* GHC.Num.- */,_Xy/* svK1 */, _Xw/* svJS */, new T(function(){
      return B(A2(_L3/* GHC.Num.fromInteger */,_Xy/* svK1 */, _KY/* GHC.Real.$fEnumRatio1 */));
    }));});
  }
},
_Xz/* slaT */ = 479723520,
_XA/* slaU */ = 40233135,
_XB/* slaV */ = new T2(1,_XA/* slaU */,_6/* GHC.Types.[] */),
_XC/* slaW */ = new T2(1,_Xz/* slaT */,_XB/* slaV */),
_XD/* posixDayLength1 */ = new T(function(){
  return B(_KA/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _XC/* slaW */));
}),
_XE/* posixSecondsToUTCTime1 */ = new T1(0,40587),
_XF/* $wposixSecondsToUTCTime */ = function(_XG/* slaX */){
  var _XH/* slaY */ = new T(function(){
    var _XI/* slaZ */ = B(_UX/* GHC.Real.$w$s$c/ */(_XG/* slaX */, _KY/* GHC.Real.$fEnumRatio1 */, _UC/* Data.Fixed.$fHasResolutionE5 */, _KY/* GHC.Real.$fEnumRatio1 */)),
    _XJ/* slb2 */ = B(_UX/* GHC.Real.$w$s$c/ */(_XD/* Data.Time.Clock.POSIX.posixDayLength1 */, _KY/* GHC.Real.$fEnumRatio1 */, _UC/* Data.Fixed.$fHasResolutionE5 */, _KY/* GHC.Real.$fEnumRatio1 */)),
    _XK/* slb5 */ = B(_UX/* GHC.Real.$w$s$c/ */(_XI/* slaZ */.a, _XI/* slaZ */.b, _XJ/* slb2 */.a, _XJ/* slb2 */.b));
    return B(_Xr/* GHC.Real.$w$s$cfloor */(_Xb/* GHC.Real.$fIntegralInteger */, _XK/* slb5 */.a, _XK/* slb5 */.b));
  });
  return new T2(0,new T(function(){
    return B(_Km/* GHC.Integer.Type.plusInteger */(_XE/* Data.Time.Clock.POSIX.posixSecondsToUTCTime1 */, _XH/* slaY */));
  }),new T(function(){
    return B(_M1/* GHC.Integer.Type.minusInteger */(_XG/* slaX */, B(_Xd/* Data.Fixed.$fNumFixed5 */(_V3/* Data.Fixed.$fHasResolutionE12_$cresolution */, B(_Sh/* GHC.Integer.Type.timesInteger */(_XH/* slaY */, _UC/* Data.Fixed.$fHasResolutionE5 */)), _XD/* Data.Time.Clock.POSIX.posixDayLength1 */))));
  }));
},
_XL/* getCPUTime2 */ = new T1(0,0),
_XM/* $wa1 */ = function(_XN/* s3vS */, _/* EXTERNAL */){
  var _XO/* s3vX */ = __get/* EXTERNAL */(_XN/* s3vS */, 0),
  _XP/* s3w3 */ = __get/* EXTERNAL */(_XN/* s3vS */, 1),
  _XQ/* s3w7 */ = Number/* EXTERNAL */(_XO/* s3vX */),
  _XR/* s3wb */ = jsTrunc/* EXTERNAL */(_XQ/* s3w7 */),
  _XS/* s3wf */ = Number/* EXTERNAL */(_XP/* s3w3 */),
  _XT/* s3wj */ = jsTrunc/* EXTERNAL */(_XS/* s3wf */);
  return new T2(0,_XR/* s3wb */,_XT/* s3wj */);
},
_XU/* getCTimeval_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");
}),
_XV/* slbq */ = 660865024,
_XW/* slbr */ = 465661287,
_XX/* slbs */ = new T2(1,_XW/* slbr */,_6/* GHC.Types.[] */),
_XY/* slbt */ = new T2(1,_XV/* slbq */,_XX/* slbs */),
_XZ/* getPOSIXTime2 */ = new T(function(){
  return B(_KA/* GHC.Integer.Type.mkInteger */(_aw/* GHC.Types.True */, _XY/* slbt */));
}),
_Y0/* getPOSIXTime1 */ = function(_/* EXTERNAL */){
  var _Y1/* slby */ = __app0/* EXTERNAL */(E(_XU/* Data.Time.Clock.CTimeval.getCTimeval_f1 */)),
  _Y2/* slbB */ = B(_XM/* Data.Time.Clock.CTimeval.$wa1 */(_Y1/* slby */, _/* EXTERNAL */));
  return new T(function(){
    var _Y3/* slbE */ = E(_Y2/* slbB */);
    if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_XZ/* Data.Time.Clock.POSIX.getPOSIXTime2 */, _Xc/* Data.Fixed.$fFractionalFixed1 */))){
      return B(_Km/* GHC.Integer.Type.plusInteger */(B(_Sh/* GHC.Integer.Type.timesInteger */(B(_MM/* GHC.Integer.Type.smallInteger */(E(_Y3/* slbE */.a))), _UC/* Data.Fixed.$fHasResolutionE5 */)), B(_VM/* GHC.Integer.Type.divInteger */(B(_Sh/* GHC.Integer.Type.timesInteger */(B(_Sh/* GHC.Integer.Type.timesInteger */(B(_MM/* GHC.Integer.Type.smallInteger */(E(_Y3/* slbE */.b))), _UC/* Data.Fixed.$fHasResolutionE5 */)), _UC/* Data.Fixed.$fHasResolutionE5 */)), _XZ/* Data.Time.Clock.POSIX.getPOSIXTime2 */))));
    }else{
      return E(_Pz/* GHC.Real.divZeroError */);
    }
  });
},
_Y4/* getStdRandom3 */ = new T1(0,12345),
_Y5/* getStdRandom2 */ = function(_/* EXTERNAL */){
  var _Y6/* sfpA */ = B(_Y0/* Data.Time.Clock.POSIX.getPOSIXTime1 */(0)),
  _Y7/* sfpG */ = B(_UX/* GHC.Real.$w$s$c/ */(B(_XF/* Data.Time.Clock.POSIX.$wposixSecondsToUTCTime */(_Y6/* sfpA */)).b, _KY/* GHC.Real.$fEnumRatio1 */, _UC/* Data.Fixed.$fHasResolutionE5 */, _KY/* GHC.Real.$fEnumRatio1 */)),
  _Y8/* sfpI */ = _Y7/* sfpG */.b;
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_Y8/* sfpI */, _TB/* System.Random.getStdRandom4 */))){
    var _Y9/* sfpK */ = B(_Wg/* GHC.Integer.Type.quotRemInteger */(_Y7/* sfpG */.a, _Y8/* sfpI */));
    return new F(function(){return nMV/* EXTERNAL */(new T(function(){
      var _Ya/* sfpV */ = B(_UE/* GHC.Int.$w$cdivMod1 */((B(_Vx/* GHC.Integer.Type.integerToInt */(B(_Km/* GHC.Integer.Type.plusInteger */(B(_Km/* GHC.Integer.Type.plusInteger */(B(_Km/* GHC.Integer.Type.plusInteger */(B(_Sh/* GHC.Integer.Type.timesInteger */(_Y9/* sfpK */.a, _Y4/* System.Random.getStdRandom3 */)), _Y9/* sfpK */.b)), _XL/* System.CPUTime.getCPUTime2 */)), _TB/* System.Random.getStdRandom4 */))))>>>0&2147483647)>>>0&4294967295, 2147483562));
      return new T2(0,E(_Ya/* sfpV */.b)+1|0,B(_TD/* GHC.Classes.modInt# */(E(_Ya/* sfpV */.a), 2147483398))+1|0);
    }));});
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_Yb/* theStdGen */ = new T(function(){
  return B(_44/* GHC.IO.unsafeDupablePerformIO */(_Y5/* System.Random.getStdRandom2 */));
}),
_Yc/* $fRandomDouble8 */ = function(_Yd/* sfTt */, _/* EXTERNAL */){
  var _Ye/* sfTM */ = mMV/* EXTERNAL */(E(_Yb/* System.Random.theStdGen */), function(_Yf/* sfTx */){
    var _Yg/* sfTy */ = E(_Yd/* sfTt */),
    _Yh/* sfTF */ = B(_Uk/* System.Random.$w$srandomRFloating2 */(E(_Yg/* sfTy */.a), E(_Yg/* sfTy */.b), _Yf/* sfTx */));
    return new T2(0,E(_Yh/* sfTF */.b),_Yh/* sfTF */.a);
  }),
  _Yi/* sfTQ */ = E(_Ye/* sfTM */);
  return _Ye/* sfTM */;
},
_Yj/* speedMot19 */ = 1,
_Yk/* speedMot18 */ = new T2(0,_Jw/* Motion.Speed.speedMot14 */,_Yj/* Motion.Speed.speedMot19 */),
_Yl/* speedMot17 */ = function(_/* EXTERNAL */){
  return new F(function(){return _Yc/* System.Random.$fRandomDouble8 */(_Yk/* Motion.Speed.speedMot18 */, _/* EXTERNAL */);});
},
_Ym/* speedMot16 */ = new T1(1,_Yl/* Motion.Speed.speedMot17 */),
_Yn/* speedMot15 */ = new T(function(){
  return B(_rx/* Control.Monad.Skeleton.bone */(_Ym/* Motion.Speed.speedMot16 */));
}),
_Yo/* speedMot3 */ = 60,
_Yp/* speedMot2 */ = new T1(0,_Yo/* Motion.Speed.speedMot3 */),
_Yq/* speedMot22 */ = 100,
_Yr/* speedMot21 */ = new T1(0,_Yq/* Motion.Speed.speedMot22 */),
_Ys/* speedMot20 */ = new T2(0,_Yr/* Motion.Speed.speedMot21 */,_Yr/* Motion.Speed.speedMot21 */),
_Yt/* speedMot5 */ = -30,
_Yu/* speedMot4 */ = new T1(0,_Yt/* Motion.Speed.speedMot5 */),
_Yv/* speedMot8 */ = new T(function(){
  return  -0;
}),
_Yw/* speedMot7 */ = new T1(0,_Yv/* Motion.Speed.speedMot8 */),
_Yx/* speedMot6 */ = new T2(0,_Yw/* Motion.Speed.speedMot7 */,_Yw/* Motion.Speed.speedMot7 */),
_Yy/* $fFloatingDouble_$cpi */ = 3.141592653589793,
_Yz/* $s$fFloatingValue_$cpi */ = new T1(0,_Yy/* GHC.Float.$fFloatingDouble_$cpi */),
_YA/* speedMot11 */ = 6,
_YB/* speedMot10 */ = new T1(0,_YA/* Motion.Speed.speedMot11 */),
_YC/* speedMot9 */ = new T(function(){
  return B(_sg/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, _Yz/* Motion.Speed.$s$fFloatingValue_$cpi */, _YB/* Motion.Speed.speedMot10 */));
}),
_YD/* speedMot */ = function(_YE/* sRjs */){
  var _YF/* sRjt */ = new T(function(){
    var _YG/* sRkl */ = new T(function(){
      var _YH/* sRju */ = E(_Yn/* Motion.Speed.speedMot15 */),
      _YI/* sRjv */ = _YH/* sRju */.a,
      _YJ/* sRjw */ = _YH/* sRju */.b,
      _YK/* sRki */ = function(_YL/* sRjx */){
        var _YM/* sRjy */ = new T(function(){
          var _YN/* sRjB */ = Math.log/* EXTERNAL */(E(_YL/* sRjx */));
          return Math.sqrt/* EXTERNAL */( -(_YN/* sRjB */+_YN/* sRjB */));
        }),
        _YO/* sRkf */ = function(_YP/* sRjF */){
          var _YQ/* sRjG */ = new T(function(){
            var _YR/* sRjH */ = E(_YM/* sRjy */),
            _YS/* sRjJ */ = E(_YP/* sRjF */);
            return _YR/* sRjH */*Math.sin/* EXTERNAL */(6.283185307179586*_YS/* sRjJ */)+_YR/* sRjH */*Math.sin/* EXTERNAL */(6.283185307179586*_YS/* sRjJ */);
          }),
          _YT/* sRkc */ = function(_YU/* sRjT */){
            var _YV/* sRka */ = new T(function(){
              var _YW/* sRk8 */ = new T(function(){
                var _YX/* sRk6 */ = new T(function(){
                  var _YY/* sRk5 */ = new T(function(){
                    var _YZ/* sRk0 */ = new T(function(){
                      return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _Yu/* Motion.Speed.speedMot4 */, new T1(0,new T(function(){
                        return 4/(1-E(_YU/* sRjT */));
                      }))));
                    }),
                    _Z0/* sRk1 */ = B(_GQ/* Core.Shape.Internal.$wcenterRect */(new T1(0,_YQ/* sRjG */), _YZ/* sRk0 */, _Yp/* Motion.Speed.speedMot2 */, _Yp/* Motion.Speed.speedMot2 */));
                    return new T3(0,_Z0/* sRk1 */.a,_Z0/* sRk1 */.b,_Z0/* sRk1 */.c);
                  });
                  return B(_rB/* Core.Render.Internal.fill1 */(_YE/* sRjs */, _YY/* sRk5 */));
                });
                return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_Yx/* Motion.Speed.speedMot6 */,_YX/* sRk6 */,_7/* GHC.Tuple.() */)));
              });
              return B(_rx/* Control.Monad.Skeleton.bone */(new T3(6,_YC/* Motion.Speed.speedMot9 */,_YW/* sRk8 */,_7/* GHC.Tuple.() */)));
            });
            return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T3(5,_Jy/* Motion.Speed.speedMot12 */,_YV/* sRka */,_7/* GHC.Tuple.() */));});
          };
          return new T2(0,E(_YI/* sRjv */),E(new T2(2,_YJ/* sRjw */,new T1(1,_YT/* sRkc */))));
        };
        return new T2(0,E(_YI/* sRjv */),E(new T2(2,_YJ/* sRjw */,new T1(1,_YO/* sRkf */))));
      };
      return new T2(0,E(_YI/* sRjv */),E(new T2(2,_YJ/* sRjw */,new T1(1,_YK/* sRki */))));
    });
    return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_Ys/* Motion.Speed.speedMot20 */,_YG/* sRkl */,_7/* GHC.Tuple.() */)));
  });
  return function(_Z1/* sRko */, _Z2/* sRkp */){
    return new F(function(){return A1(_Z2/* sRkp */,new T2(0,new T2(0,_YF/* sRjt */,_Jt/* Motion.Speed.speedMot1 */),_Z1/* sRko */));});
  };
},
_Z3/* lvl53 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_Jq/* Motion.Main.lvl50 */, _YD/* Motion.Speed.speedMot */, _Jr/* Motion.Main.lvl51 */, _Js/* Motion.Main.lvl52 */));
}),
_Z4/* $sreplicateM2 */ = function(_Z5/* s81j */, _Z6/* s81k */){
  var _Z7/* s81l */ = E(_Z5/* s81j */);
  if(!_Z7/* s81l */._){
    return function(_Z8/* s81n */){
      return new F(function(){return A1(_Z8/* s81n */,new T2(0,_6/* GHC.Types.[] */,_Z6/* s81k */));});
    };
  }else{
    var _Z9/* s81C */ = function(_Za/* s81r */){
      var _Zb/* s81s */ = new T(function(){
        return B(A1(_Z7/* s81l */.a,_Za/* s81r */));
      }),
      _Zc/* s81B */ = function(_Zd/* s81t */){
        var _Ze/* s81A */ = function(_Zf/* s81u */){
          var _Zg/* s81z */ = new T(function(){
            var _Zh/* s81v */ = E(_Zf/* s81u */);
            return new T2(0,function(_Zi/* B1 */){
              return new T2(1,_Zh/* s81v */.a,_Zi/* B1 */);
            },_Zh/* s81v */.b);
          });
          return new F(function(){return A1(_Zd/* s81t */,_Zg/* s81z */);});
        };
        return new F(function(){return A1(_Zb/* s81s */,_Ze/* s81A */);});
      };
      return E(_Zc/* s81B */);
    };
    return new F(function(){return _55/* Core.World.Internal.$fApplicativeWorld3 */(_Z9/* s81C */, function(_Zi/* B1 */){
      return new F(function(){return _Z4/* Motion.Change.$sreplicateM2 */(_Z7/* s81l */.b, _Zi/* B1 */);});
    }, _Z6/* s81k */);});
  }
},
_Zj/* $swhen1 */ = new T(function(){
  return B(_qY/* Control.Monad.Skeleton.$w$cpure */(_/* EXTERNAL */, _7/* GHC.Tuple.() */));
}),
_Zk/* $fNumInt_$c* */ = function(_Zl/* s6GP */, _Zm/* s6GQ */){
  return imul/* EXTERNAL */(E(_Zl/* s6GP */), E(_Zm/* s6GQ */))|0;
},
_Zn/* $fNumInt_$c+ */ = function(_Zo/* s6H3 */, _Zp/* s6H4 */){
  return E(_Zo/* s6H3 */)+E(_Zp/* s6H4 */)|0;
},
_Zq/* $fNumInt_$c- */ = function(_Zr/* s6GW */, _Zs/* s6GX */){
  return E(_Zr/* s6GW */)-E(_Zs/* s6GX */)|0;
},
_Zt/* $fNumInt_$cabs */ = function(_Zu/* s6Hg */){
  var _Zv/* s6Hh */ = E(_Zu/* s6Hg */);
  return (_Zv/* s6Hh */<0) ?  -_Zv/* s6Hh */ : E(_Zv/* s6Hh */);
},
_Zw/* $fNumInt_$cfromInteger */ = function(_Zx/* s6GJ */){
  return new F(function(){return _Vx/* GHC.Integer.Type.integerToInt */(_Zx/* s6GJ */);});
},
_Zy/* $fNumInt_$cnegate */ = function(_Zz/* s6GL */){
  return  -E(_Zz/* s6GL */);
},
_ZA/* $fNumInt1 */ = -1,
_ZB/* $fNumInt2 */ = 0,
_ZC/* $fNumInt3 */ = 1,
_ZD/* $fNumInt_$csignum */ = function(_ZE/* s6Ha */){
  var _ZF/* s6Hb */ = E(_ZE/* s6Ha */);
  return (_ZF/* s6Hb */>=0) ? (E(_ZF/* s6Hb */)==0) ? E(_ZB/* GHC.Num.$fNumInt2 */) : E(_ZC/* GHC.Num.$fNumInt3 */) : E(_ZA/* GHC.Num.$fNumInt1 */);
},
_ZG/* $fNumInt */ = {_:0,a:_Zn/* GHC.Num.$fNumInt_$c+ */,b:_Zq/* GHC.Num.$fNumInt_$c- */,c:_Zk/* GHC.Num.$fNumInt_$c* */,d:_Zy/* GHC.Num.$fNumInt_$cnegate */,e:_Zt/* GHC.Num.$fNumInt_$cabs */,f:_ZD/* GHC.Num.$fNumInt_$csignum */,g:_Zw/* GHC.Num.$fNumInt_$cfromInteger */},
_ZH/* $fRandomBool2 */ = function(_ZI/* sftN */){
  var _ZJ/* sftO */ = B(_TS/* System.Random.$w$srandomIvalInteger */(_ZG/* GHC.Num.$fNumInt */, _TB/* System.Random.getStdRandom4 */, _Tm/* System.Random.$fRandomBool3 */, _ZI/* sftN */));
  return new T2(0,E(_ZJ/* sftO */.b),new T(function(){
    if(!E(_ZJ/* sftO */.a)){
      return false;
    }else{
      return true;
    }
  }));
},
_ZK/* a10 */ = function(_ZL/* s82q */, _ZM/* s82r */, _ZN/* s82s */){
  var _ZO/* s82t */ = E(_ZL/* s82q */);
  if(!_ZO/* s82t */._){
    return new F(function(){return A1(_ZN/* s82s */,new T2(0,_7/* GHC.Tuple.() */,_ZM/* s82r */));});
  }else{
    var _ZP/* s83c */ = function(_/* EXTERNAL */){
      var _ZQ/* s82y */ = E(_Yb/* System.Random.theStdGen */),
      _ZR/* s82A */ = mMV/* EXTERNAL */(_ZQ/* s82y */, _ZH/* System.Random.$fRandomBool2 */);
      return new T(function(){
        var _ZS/* s83a */ = function(_ZT/* s82I */){
          var _ZU/* s82M */ = function(_ZV/* s82N */, _ZW/* s82O */, _ZX/* s82P */){
            var _ZY/* s82Q */ = E(_ZV/* s82N */);
            if(!_ZY/* s82Q */._){
              return new F(function(){return A1(_ZX/* s82P */,new T2(0,_7/* GHC.Tuple.() */,_ZW/* s82O */));});
            }else{
              var _ZZ/* s839 */ = function(_/* EXTERNAL */){
                var _100/* s82V */ = mMV/* EXTERNAL */(_ZQ/* s82y */, _ZH/* System.Random.$fRandomBool2 */);
                return new T(function(){
                  return B(A(_jN/* Core.Ease.$wforceTo */,[E(_ZY/* s82Q */.a).c, E(_100/* s82V */), _ZW/* s82O */, function(_101/* s833 */){
                    return new F(function(){return _ZU/* s82M */(_ZY/* s82Q */.b, E(_101/* s833 */).b, _ZX/* s82P */);});
                  }]));
                });
              };
              return new T1(0,_ZZ/* s839 */);
            }
          };
          return new F(function(){return _ZU/* s82M */(_ZO/* s82t */.b, E(_ZT/* s82I */).b, _ZN/* s82s */);});
        };
        return B(A(_jN/* Core.Ease.$wforceTo */,[E(_ZO/* s82t */.a).c, E(_ZR/* s82A */), _ZM/* s82r */, _ZS/* s83a */]));
      });
    };
    return new T1(0,_ZP/* s83c */);
  }
},
_102/* a */ = new T1(0,_/* EXTERNAL */),
_103/* a1 */ = new T1(0,_7/* GHC.Tuple.() */),
_104/* a2 */ = new T2(0,E(_103/* Motion.Change.a1 */),E(_102/* Motion.Change.a */)),
_105/* lvl */ = new T4(0,_aw/* GHC.Types.True */,_aw/* GHC.Types.True */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_106/* lvl1 */ = new T2(0,_aw/* GHC.Types.True */,_105/* Motion.Change.lvl */),
_107/* lvl2 */ = new T2(0,_106/* Motion.Change.lvl1 */,_6/* GHC.Types.[] */),
_108/* lvl3 */ = function(_109/* s81E */, _10a/* s81F */){
  var _10b/* s81O */ = function(_/* EXTERNAL */){
    var _10c/* s81H */ = nMV/* EXTERNAL */(_107/* Motion.Change.lvl2 */);
    return new T(function(){
      return B(A1(_10a/* s81F */,new T2(0,new T3(0,_jM/* Core.Ease.forceTo_b1 */,_lA/* Core.Ease.easeIn */,_10c/* s81H */),_109/* s81E */)));
    });
  };
  return new T1(0,_10b/* s81O */);
},
_10d/* lvl4 */ = new T2(1,_108/* Motion.Change.lvl3 */,_6/* GHC.Types.[] */),
_10e/* $wxs */ = function(_10f/* s81P */){
  var _10g/* s81Q */ = E(_10f/* s81P */);
  return (_10g/* s81Q */==1) ? E(_10d/* Motion.Change.lvl4 */) : new T2(1,_108/* Motion.Change.lvl3 */,new T(function(){
    return B(_10e/* Motion.Change.$wxs */(_10g/* s81Q */-1|0));
  }));
},
_10h/* a7 */ = new T(function(){
  return B(_10e/* Motion.Change.$wxs */(10));
}),
_10i/* dur */ = 10,
_10j/* e */ = function(_10k/* s81T */, _10l/* s81U */){
  return 1-B(A1(_10k/* s81T */,new T(function(){
    return Math.pow/* EXTERNAL */(2,  -((1-(1-E(_10l/* s81U */)))*10));
  })));
},
_10m/* $fRealDouble1 */ = new T1(0,1),
_10n/* encodeDoubleInteger */ = function(_10o/* s1LC */, _10p/* s1LD */){
  var _10q/* s1LE */ = E(_10o/* s1LC */);
  return (_10q/* s1LE */._==0) ? _10q/* s1LE */.a*Math.pow/* EXTERNAL */(2, _10p/* s1LD */) : I_toNumber/* EXTERNAL */(_10q/* s1LE */.a)*Math.pow/* EXTERNAL */(2, _10p/* s1LD */);
},
_10r/* rationalToDouble5 */ = new T1(0,0),
_10s/* $w$j1 */ = function(_10t/* s18QG */, _10u/* s18QH */, _10v/* s18QI */){
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_10v/* s18QI */, _10r/* GHC.Float.rationalToDouble5 */))){
    var _10w/* s18QK */ = B(_Wg/* GHC.Integer.Type.quotRemInteger */(_10u/* s18QH */, _10v/* s18QI */)),
    _10x/* s18QL */ = _10w/* s18QK */.a;
    switch(B(_WV/* GHC.Integer.Type.compareInteger */(B(_Kd/* GHC.Integer.Type.shiftLInteger */(_10w/* s18QK */.b, 1)), _10v/* s18QI */))){
      case 0:
        return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(_10x/* s18QL */, _10t/* s18QG */);});
        break;
      case 1:
        if(!(B(_Vx/* GHC.Integer.Type.integerToInt */(_10x/* s18QL */))&1)){
          return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(_10x/* s18QL */, _10t/* s18QG */);});
        }else{
          return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(B(_Km/* GHC.Integer.Type.plusInteger */(_10x/* s18QL */, _10m/* GHC.Float.$fRealDouble1 */)), _10t/* s18QG */);});
        }
        break;
      default:
        return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(B(_Km/* GHC.Integer.Type.plusInteger */(_10x/* s18QL */, _10m/* GHC.Float.$fRealDouble1 */)), _10t/* s18QG */);});
    }
  }else{
    return E(_Pz/* GHC.Real.divZeroError */);
  }
},
_10y/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_10z/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_10A/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_10B/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_10y/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_10z/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_10A/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_10C/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_10B/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_10D/* $fExceptionPatternMatchFail1 */ = function(_10E/* s4nDQ */){
  return E(_10C/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_10F/* $fExceptionPatternMatchFail_$cfromException */ = function(_10G/* s4nE1 */){
  var _10H/* s4nE2 */ = E(_10G/* s4nE1 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_10H/* s4nE2 */.a)), _10D/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _10H/* s4nE2 */.b);});
},
_10I/* $fExceptionPatternMatchFail_$cshow */ = function(_10J/* s4nDT */){
  return E(E(_10J/* s4nDT */).a);
},
_10K/* $fExceptionPatternMatchFail_$ctoException */ = function(_10L/* B1 */){
  return new T2(0,_10M/* Control.Exception.Base.$fExceptionPatternMatchFail */,_10L/* B1 */);
},
_10N/* $fShowPatternMatchFail1 */ = function(_10O/* s4nzz */, _10P/* s4nzA */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_10O/* s4nzz */).a, _10P/* s4nzA */);});
},
_10Q/* $fShowPatternMatchFail_$cshowList */ = function(_10R/* s4nDR */, _10S/* s4nDS */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_10N/* Control.Exception.Base.$fShowPatternMatchFail1 */, _10R/* s4nDR */, _10S/* s4nDS */);});
},
_10T/* $fShowPatternMatchFail_$cshowsPrec */ = function(_10U/* s4nDW */, _10V/* s4nDX */, _10W/* s4nDY */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_10V/* s4nDX */).a, _10W/* s4nDY */);});
},
_10X/* $fShowPatternMatchFail */ = new T3(0,_10T/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_10I/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_10Q/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_10M/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_10D/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_10X/* Control.Exception.Base.$fShowPatternMatchFail */,_10K/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_10F/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_10I/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_10Y/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_10Z/* lvl */ = function(_110/* s2S2g */, _111/* s2S2h */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_111/* s2S2h */, _110/* s2S2g */));
  }));});
},
_112/* throw1 */ = function(_113/* B2 */, _Pw/* B1 */){
  return new F(function(){return _10Z/* GHC.Exception.lvl */(_113/* B2 */, _Pw/* B1 */);});
},
_114/* $wspan */ = function(_115/* s9wA */, _116/* s9wB */){
  var _117/* s9wC */ = E(_116/* s9wB */);
  if(!_117/* s9wC */._){
    return new T2(0,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */);
  }else{
    var _118/* s9wD */ = _117/* s9wC */.a;
    if(!B(A1(_115/* s9wA */,_118/* s9wD */))){
      return new T2(0,_6/* GHC.Types.[] */,_117/* s9wC */);
    }else{
      var _119/* s9wG */ = new T(function(){
        var _11a/* s9wH */ = B(_114/* GHC.List.$wspan */(_115/* s9wA */, _117/* s9wC */.b));
        return new T2(0,_11a/* s9wH */.a,_11a/* s9wH */.b);
      });
      return new T2(0,new T2(1,_118/* s9wD */,new T(function(){
        return E(E(_119/* s9wG */).a);
      })),new T(function(){
        return E(E(_119/* s9wG */).b);
      }));
    }
  }
},
_11b/* untangle1 */ = 32,
_11c/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_11d/* untangle3 */ = function(_11e/* s3JKg */){
  return (E(_11e/* s3JKg */)==124) ? false : true;
},
_11f/* untangle */ = function(_11g/* s3JL9 */, _11h/* s3JLa */){
  var _11i/* s3JLc */ = B(_114/* GHC.List.$wspan */(_11d/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_11g/* s3JL9 */)))),
  _11j/* s3JLd */ = _11i/* s3JLc */.a,
  _11k/* s3JLf */ = function(_11l/* s3JLg */, _11m/* s3JLh */){
    var _11n/* s3JLk */ = new T(function(){
      var _11o/* s3JLj */ = new T(function(){
        return B(_2/* GHC.Base.++ */(_11h/* s3JLa */, new T(function(){
          return B(_2/* GHC.Base.++ */(_11m/* s3JLh */, _11c/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _11o/* s3JLj */));
    },1);
    return new F(function(){return _2/* GHC.Base.++ */(_11l/* s3JLg */, _11n/* s3JLk */);});
  },
  _11p/* s3JLl */ = E(_11i/* s3JLc */.b);
  if(!_11p/* s3JLl */._){
    return new F(function(){return _11k/* s3JLf */(_11j/* s3JLd */, _6/* GHC.Types.[] */);});
  }else{
    if(E(_11p/* s3JLl */.a)==124){
      return new F(function(){return _11k/* s3JLf */(_11j/* s3JLd */, new T2(1,_11b/* GHC.IO.Exception.untangle1 */,_11p/* s3JLl */.b));});
    }else{
      return new F(function(){return _11k/* s3JLf */(_11j/* s3JLd */, _6/* GHC.Types.[] */);});
    }
  }
},
_11q/* patError */ = function(_11r/* s4nFx */){
  return new F(function(){return _112/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_11f/* GHC.IO.Exception.untangle */(_11r/* s4nFx */, _10Y/* Control.Exception.Base.lvl3 */));
  })), _10M/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_11s/* log2I */ = function(_11t/* s1Ju */){
  var _11u/* s1Jv */ = function(_11v/* s1Jw */, _11w/* s1Jx */){
    while(1){
      if(!B(_LB/* GHC.Integer.Type.ltInteger */(_11v/* s1Jw */, _11t/* s1Ju */))){
        if(!B(_L5/* GHC.Integer.Type.gtInteger */(_11v/* s1Jw */, _11t/* s1Ju */))){
          if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_11v/* s1Jw */, _11t/* s1Ju */))){
            return new F(function(){return _11q/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});
          }else{
            return E(_11w/* s1Jx */);
          }
        }else{
          return _11w/* s1Jx */-1|0;
        }
      }else{
        var _11x/*  s1Jw */ = B(_Kd/* GHC.Integer.Type.shiftLInteger */(_11v/* s1Jw */, 1)),
        _11y/*  s1Jx */ = _11w/* s1Jx */+1|0;
        _11v/* s1Jw */ = _11x/*  s1Jw */;
        _11w/* s1Jx */ = _11y/*  s1Jx */;
        continue;
      }
    }
  };
  return new F(function(){return _11u/* s1Jv */(_Kk/* GHC.Integer.Type.log2I1 */, 0);});
},
_11z/* integerLog2# */ = function(_11A/* s1JD */){
  var _11B/* s1JE */ = E(_11A/* s1JD */);
  if(!_11B/* s1JE */._){
    var _11C/* s1JG */ = _11B/* s1JE */.a>>>0;
    if(!_11C/* s1JG */){
      return -1;
    }else{
      var _11D/* s1JH */ = function(_11E/* s1JI */, _11F/* s1JJ */){
        while(1){
          if(_11E/* s1JI */>=_11C/* s1JG */){
            if(_11E/* s1JI */<=_11C/* s1JG */){
              if(_11E/* s1JI */!=_11C/* s1JG */){
                return new F(function(){return _11q/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_11F/* s1JJ */);
              }
            }else{
              return _11F/* s1JJ */-1|0;
            }
          }else{
            var _11G/*  s1JI */ = imul/* EXTERNAL */(_11E/* s1JI */, 2)>>>0,
            _11H/*  s1JJ */ = _11F/* s1JJ */+1|0;
            _11E/* s1JI */ = _11G/*  s1JI */;
            _11F/* s1JJ */ = _11H/*  s1JJ */;
            continue;
          }
        }
      };
      return new F(function(){return _11D/* s1JH */(1, 0);});
    }
  }else{
    return new F(function(){return _11s/* GHC.Integer.Type.log2I */(_11B/* s1JE */);});
  }
},
_11I/* integerLog2IsPowerOf2# */ = function(_11J/* s1JT */){
  var _11K/* s1JU */ = E(_11J/* s1JT */);
  if(!_11K/* s1JU */._){
    var _11L/* s1JW */ = _11K/* s1JU */.a>>>0;
    if(!_11L/* s1JW */){
      return new T2(0,-1,0);
    }else{
      var _11M/* s1JX */ = function(_11N/* s1JY */, _11O/* s1JZ */){
        while(1){
          if(_11N/* s1JY */>=_11L/* s1JW */){
            if(_11N/* s1JY */<=_11L/* s1JW */){
              if(_11N/* s1JY */!=_11L/* s1JW */){
                return new F(function(){return _11q/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_11O/* s1JZ */);
              }
            }else{
              return _11O/* s1JZ */-1|0;
            }
          }else{
            var _11P/*  s1JY */ = imul/* EXTERNAL */(_11N/* s1JY */, 2)>>>0,
            _11Q/*  s1JZ */ = _11O/* s1JZ */+1|0;
            _11N/* s1JY */ = _11P/*  s1JY */;
            _11O/* s1JZ */ = _11Q/*  s1JZ */;
            continue;
          }
        }
      };
      return new T2(0,B(_11M/* s1JX */(1, 0)),(_11L/* s1JW */&_11L/* s1JW */-1>>>0)>>>0&4294967295);
    }
  }else{
    var _11R/* s1Kc */ = _11K/* s1JU */.a;
    return new T2(0,B(_11z/* GHC.Integer.Type.integerLog2# */(_11K/* s1JU */)),I_compareInt/* EXTERNAL */(I_and/* EXTERNAL */(_11R/* s1Kc */, I_sub/* EXTERNAL */(_11R/* s1Kc */, I_fromInt/* EXTERNAL */(1))), 0));
  }
},
_11S/* andInteger */ = function(_11T/* s1Lf */, _11U/* s1Lg */){
  while(1){
    var _11V/* s1Lh */ = E(_11T/* s1Lf */);
    if(!_11V/* s1Lh */._){
      var _11W/* s1Li */ = _11V/* s1Lh */.a,
      _11X/* s1Lj */ = E(_11U/* s1Lg */);
      if(!_11X/* s1Lj */._){
        return new T1(0,(_11W/* s1Li */>>>0&_11X/* s1Lj */.a>>>0)>>>0&4294967295);
      }else{
        _11T/* s1Lf */ = new T1(1,I_fromInt/* EXTERNAL */(_11W/* s1Li */));
        _11U/* s1Lg */ = _11X/* s1Lj */;
        continue;
      }
    }else{
      var _11Y/* s1Lu */ = E(_11U/* s1Lg */);
      if(!_11Y/* s1Lu */._){
        _11T/* s1Lf */ = _11V/* s1Lh */;
        _11U/* s1Lg */ = new T1(1,I_fromInt/* EXTERNAL */(_11Y/* s1Lu */.a));
        continue;
      }else{
        return new T1(1,I_and/* EXTERNAL */(_11V/* s1Lh */.a, _11Y/* s1Lu */.a));
      }
    }
  }
},
_11Z/* roundingMode#1 */ = new T1(0,2),
_120/* roundingMode# */ = function(_121/* s1Pt */, _122/* s1Pu */){
  var _123/* s1Pv */ = E(_121/* s1Pt */);
  if(!_123/* s1Pv */._){
    var _124/* s1Px */ = (_123/* s1Pv */.a>>>0&(2<<_122/* s1Pu */>>>0)-1>>>0)>>>0,
    _125/* s1PB */ = 1<<_122/* s1Pu */>>>0;
    return (_125/* s1PB */<=_124/* s1Px */) ? (_125/* s1PB */>=_124/* s1Px */) ? 1 : 2 : 0;
  }else{
    var _126/* s1PH */ = B(_11S/* GHC.Integer.Type.andInteger */(_123/* s1Pv */, B(_M1/* GHC.Integer.Type.minusInteger */(B(_Kd/* GHC.Integer.Type.shiftLInteger */(_11Z/* GHC.Integer.Type.roundingMode#1 */, _122/* s1Pu */)), _Kk/* GHC.Integer.Type.log2I1 */)))),
    _127/* s1PK */ = B(_Kd/* GHC.Integer.Type.shiftLInteger */(_Kk/* GHC.Integer.Type.log2I1 */, _122/* s1Pu */));
    return (!B(_L5/* GHC.Integer.Type.gtInteger */(_127/* s1PK */, _126/* s1PH */))) ? (!B(_LB/* GHC.Integer.Type.ltInteger */(_127/* s1PK */, _126/* s1PH */))) ? 1 : 2 : 0;
  }
},
_128/* shiftRInteger */ = function(_129/* s1Ja */, _12a/* s1Jb */){
  while(1){
    var _12b/* s1Jc */ = E(_129/* s1Ja */);
    if(!_12b/* s1Jc */._){
      _129/* s1Ja */ = new T1(1,I_fromInt/* EXTERNAL */(_12b/* s1Jc */.a));
      continue;
    }else{
      return new T1(1,I_shiftRight/* EXTERNAL */(_12b/* s1Jc */.a, _12a/* s1Jb */));
    }
  }
},
_12c/* $w$sfromRat'' */ = function(_12d/* s18QU */, _12e/* s18QV */, _12f/* s18QW */, _12g/* s18QX */){
  var _12h/* s18QY */ = B(_11I/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_12g/* s18QX */)),
  _12i/* s18QZ */ = _12h/* s18QY */.a;
  if(!E(_12h/* s18QY */.b)){
    var _12j/* s18Rp */ = B(_11z/* GHC.Integer.Type.integerLog2# */(_12f/* s18QW */));
    if(_12j/* s18Rp */<((_12i/* s18QZ */+_12d/* s18QU */|0)-1|0)){
      var _12k/* s18Ru */ = _12i/* s18QZ */+(_12d/* s18QU */-_12e/* s18QV */|0)|0;
      if(_12k/* s18Ru */>0){
        if(_12k/* s18Ru */>_12j/* s18Rp */){
          if(_12k/* s18Ru */<=(_12j/* s18Rp */+1|0)){
            if(!E(B(_11I/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_12f/* s18QW */)).b)){
              return 0;
            }else{
              return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(_10m/* GHC.Float.$fRealDouble1 */, _12d/* s18QU */-_12e/* s18QV */|0);});
            }
          }else{
            return 0;
          }
        }else{
          var _12l/* s18RI */ = B(_128/* GHC.Integer.Type.shiftRInteger */(_12f/* s18QW */, _12k/* s18Ru */));
          switch(B(_120/* GHC.Integer.Type.roundingMode# */(_12f/* s18QW */, _12k/* s18Ru */-1|0))){
            case 0:
              return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(_12l/* s18RI */, _12d/* s18QU */-_12e/* s18QV */|0);});
              break;
            case 1:
              if(!(B(_Vx/* GHC.Integer.Type.integerToInt */(_12l/* s18RI */))&1)){
                return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(_12l/* s18RI */, _12d/* s18QU */-_12e/* s18QV */|0);});
              }else{
                return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(B(_Km/* GHC.Integer.Type.plusInteger */(_12l/* s18RI */, _10m/* GHC.Float.$fRealDouble1 */)), _12d/* s18QU */-_12e/* s18QV */|0);});
              }
              break;
            default:
              return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(B(_Km/* GHC.Integer.Type.plusInteger */(_12l/* s18RI */, _10m/* GHC.Float.$fRealDouble1 */)), _12d/* s18QU */-_12e/* s18QV */|0);});
          }
        }
      }else{
        return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(_12f/* s18QW */, (_12d/* s18QU */-_12e/* s18QV */|0)-_12k/* s18Ru */|0);});
      }
    }else{
      if(_12j/* s18Rp */>=_12e/* s18QV */){
        var _12m/* s18RX */ = B(_128/* GHC.Integer.Type.shiftRInteger */(_12f/* s18QW */, (_12j/* s18Rp */+1|0)-_12e/* s18QV */|0));
        switch(B(_120/* GHC.Integer.Type.roundingMode# */(_12f/* s18QW */, _12j/* s18Rp */-_12e/* s18QV */|0))){
          case 0:
            return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(_12m/* s18RX */, ((_12j/* s18Rp */-_12i/* s18QZ */|0)+1|0)-_12e/* s18QV */|0);});
            break;
          case 2:
            return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(B(_Km/* GHC.Integer.Type.plusInteger */(_12m/* s18RX */, _10m/* GHC.Float.$fRealDouble1 */)), ((_12j/* s18Rp */-_12i/* s18QZ */|0)+1|0)-_12e/* s18QV */|0);});
            break;
          default:
            if(!(B(_Vx/* GHC.Integer.Type.integerToInt */(_12m/* s18RX */))&1)){
              return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(_12m/* s18RX */, ((_12j/* s18Rp */-_12i/* s18QZ */|0)+1|0)-_12e/* s18QV */|0);});
            }else{
              return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(B(_Km/* GHC.Integer.Type.plusInteger */(_12m/* s18RX */, _10m/* GHC.Float.$fRealDouble1 */)), ((_12j/* s18Rp */-_12i/* s18QZ */|0)+1|0)-_12e/* s18QV */|0);});
            }
        }
      }else{
        return new F(function(){return _10n/* GHC.Integer.Type.encodeDoubleInteger */(_12f/* s18QW */,  -_12i/* s18QZ */);});
      }
    }
  }else{
    var _12n/* s18R3 */ = B(_11z/* GHC.Integer.Type.integerLog2# */(_12f/* s18QW */))-_12i/* s18QZ */|0,
    _12o/* s18R4 */ = function(_12p/* s18R5 */){
      var _12q/* s18R6 */ = function(_12r/* s18R7 */, _12s/* s18R8 */){
        if(!B(_WH/* GHC.Integer.Type.leInteger */(B(_Kd/* GHC.Integer.Type.shiftLInteger */(_12s/* s18R8 */, _12e/* s18QV */)), _12r/* s18R7 */))){
          return new F(function(){return _10s/* GHC.Float.$w$j1 */(_12p/* s18R5 */-_12e/* s18QV */|0, _12r/* s18R7 */, _12s/* s18R8 */);});
        }else{
          return new F(function(){return _10s/* GHC.Float.$w$j1 */((_12p/* s18R5 */-_12e/* s18QV */|0)+1|0, _12r/* s18R7 */, B(_Kd/* GHC.Integer.Type.shiftLInteger */(_12s/* s18R8 */, 1)));});
        }
      };
      if(_12p/* s18R5 */>=_12e/* s18QV */){
        if(_12p/* s18R5 */!=_12e/* s18QV */){
          return new F(function(){return _12q/* s18R6 */(_12f/* s18QW */, new T(function(){
            return B(_Kd/* GHC.Integer.Type.shiftLInteger */(_12g/* s18QX */, _12p/* s18R5 */-_12e/* s18QV */|0));
          }));});
        }else{
          return new F(function(){return _12q/* s18R6 */(_12f/* s18QW */, _12g/* s18QX */);});
        }
      }else{
        return new F(function(){return _12q/* s18R6 */(new T(function(){
          return B(_Kd/* GHC.Integer.Type.shiftLInteger */(_12f/* s18QW */, _12e/* s18QV */-_12p/* s18R5 */|0));
        }), _12g/* s18QX */);});
      }
    };
    if(_12d/* s18QU */>_12n/* s18R3 */){
      return new F(function(){return _12o/* s18R4 */(_12d/* s18QU */);});
    }else{
      return new F(function(){return _12o/* s18R4 */(_12n/* s18R3 */);});
    }
  }
},
_12t/* rationalToDouble1 */ = new T(function(){
  return 0/0;
}),
_12u/* rationalToDouble2 */ = new T(function(){
  return -1/0;
}),
_12v/* rationalToDouble3 */ = new T(function(){
  return 1/0;
}),
_12w/* rationalToDouble4 */ = 0,
_12x/* rationalToDouble */ = function(_12y/* s197E */, _12z/* s197F */){
  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_12z/* s197F */, _10r/* GHC.Float.rationalToDouble5 */))){
    if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_12y/* s197E */, _10r/* GHC.Float.rationalToDouble5 */))){
      if(!B(_LB/* GHC.Integer.Type.ltInteger */(_12y/* s197E */, _10r/* GHC.Float.rationalToDouble5 */))){
        return new F(function(){return _12c/* GHC.Float.$w$sfromRat'' */(-1021, 53, _12y/* s197E */, _12z/* s197F */);});
      }else{
        return  -B(_12c/* GHC.Float.$w$sfromRat'' */(-1021, 53, B(_Kw/* GHC.Integer.Type.negateInteger */(_12y/* s197E */)), _12z/* s197F */));
      }
    }else{
      return E(_12w/* GHC.Float.rationalToDouble4 */);
    }
  }else{
    return (!B(_Ry/* GHC.Integer.Type.eqInteger */(_12y/* s197E */, _10r/* GHC.Float.rationalToDouble5 */))) ? (!B(_LB/* GHC.Integer.Type.ltInteger */(_12y/* s197E */, _10r/* GHC.Float.rationalToDouble5 */))) ? E(_12v/* GHC.Float.rationalToDouble3 */) : E(_12u/* GHC.Float.rationalToDouble2 */) : E(_12t/* GHC.Float.rationalToDouble1 */);
  }
},
_12A/* $fFractionalDouble_$cfromRational */ = function(_12B/* s197P */){
  var _12C/* s197Q */ = E(_12B/* s197P */);
  return new F(function(){return _12x/* GHC.Float.rationalToDouble */(_12C/* s197Q */.a, _12C/* s197Q */.b);});
},
_12D/* $fFractionalDouble_$crecip */ = function(_12E/* s191m */){
  return 1/E(_12E/* s191m */);
},
_12F/* $fNumDouble_$cabs */ = function(_12G/* s190N */){
  var _12H/* s190O */ = E(_12G/* s190N */),
  _12I/* s190Q */ = E(_12H/* s190O */);
  return (_12I/* s190Q */==0) ? E(_12w/* GHC.Float.rationalToDouble4 */) : (_12I/* s190Q */<=0) ?  -_12I/* s190Q */ : E(_12H/* s190O */);
},
_12J/* $fNumDouble_$cfromInteger */ = function(_12K/* s190E */){
  return new F(function(){return _Ta/* GHC.Integer.Type.doubleFromInteger */(_12K/* s190E */);});
},
_12L/* $fNumDouble1 */ = 1,
_12M/* $fNumDouble2 */ = -1,
_12N/* $fNumDouble_$csignum */ = function(_12O/* s190G */){
  var _12P/* s190H */ = E(_12O/* s190G */);
  return (_12P/* s190H */<=0) ? (_12P/* s190H */>=0) ? E(_12P/* s190H */) : E(_12M/* GHC.Float.$fNumDouble2 */) : E(_12L/* GHC.Float.$fNumDouble1 */);
},
_12Q/* minusDouble */ = function(_12R/* s18yR */, _12S/* s18yS */){
  return E(_12R/* s18yR */)-E(_12S/* s18yS */);
},
_12T/* $fNumDouble */ = {_:0,a:_tr/* GHC.Float.plusDouble */,b:_12Q/* GHC.Float.minusDouble */,c:_Aq/* GHC.Float.timesDouble */,d:_G5/* GHC.Float.negateDouble */,e:_12F/* GHC.Float.$fNumDouble_$cabs */,f:_12N/* GHC.Float.$fNumDouble_$csignum */,g:_12J/* GHC.Float.$fNumDouble_$cfromInteger */},
_12U/* $fFractionalDouble */ = new T4(0,_12T/* GHC.Float.$fNumDouble */,_iE/* GHC.Float.divideDouble */,_12D/* GHC.Float.$fFractionalDouble_$crecip */,_12A/* GHC.Float.$fFractionalDouble_$cfromRational */),
_12V/* $fEqDouble_$c/= */ = function(_12W/* scFX */, _12X/* scFY */){
  return (E(_12W/* scFX */)!=E(_12X/* scFY */)) ? true : false;
},
_12Y/* $fEqDouble_$c== */ = function(_12Z/* scFQ */, _130/* scFR */){
  return E(_12Z/* scFQ */)==E(_130/* scFR */);
},
_131/* $fEqDouble */ = new T2(0,_12Y/* GHC.Classes.$fEqDouble_$c== */,_12V/* GHC.Classes.$fEqDouble_$c/= */),
_132/* $fOrdDouble_$c< */ = function(_133/* scIa */, _134/* scIb */){
  return E(_133/* scIa */)<E(_134/* scIb */);
},
_135/* $fOrdDouble_$c<= */ = function(_136/* scI3 */, _137/* scI4 */){
  return E(_136/* scI3 */)<=E(_137/* scI4 */);
},
_138/* $fOrdDouble_$c> */ = function(_139/* scHW */, _13a/* scHX */){
  return E(_139/* scHW */)>E(_13a/* scHX */);
},
_13b/* $fOrdDouble_$c>= */ = function(_13c/* scHP */, _13d/* scHQ */){
  return E(_13c/* scHP */)>=E(_13d/* scHQ */);
},
_13e/* $fOrdDouble_$ccompare */ = function(_13f/* scIh */, _13g/* scIi */){
  var _13h/* scIj */ = E(_13f/* scIh */),
  _13i/* scIl */ = E(_13g/* scIi */);
  return (_13h/* scIj */>=_13i/* scIl */) ? (_13h/* scIj */!=_13i/* scIl */) ? 2 : 1 : 0;
},
_13j/* $fOrdDouble_$cmax */ = function(_13k/* scIz */, _13l/* scIA */){
  var _13m/* scIB */ = E(_13k/* scIz */),
  _13n/* scID */ = E(_13l/* scIA */);
  return (_13m/* scIB */>_13n/* scID */) ? E(_13m/* scIB */) : E(_13n/* scID */);
},
_13o/* $fOrdDouble_$cmin */ = function(_13p/* scIr */, _13q/* scIs */){
  var _13r/* scIt */ = E(_13p/* scIr */),
  _13s/* scIv */ = E(_13q/* scIs */);
  return (_13r/* scIt */>_13s/* scIv */) ? E(_13s/* scIv */) : E(_13r/* scIt */);
},
_13t/* $fOrdDouble */ = {_:0,a:_131/* GHC.Classes.$fEqDouble */,b:_13e/* GHC.Classes.$fOrdDouble_$ccompare */,c:_132/* GHC.Classes.$fOrdDouble_$c< */,d:_135/* GHC.Classes.$fOrdDouble_$c<= */,e:_138/* GHC.Classes.$fOrdDouble_$c> */,f:_13b/* GHC.Classes.$fOrdDouble_$c>= */,g:_13j/* GHC.Classes.$fOrdDouble_$cmax */,h:_13o/* GHC.Classes.$fOrdDouble_$cmin */},
_13u/* lvl8 */ = -1,
_13v/* $p1Fractional */ = function(_13w/* svdN */){
  return E(E(_13w/* svdN */).a);
},
_13x/* + */ = function(_13y/* s6Fy */){
  return E(E(_13y/* s6Fy */).a);
},
_13z/* $wnumericEnumFrom */ = function(_13A/* svLB */, _13B/* svLC */){
  var _13C/* svLD */ = E(_13B/* svLC */),
  _13D/* svLK */ = new T(function(){
    var _13E/* svLE */ = B(_13v/* GHC.Real.$p1Fractional */(_13A/* svLB */)),
    _13F/* svLH */ = B(_13z/* GHC.Real.$wnumericEnumFrom */(_13A/* svLB */, B(A3(_13x/* GHC.Num.+ */,_13E/* svLE */, _13C/* svLD */, new T(function(){
      return B(A2(_L3/* GHC.Num.fromInteger */,_13E/* svLE */, _KY/* GHC.Real.$fEnumRatio1 */));
    })))));
    return new T2(1,_13F/* svLH */.a,_13F/* svLH */.b);
  });
  return new T2(0,_13C/* svLD */,_13D/* svLK */);
},
_13G/* / */ = function(_13H/* svdT */){
  return E(E(_13H/* svdT */).b);
},
_13I/* <= */ = function(_13J/* scCl */){
  return E(E(_13J/* scCl */).d);
},
_13K/* takeWhile */ = function(_13L/* s9yw */, _13M/* s9yx */){
  var _13N/* s9yy */ = E(_13M/* s9yx */);
  if(!_13N/* s9yy */._){
    return __Z/* EXTERNAL */;
  }else{
    var _13O/* s9yz */ = _13N/* s9yy */.a;
    return (!B(A1(_13L/* s9yw */,_13O/* s9yz */))) ? __Z/* EXTERNAL */ : new T2(1,_13O/* s9yz */,new T(function(){
      return B(_13K/* GHC.List.takeWhile */(_13L/* s9yw */, _13N/* s9yy */.b));
    }));
  }
},
_13P/* numericEnumFromTo */ = function(_13Q/* svMm */, _13R/* svMn */, _13S/* svMo */, _13T/* svMp */){
  var _13U/* svMq */ = B(_13z/* GHC.Real.$wnumericEnumFrom */(_13R/* svMn */, _13S/* svMo */)),
  _13V/* svMt */ = new T(function(){
    var _13W/* svMu */ = B(_13v/* GHC.Real.$p1Fractional */(_13R/* svMn */)),
    _13X/* svMx */ = new T(function(){
      return B(A3(_13G/* GHC.Real./ */,_13R/* svMn */, new T(function(){
        return B(A2(_L3/* GHC.Num.fromInteger */,_13W/* svMu */, _KY/* GHC.Real.$fEnumRatio1 */));
      }), new T(function(){
        return B(A2(_L3/* GHC.Num.fromInteger */,_13W/* svMu */, _Sz/* GHC.Real.even2 */));
      })));
    });
    return B(A3(_13x/* GHC.Num.+ */,_13W/* svMu */, _13T/* svMp */, _13X/* svMx */));
  });
  return new F(function(){return _13K/* GHC.List.takeWhile */(function(_13Y/* svMy */){
    return new F(function(){return A3(_13I/* GHC.Classes.<= */,_13Q/* svMm */, _13Y/* svMy */, _13V/* svMt */);});
  }, new T2(1,_13U/* svMq */.a,_13U/* svMq */.b));});
},
_13Z/* x */ = 1,
_140/* lvl9 */ = new T(function(){
  return B(_13P/* GHC.Real.numericEnumFromTo */(_13t/* GHC.Classes.$fOrdDouble */, _12U/* GHC.Float.$fFractionalDouble */, _13u/* Motion.Change.lvl8 */, _13Z/* Motion.Change.x */));
}),
_141/* go */ = function(_142/* s826 */){
  var _143/* s827 */ = E(_142/* s826 */);
  if(!_143/* s827 */._){
    return __Z/* EXTERNAL */;
  }else{
    var _144/* s82a */ = new T(function(){
      return E(_143/* s827 */.a)*100;
    }),
    _145/* s82e */ = new T(function(){
      return B(_141/* Motion.Change.go */(_143/* s827 */.b));
    }),
    _146/* s82f */ = function(_147/* s82g */){
      var _148/* s82h */ = E(_147/* s82g */);
      return (_148/* s82h */._==0) ? E(_145/* s82e */) : new T2(1,new T2(0,_144/* s82a */,new T(function(){
        return E(_148/* s82h */.a)*100;
      })),new T(function(){
        return B(_146/* s82f */(_148/* s82h */.b));
      }));
    };
    return new F(function(){return _146/* s82f */(_140/* Motion.Change.lvl9 */);});
  }
},
_149/* lvl10 */ = new T(function(){
  return B(_141/* Motion.Change.go */(_140/* Motion.Change.lvl9 */));
}),
_14a/* lvl11 */ = 1.5,
_14b/* lvl12 */ = 15,
_14c/* lvl13 */ = 50,
_14d/* lvl14 */ = 100,
_14e/* lvl15 */ = new T4(0,_13Z/* Motion.Change.x */,_13Z/* Motion.Change.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_14f/* lvl16 */ = new T2(0,_13Z/* Motion.Change.x */,_14e/* Motion.Change.lvl15 */),
_14g/* lvl17 */ = new T2(0,_14f/* Motion.Change.lvl16 */,_6/* GHC.Types.[] */),
_14h/* a8 */ = 100,
_14i/* lvl5 */ = new T1(0,_14h/* Motion.Change.a8 */),
_14j/* lvl6 */ = new T2(0,_14i/* Motion.Change.lvl5 */,_14i/* Motion.Change.lvl5 */),
_14k/* a9 */ = 3,
_14l/* lvl7 */ = new T1(0,_14k/* Motion.Change.a9 */),
_14m/* valueIO1 */ = function(_14n/* sb7c */, _/* EXTERNAL */){
  var _14o/* sb7e */ = E(_14n/* sb7c */);
  switch(_14o/* sb7e */._){
    case 0:
      return new T1(1,_14o/* sb7e */.a);
    case 1:
      var _14p/* sb7i */ = B(A1(_14o/* sb7e */.a,_/* EXTERNAL */));
      return new T1(1,_14p/* sb7i */);
    case 2:
      var _14q/* sb7u */ = rMV/* EXTERNAL */(E(E(_14o/* sb7e */.a).c)),
      _14r/* sb7x */ = E(_14q/* sb7u */);
      if(!_14r/* sb7x */._){
        var _14s/* sb7B */ = new T(function(){
          return B(A1(_14o/* sb7e */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_14r/* sb7x */.a));
          })));
        });
        return new T1(1,_14s/* sb7B */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
      break;
    default:
      var _14t/* sb7M */ = rMV/* EXTERNAL */(E(E(_14o/* sb7e */.a).c)),
      _14u/* sb7P */ = E(_14t/* sb7M */);
      if(!_14u/* sb7P */._){
        var _14v/* sb7V */ = B(A2(_14o/* sb7e */.b,E(_14u/* sb7P */.a).a, _/* EXTERNAL */));
        return new T1(1,_14v/* sb7V */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
  }
},
_14w/* changeMot1 */ = function(_14x/* s83d */, _14y/* s83e */){
  var _14z/* s83f */ = new T(function(){
    return B(_Z4/* Motion.Change.$sreplicateM2 */(_10h/* Motion.Change.a7 */, _14y/* s83e */));
  }),
  _14A/* s83g */ = function(_14B/* s83h */, _14C/* s83i */){
    var _14D/* s83j */ = E(_14B/* s83h */);
    if(!_14D/* s83j */._){
      return E(_104/* Motion.Change.a2 */);
    }else{
      var _14E/* s83m */ = E(_14C/* s83i */);
      if(!_14E/* s83m */._){
        return E(_104/* Motion.Change.a2 */);
      }else{
        var _14F/* s83p */ = E(_14E/* s83m */.a),
        _14G/* s83s */ = new T(function(){
          return B(_Is/* Core.Ease.morph */(_14D/* s83j */.a));
        }),
        _14H/* s83v */ = B(_rx/* Control.Monad.Skeleton.bone */(new T1(1,function(_/* EXTERNAL */){
          return new F(function(){return _14m/* Core.Ease.valueIO1 */(_14G/* s83s */, _/* EXTERNAL */);});
        }))),
        _14I/* s83y */ = new T(function(){
          return B(_14A/* s83g */(_14D/* s83j */.b, _14E/* s83m */.b));
        }),
        _14J/* s83z */ = new T(function(){
          return B(_rB/* Core.Render.Internal.fill1 */(_14x/* s83d */, new T(function(){
            var _14K/* s83C */ = B(_GQ/* Core.Shape.Internal.$wcenterRect */(new T1(0,_14F/* s83p */.a), new T1(0,_14F/* s83p */.b), _14i/* Motion.Change.lvl5 */, _14i/* Motion.Change.lvl5 */));
            return new T3(0,_14K/* s83C */.a,_14K/* s83C */.b,_14K/* s83C */.c);
          })));
        });
        return new T2(0,E(_14H/* s83v */.a),E(new T2(2,new T2(2,_14H/* s83v */.b,new T1(1,function(_14L/* s83H */){
          var _14M/* s83I */ = E(_14L/* s83H */);
          return (_14M/* s83I */._==0) ? E(_Zj/* Motion.Change.$swhen1 */) : (!E(_14M/* s83I */.a)) ? E(_Zj/* Motion.Change.$swhen1 */) : E(_14J/* s83z */);
        })),new T1(1,function(_14N/* s83O */){
          return E(_14I/* s83y */);
        }))));
      }
    }
  },
  _14O/* s85x */ = function(_14P/* s83S */){
    var _14Q/* s85w */ = function(_14R/* s83T */){
      var _14S/* s83U */ = E(_14R/* s83T */),
      _14T/* s83V */ = _14S/* s83U */.a,
      _14U/* s85v */ = function(_/* EXTERNAL */){
        var _14V/* s83Y */ = nMV/* EXTERNAL */(_14g/* Motion.Change.lvl17 */);
        return new T(function(){
          var _14W/* s842 */ = new T(function(){
            return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _10i/* Motion.Change.dur */, _10j/* Motion.Change.e */, _14V/* s83Y */, _13Z/* Motion.Change.x */, _Ac/* Core.Ease.easeTo1 */));
          }),
          _14X/* s843 */ = new T(function(){
            return B(_jN/* Core.Ease.$wforceTo */(_14V/* s83Y */, _14a/* Motion.Change.lvl11 */));
          }),
          _14Y/* s844 */ = function(_14Z/* s845 */, _150/* s846 */){
            var _151/* s847 */ = function(_152/* s848 */){
              return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_14b/* Motion.Change.lvl12 */, E(_152/* s848 */).b, _150/* s846 */);});
            },
            _153/* s84c */ = function(_154/* s84d */){
              return new F(function(){return A2(_14W/* s842 */,E(_154/* s84d */).b, _151/* s847 */);});
            };
            return new F(function(){return _ZK/* Motion.Change.a10 */(_14T/* s83V */, _14Z/* s845 */, function(_155/* s84h */){
              return new F(function(){return A2(_14X/* s843 */,E(_155/* s84h */).b, _153/* s84c */);});
            });});
          },
          _156/* s84m */ = new T(function(){
            var _157/* s84o */ = function(_158/* s84p */){
              var _159/* s84q */ = E(_158/* s84p */);
              return (_159/* s84q */==1) ? E(new T2(1,_14Y/* s844 */,_6/* GHC.Types.[] */)) : new T2(1,_14Y/* s844 */,new T(function(){
                return B(_157/* s84o */(_159/* s84q */-1|0));
              }));
            };
            return B(_157/* s84o */(4));
          }),
          _15a/* s84t */ = function(_15b/* s84u */){
            var _15c/* s84v */ = new T(function(){
              return B(_Z4/* Motion.Change.$sreplicateM2 */(_156/* s84m */, _15b/* s84u */));
            }),
            _15d/* s85g */ = function(_15e/* s84w */){
              var _15f/* s84x */ = function(_15g/* s84y */){
                return new F(function(){return A2(_15a/* s84t */,E(_15g/* s84y */).b, _15e/* s84w */);});
              },
              _15h/* s84C */ = function(_15i/* s84D */){
                return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_14d/* Motion.Change.lvl14 */, E(_15i/* s84D */).b, _15f/* s84x */);});
              },
              _15j/* s84H */ = function(_15k/* s84I */){
                return new F(function(){return A2(_14W/* s842 */,E(_15k/* s84I */).b, _15h/* s84C */);});
              },
              _15l/* s84M */ = function(_15m/* s84N */){
                return new F(function(){return A2(_14X/* s843 */,E(_15m/* s84N */).b, _15j/* s84H */);});
              },
              _15n/* s84R */ = function(_15o/* s84S */){
                return new F(function(){return _ZK/* Motion.Change.a10 */(_14T/* s83V */, E(_15o/* s84S */).b, _15l/* s84M */);});
              },
              _15p/* s84W */ = function(_15q/* s84X */){
                return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_14c/* Motion.Change.lvl13 */, E(_15q/* s84X */).b, _15n/* s84R */);});
              },
              _15r/* s851 */ = function(_15s/* s852 */){
                return new F(function(){return A2(_14W/* s842 */,E(_15s/* s852 */).b, _15p/* s84W */);});
              },
              _15t/* s856 */ = function(_15u/* s857 */){
                return new F(function(){return A2(_14X/* s843 */,E(_15u/* s857 */).b, _15r/* s851 */);});
              };
              return new F(function(){return A1(_15c/* s84v */,function(_15v/* s85b */){
                return new F(function(){return _ZK/* Motion.Change.a10 */(_14T/* s83V */, E(_15v/* s85b */).b, _15t/* s856 */);});
              });});
            };
            return E(_15d/* s85g */);
          },
          _15w/* s85r */ = new T(function(){
            var _15x/* s85p */ = new T(function(){
              var _15y/* s85h */ = new T3(0,_10i/* Motion.Change.dur */,_10j/* Motion.Change.e */,_14V/* s83Y */);
              return B(_rx/* Control.Monad.Skeleton.bone */(new T3(7,new T2(0,new T(function(){
                return B(_sg/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, new T2(2,_15y/* s85h */,_2E/* GHC.Base.id */), _14l/* Motion.Change.lvl7 */));
              }),new T(function(){
                return B(_sg/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, new T2(2,_15y/* s85h */,_2E/* GHC.Base.id */), _14l/* Motion.Change.lvl7 */));
              })),new T(function(){
                return B(_14A/* s83g */(_14T/* s83V */, _149/* Motion.Change.lvl10 */));
              }),_7/* GHC.Tuple.() */)));
            });
            return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_14j/* Motion.Change.lvl6 */,_15x/* s85p */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_14P/* s83S */,new T2(0,new T2(0,_15w/* s85r */,_15a/* s84t */),_14S/* s83U */.b)));
        });
      };
      return new T1(0,_14U/* s85v */);
    };
    return new F(function(){return A1(_14z/* s83f */,_14Q/* s85w */);});
  };
  return E(_14O/* s85x */);
},
_15z/* lvl54 */ = 0.1,
_15A/* lvl55 */ = new T1(0,_15z/* Motion.Main.lvl54 */),
_15B/* lvl56 */ = new T4(0,_15A/* Motion.Main.lvl55 */,_Jl/* Motion.Main.lvl45 */,_Jl/* Motion.Main.lvl45 */,_Al/* Motion.Main.lvl11 */),
_15C/* lvl57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Change"));
}),
_15D/* lvl58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("easeOutExpo"));
}),
_15E/* lvl59 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_15B/* Motion.Main.lvl56 */, _14w/* Motion.Change.changeMot1 */, _15C/* Motion.Main.lvl57 */, _15D/* Motion.Main.lvl58 */));
}),
_15F/* lvl60 */ = new T4(0,_Al/* Motion.Main.lvl11 */,_AC/* Motion.Main.lvl23 */,_yT/* Motion.Main.lvl4 */,_Al/* Motion.Main.lvl11 */),
_15G/* lvl61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Trot"));
}),
_15H/* lvl62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("rotateAt corner easeInCubic & smoothStep scroll"));
}),
_15I/* cubic */ = function(_15J/* sbes */, _15K/* sbet */){
  var _15L/* sbeu */ = B(A1(_15J/* sbes */,_15K/* sbet */));
  return _15L/* sbeu */*_15L/* sbeu */*_15L/* sbeu */;
},
_15M/* dur */ = 40,
_15N/* $we */ = function(_15O/* s6Uc */, _15P/* s6Ud */){
  if(_15P/* s6Ud */>=0.5){
    var _15Q/* s6Ug */ = 2-(_15P/* s6Ud */+_15P/* s6Ud */);
    return 1-B(A1(_15O/* s6Uc */,_15Q/* s6Ug */*_15Q/* s6Ug */*(3-_15Q/* s6Ug */)/2))/2;
  }else{
    var _15R/* s6Uq */ = _15P/* s6Ud */+_15P/* s6Ud */;
    return B(A1(_15O/* s6Uc */,_15R/* s6Uq */*_15R/* s6Uq */*(3-_15R/* s6Uq */)/2))/2;
  }
},
_15S/* e */ = function(_15T/* s6Uy */, _15U/* s6Uz */){
  return new F(function(){return _15N/* Motion.Trot.$we */(_15T/* s6Uy */, E(_15U/* s6Uz */));});
},
_15V/* x */ = 0,
_15W/* lvl */ = new T1(0,_15V/* Motion.Trot.x */),
_15X/* lvl10 */ = -100,
_15Y/* lvl11 */ = new T1(0,_15X/* Motion.Trot.lvl10 */),
_15Z/* lvl12 */ = -200,
_160/* lvl13 */ = new T1(0,_15Z/* Motion.Trot.lvl12 */),
_161/* lvl14 */ = new T2(0,_15Y/* Motion.Trot.lvl11 */,_160/* Motion.Trot.lvl13 */),
_162/* lvl15 */ = new T4(0,_15V/* Motion.Trot.x */,_15V/* Motion.Trot.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_163/* lvl16 */ = new T2(0,_15V/* Motion.Trot.x */,_162/* Motion.Trot.lvl15 */),
_164/* lvl17 */ = new T2(0,_163/* Motion.Trot.lvl16 */,_6/* GHC.Types.[] */),
_165/* a3 */ = 25,
_166/* lvl3 */ = new T1(0,_165/* Motion.Trot.a3 */),
_167/* a4 */ = 125,
_168/* lvl4 */ = new T1(0,_167/* Motion.Trot.a4 */),
_169/* a5 */ = 75,
_16a/* lvl5 */ = new T1(0,_169/* Motion.Trot.a5 */),
_16b/* lvl6 */ = new T(function(){
  var _16c/* s6UD */ = B(_kB/* Core.Shape.Internal.$wrect */(_166/* Motion.Trot.lvl3 */, _168/* Motion.Trot.lvl4 */, _16a/* Motion.Trot.lvl5 */, _16a/* Motion.Trot.lvl5 */));
  return new T3(0,_16c/* s6UD */.a,_16c/* s6UD */.b,_16c/* s6UD */.c);
}),
_16d/* lvl7 */ = 1.5707963267948966,
_16e/* lvl8 */ = -75,
_16f/* a1 */ = 100,
_16g/* lvl1 */ = new T1(0,_16f/* Motion.Trot.a1 */),
_16h/* a2 */ = 200,
_16i/* lvl2 */ = new T1(0,_16h/* Motion.Trot.a2 */),
_16j/* lvl9 */ = new T2(0,_16g/* Motion.Trot.lvl1 */,_16i/* Motion.Trot.lvl2 */),
_16k/* trotMot */ = function(_16l/* s6UH */){
  var _16m/* s6UI */ = new T(function(){
    return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_161/* Motion.Trot.lvl14 */,new T(function(){
      return B(_rB/* Core.Render.Internal.fill1 */(_16l/* s6UH */, _16b/* Motion.Trot.lvl6 */));
    }),_7/* GHC.Tuple.() */)));
  }),
  _16n/* s6VR */ = function(_16o/* s6UL */, _16p/* s6UM */){
    var _16q/* s6VQ */ = function(_/* EXTERNAL */){
      var _16r/* s6UO */ = nMV/* EXTERNAL */(_164/* Motion.Trot.lvl17 */),
      _16s/* s6UQ */ = _16r/* s6UO */,
      _16t/* s6US */ = new T(function(){
        return B(_jN/* Core.Ease.$wforceTo */(_16s/* s6UQ */, _15V/* Motion.Trot.x */));
      }),
      _16u/* s6UT */ = function(_16v/* s6UU */){
        return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _15M/* Motion.Trot.dur */, _15I/* Core.Ease.cubic */, _16s/* s6UQ */, _16d/* Motion.Trot.lvl7 */, function(_16w/* s6UV */){
          return E(_16v/* s6UU */);
        });});
      },
      _16x/* s6VO */ = function(_/* EXTERNAL */){
        var _16y/* s6UY */ = nMV/* EXTERNAL */(_164/* Motion.Trot.lvl17 */),
        _16z/* s6V0 */ = _16y/* s6UY */;
        return new T(function(){
          var _16A/* s6V2 */ = new T(function(){
            return B(_jN/* Core.Ease.$wforceTo */(_16z/* s6V0 */, _15V/* Motion.Trot.x */));
          }),
          _16B/* s6V3 */ = function(_16C/* s6V4 */){
            return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _15M/* Motion.Trot.dur */, _15S/* Motion.Trot.e */, _16z/* s6V0 */, _16e/* Motion.Trot.lvl8 */, function(_16D/* s6V5 */){
              return E(_16C/* s6V4 */);
            });});
          },
          _16E/* s6V7 */ = function(_16F/* s6V8 */){
            var _16G/* s6V9 */ = new T(function(){
              return B(A1(_16t/* s6US */,_16F/* s6V8 */));
            }),
            _16H/* s6Vz */ = function(_16I/* s6Va */){
              var _16J/* s6Vb */ = function(_16K/* s6Vc */){
                return new F(function(){return A2(_16E/* s6V7 */,E(_16K/* s6Vc */).b, _16I/* s6Va */);});
              },
              _16L/* s6Vg */ = function(_16M/* s6Vh */){
                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_16B/* s6V3 */, E(_16M/* s6Vh */).b, _16J/* s6Vb */)));
              },
              _16N/* s6Vn */ = function(_16O/* s6Vo */){
                return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_16u/* s6UT */, E(_16O/* s6Vo */).b, _16L/* s6Vg */)));
              };
              return new F(function(){return A1(_16G/* s6V9 */,function(_16P/* s6Vu */){
                return new F(function(){return A2(_16A/* s6V2 */,E(_16P/* s6Vu */).b, _16N/* s6Vn */);});
              });});
            };
            return E(_16H/* s6Vz */);
          },
          _16Q/* s6VK */ = new T(function(){
            var _16R/* s6VI */ = new T(function(){
              return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_16j/* Motion.Trot.lvl9 */,new T(function(){
                return B(_rx/* Control.Monad.Skeleton.bone */(new T3(6,new T2(2,new T3(0,_15M/* Motion.Trot.dur */,_15I/* Core.Ease.cubic */,_16s/* s6UQ */),_2E/* GHC.Base.id */),_16m/* s6UI */,_7/* GHC.Tuple.() */)));
              }),_7/* GHC.Tuple.() */)));
            });
            return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,new T2(2,new T3(0,_15M/* Motion.Trot.dur */,_15S/* Motion.Trot.e */,_16z/* s6V0 */),_2E/* GHC.Base.id */),_15W/* Motion.Trot.lvl */),_16R/* s6VI */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_16p/* s6UM */,new T2(0,new T2(0,_16Q/* s6VK */,_16E/* s6V7 */),_16o/* s6UL */)));
        });
      };
      return new T1(0,_16x/* s6VO */);
    };
    return new T1(0,_16q/* s6VQ */);
  };
  return E(_16n/* s6VR */);
},
_16S/* lvl63 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_15F/* Motion.Main.lvl60 */, _16k/* Motion.Trot.trotMot */, _15G/* Motion.Main.lvl61 */, _15H/* Motion.Main.lvl62 */));
}),
_16T/* lvl64 */ = new T4(0,_Al/* Motion.Main.lvl11 */,_yT/* Motion.Main.lvl4 */,_Az/* Motion.Main.lvl21 */,_Al/* Motion.Main.lvl11 */),
_16U/* lvl65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resist"));
}),
_16V/* lvl66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("easeOutExpo & Randomness & Vel/Acc model"));
}),
_16W/* . */ = function(_16X/* s3ay */, _16Y/* s3az */, _16Z/* s3aA */){
  return new F(function(){return A1(_16X/* s3ay */,new T(function(){
    return B(A1(_16Y/* s3az */,_16Z/* s3aA */));
  }));});
},
_170/* $fFloatingValue_$cfmap */ = function(_171/* sb0f */, _172/* sb0g */){
  var _173/* sb0h */ = E(_172/* sb0g */);
  switch(_173/* sb0h */._){
    case 0:
      return new T1(0,new T(function(){
        return B(A1(_171/* sb0f */,_173/* sb0h */.a));
      }));
    case 1:
      return new T1(1,function(_/* EXTERNAL */){
        return new F(function(){return _x/* GHC.Base.$fFunctorIO2 */(_171/* sb0f */, _173/* sb0h */.a, _/* EXTERNAL */);});
      });
    case 2:
      return new T2(2,_173/* sb0h */.a,function(_Af/* B1 */){
        return new F(function(){return _16W/* GHC.Base.. */(_171/* sb0f */, _173/* sb0h */.b, _Af/* B1 */);});
      });
    default:
      var _174/* sb0x */ = function(_175/* sb0r */, _/* EXTERNAL */){
        var _176/* sb0t */ = B(A2(_173/* sb0h */.b,_175/* sb0r */, _/* EXTERNAL */));
        return new T(function(){
          return B(A1(_171/* sb0f */,_176/* sb0t */));
        });
      };
      return new T2(3,_173/* sb0h */.a,_174/* sb0x */);
  }
},
_177/* a11 */ = 0,
_178/* a */ = new T1(0,_/* EXTERNAL */),
_179/* a1 */ = new T1(0,_7/* GHC.Tuple.() */),
_17a/* a2 */ = new T2(0,E(_179/* Motion.Resist.a1 */),E(_178/* Motion.Resist.a */)),
_17b/* a5 */ = 1,
_17c/* lvl7 */ = -2.0e-2,
_17d/* lvl8 */ = 2.0e-2,
_17e/* lvl9 */ = new T2(0,_17c/* Motion.Resist.lvl7 */,_17d/* Motion.Resist.lvl8 */),
_17f/* lvl10 */ = function(_/* EXTERNAL */){
  return new F(function(){return _Yc/* System.Random.$fRandomDouble8 */(_17e/* Motion.Resist.lvl9 */, _/* EXTERNAL */);});
},
_17g/* lvl11 */ = new T1(1,_17f/* Motion.Resist.lvl10 */),
_17h/* a9 */ = new T(function(){
  return B(_rx/* Control.Monad.Skeleton.bone */(_17g/* Motion.Resist.lvl11 */));
}),
_17i/* dur */ = 100,
_17j/* dur1 */ = 80,
_17k/* e */ = function(_17l/* si1R */, _17m/* si1S */){
  return 1-B(A1(_17l/* si1R */,new T(function(){
    return Math.pow/* EXTERNAL */(2,  -((1-(1-E(_17m/* si1S */)))*10));
  })));
},
_17n/* hPutStrLn2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_17o/* jshWrite1 */ = function(_17p/* s4GFX */, _17q/* s4GFY */, _/* EXTERNAL */){
  var _17r/* s4GG8 */ = jsWriteHandle/* EXTERNAL */(E(_17p/* s4GFX */), toJSStr/* EXTERNAL */(E(_17q/* s4GFY */)));
  return _7/* GHC.Tuple.() */;
},
_17s/* hPutStrLn1 */ = function(_17t/* s5hMY */, _17u/* s5hMZ */, _/* EXTERNAL */){
  var _17v/* s5hN1 */ = E(_17t/* s5hMY */),
  _17w/* s5hN9 */ = jsWriteHandle/* EXTERNAL */(_17v/* s5hN1 */, toJSStr/* EXTERNAL */(E(_17u/* s5hMZ */)));
  return new F(function(){return _17o/* Haste.Handle.jshWrite1 */(_17v/* s5hN1 */, _17n/* GHC.IO.Handle.Text.hPutStrLn2 */, _/* EXTERNAL */);});
},
_17x/* lvl */ = new T1(0,_17b/* Motion.Resist.a5 */),
_17y/* a6 */ = 2,
_17z/* lvl1 */ = new T1(0,_17y/* Motion.Resist.a6 */),
_17A/* x */ = 0,
_17B/* lvl12 */ = new T1(0,_17A/* Motion.Resist.x */),
_17C/* a10 */ = -40,
_17D/* lvl13 */ = new T1(0,_17C/* Motion.Resist.a10 */),
_17E/* lvl14 */ = new T2(0,_17B/* Motion.Resist.lvl12 */,_17D/* Motion.Resist.lvl13 */),
_17F/* lvl15 */ = new T1(0,0),
_17G/* lvl16 */ = 0.3,
_17H/* lvl17 */ = 20,
_17I/* lvl18 */ = -5.0e-2,
_17J/* a7 */ = 40,
_17K/* lvl2 */ = new T1(0,_17J/* Motion.Resist.a7 */),
_17L/* lvl19 */ = new T1(0,100),
_17M/* lvl4 */ = new T1(0,1),
_17N/* lvl20 */ = new T(function(){
  return B(_Vi/* GHC.Enum.enumDeltaToInteger */(_17F/* Motion.Resist.lvl15 */, _17M/* Motion.Resist.lvl4 */, _17L/* Motion.Resist.lvl19 */));
}),
_17O/* lvl21 */ = function(_17P/* si24 */){
  var _17Q/* si25 */ = E(_17P/* si24 */);
  return (_17Q/* si25 */<=0) ? (_17Q/* si25 */>=0) ? E(_17Q/* si25 */) : E(_12M/* GHC.Float.$fNumDouble2 */) : E(_12L/* GHC.Float.$fNumDouble1 */);
},
_17R/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po8"));
}),
_17S/* shows5 */ = 34,
_17T/* lvl23 */ = new T2(1,_17S/* GHC.Show.shows5 */,_6/* GHC.Types.[] */),
_17U/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: negative index"));
}),
_17V/* lvl2 */ = new T(function(){
  return B(_2/* GHC.Base.++ */(_Ns/* GHC.List.prel_list_str */, _17U/* GHC.List.lvl1 */));
}),
_17W/* negIndex */ = new T(function(){
  return B(err/* EXTERNAL */(_17V/* GHC.List.lvl2 */));
}),
_17X/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: index too large"));
}),
_17Y/* lvl4 */ = new T(function(){
  return B(_2/* GHC.Base.++ */(_Ns/* GHC.List.prel_list_str */, _17X/* GHC.List.lvl3 */));
}),
_17Z/* !!1 */ = new T(function(){
  return B(err/* EXTERNAL */(_17Y/* GHC.List.lvl4 */));
}),
_180/* poly_$wgo2 */ = function(_181/* s9uX */, _182/* s9uY */){
  while(1){
    var _183/* s9uZ */ = E(_181/* s9uX */);
    if(!_183/* s9uZ */._){
      return E(_17Z/* GHC.List.!!1 */);
    }else{
      var _184/* s9v2 */ = E(_182/* s9uY */);
      if(!_184/* s9v2 */){
        return E(_183/* s9uZ */.a);
      }else{
        _181/* s9uX */ = _183/* s9uZ */.b;
        _182/* s9uY */ = _184/* s9v2 */-1|0;
        continue;
      }
    }
  }
},
_185/* $w!! */ = function(_186/* s9v4 */, _187/* s9v5 */){
  if(_187/* s9v5 */>=0){
    return new F(function(){return _180/* GHC.List.poly_$wgo2 */(_186/* s9v4 */, _187/* s9v5 */);});
  }else{
    return E(_17W/* GHC.List.negIndex */);
  }
},
_188/* asciiTab59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_189/* asciiTab58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_18a/* asciiTab57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_18b/* asciiTab33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_18c/* asciiTab32 */ = new T2(1,_18b/* GHC.Show.asciiTab33 */,_6/* GHC.Types.[] */),
_18d/* asciiTab34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_18e/* asciiTab31 */ = new T2(1,_18d/* GHC.Show.asciiTab34 */,_18c/* GHC.Show.asciiTab32 */),
_18f/* asciiTab35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_18g/* asciiTab30 */ = new T2(1,_18f/* GHC.Show.asciiTab35 */,_18e/* GHC.Show.asciiTab31 */),
_18h/* asciiTab36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_18i/* asciiTab29 */ = new T2(1,_18h/* GHC.Show.asciiTab36 */,_18g/* GHC.Show.asciiTab30 */),
_18j/* asciiTab37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_18k/* asciiTab28 */ = new T2(1,_18j/* GHC.Show.asciiTab37 */,_18i/* GHC.Show.asciiTab29 */),
_18l/* asciiTab38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_18m/* asciiTab27 */ = new T2(1,_18l/* GHC.Show.asciiTab38 */,_18k/* GHC.Show.asciiTab28 */),
_18n/* asciiTab39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_18o/* asciiTab26 */ = new T2(1,_18n/* GHC.Show.asciiTab39 */,_18m/* GHC.Show.asciiTab27 */),
_18p/* asciiTab40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_18q/* asciiTab25 */ = new T2(1,_18p/* GHC.Show.asciiTab40 */,_18o/* GHC.Show.asciiTab26 */),
_18r/* asciiTab41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_18s/* asciiTab24 */ = new T2(1,_18r/* GHC.Show.asciiTab41 */,_18q/* GHC.Show.asciiTab25 */),
_18t/* asciiTab42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_18u/* asciiTab23 */ = new T2(1,_18t/* GHC.Show.asciiTab42 */,_18s/* GHC.Show.asciiTab24 */),
_18v/* asciiTab43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_18w/* asciiTab22 */ = new T2(1,_18v/* GHC.Show.asciiTab43 */,_18u/* GHC.Show.asciiTab23 */),
_18x/* asciiTab44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_18y/* asciiTab21 */ = new T2(1,_18x/* GHC.Show.asciiTab44 */,_18w/* GHC.Show.asciiTab22 */),
_18z/* asciiTab45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_18A/* asciiTab20 */ = new T2(1,_18z/* GHC.Show.asciiTab45 */,_18y/* GHC.Show.asciiTab21 */),
_18B/* asciiTab46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_18C/* asciiTab19 */ = new T2(1,_18B/* GHC.Show.asciiTab46 */,_18A/* GHC.Show.asciiTab20 */),
_18D/* asciiTab47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_18E/* asciiTab18 */ = new T2(1,_18D/* GHC.Show.asciiTab47 */,_18C/* GHC.Show.asciiTab19 */),
_18F/* asciiTab48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_18G/* asciiTab17 */ = new T2(1,_18F/* GHC.Show.asciiTab48 */,_18E/* GHC.Show.asciiTab18 */),
_18H/* asciiTab49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_18I/* asciiTab16 */ = new T2(1,_18H/* GHC.Show.asciiTab49 */,_18G/* GHC.Show.asciiTab17 */),
_18J/* asciiTab50 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_18K/* asciiTab15 */ = new T2(1,_18J/* GHC.Show.asciiTab50 */,_18I/* GHC.Show.asciiTab16 */),
_18L/* asciiTab51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_18M/* asciiTab14 */ = new T2(1,_18L/* GHC.Show.asciiTab51 */,_18K/* GHC.Show.asciiTab15 */),
_18N/* asciiTab52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_18O/* asciiTab13 */ = new T2(1,_18N/* GHC.Show.asciiTab52 */,_18M/* GHC.Show.asciiTab14 */),
_18P/* asciiTab53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_18Q/* asciiTab12 */ = new T2(1,_18P/* GHC.Show.asciiTab53 */,_18O/* GHC.Show.asciiTab13 */),
_18R/* asciiTab54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_18S/* asciiTab11 */ = new T2(1,_18R/* GHC.Show.asciiTab54 */,_18Q/* GHC.Show.asciiTab12 */),
_18T/* asciiTab55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_18U/* asciiTab10 */ = new T2(1,_18T/* GHC.Show.asciiTab55 */,_18S/* GHC.Show.asciiTab11 */),
_18V/* asciiTab56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_18W/* asciiTab9 */ = new T2(1,_18V/* GHC.Show.asciiTab56 */,_18U/* GHC.Show.asciiTab10 */),
_18X/* asciiTab8 */ = new T2(1,_18a/* GHC.Show.asciiTab57 */,_18W/* GHC.Show.asciiTab9 */),
_18Y/* asciiTab7 */ = new T2(1,_189/* GHC.Show.asciiTab58 */,_18X/* GHC.Show.asciiTab8 */),
_18Z/* asciiTab6 */ = new T2(1,_188/* GHC.Show.asciiTab59 */,_18Y/* GHC.Show.asciiTab7 */),
_190/* asciiTab60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_191/* asciiTab5 */ = new T2(1,_190/* GHC.Show.asciiTab60 */,_18Z/* GHC.Show.asciiTab6 */),
_192/* asciiTab61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_193/* asciiTab4 */ = new T2(1,_192/* GHC.Show.asciiTab61 */,_191/* GHC.Show.asciiTab5 */),
_194/* asciiTab62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_195/* asciiTab3 */ = new T2(1,_194/* GHC.Show.asciiTab62 */,_193/* GHC.Show.asciiTab4 */),
_196/* asciiTab63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_197/* asciiTab2 */ = new T2(1,_196/* GHC.Show.asciiTab63 */,_195/* GHC.Show.asciiTab3 */),
_198/* asciiTab64 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_199/* asciiTab1 */ = new T2(1,_198/* GHC.Show.asciiTab64 */,_197/* GHC.Show.asciiTab2 */),
_19a/* asciiTab65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_19b/* asciiTab */ = new T2(1,_19a/* GHC.Show.asciiTab65 */,_199/* GHC.Show.asciiTab1 */),
_19c/* lvl */ = 92,
_19d/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\DEL"));
}),
_19e/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\a"));
}),
_19f/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\\"));
}),
_19g/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\SO"));
}),
_19h/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\r"));
}),
_19i/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\f"));
}),
_19j/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\v"));
}),
_19k/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\n"));
}),
_19l/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\t"));
}),
_19m/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\b"));
}),
_19n/* $wshowLitChar */ = function(_19o/* sfem */, _19p/* sfen */){
  if(_19o/* sfem */<=127){
    var _19q/* sfeq */ = E(_19o/* sfem */);
    switch(_19q/* sfeq */){
      case 92:
        return new F(function(){return _2/* GHC.Base.++ */(_19f/* GHC.Show.lvl2 */, _19p/* sfen */);});
        break;
      case 127:
        return new F(function(){return _2/* GHC.Base.++ */(_19d/* GHC.Show.lvl1 */, _19p/* sfen */);});
        break;
      default:
        if(_19q/* sfeq */<32){
          var _19r/* sfet */ = E(_19q/* sfeq */);
          switch(_19r/* sfet */){
            case 7:
              return new F(function(){return _2/* GHC.Base.++ */(_19e/* GHC.Show.lvl10 */, _19p/* sfen */);});
              break;
            case 8:
              return new F(function(){return _2/* GHC.Base.++ */(_19m/* GHC.Show.lvl9 */, _19p/* sfen */);});
              break;
            case 9:
              return new F(function(){return _2/* GHC.Base.++ */(_19l/* GHC.Show.lvl8 */, _19p/* sfen */);});
              break;
            case 10:
              return new F(function(){return _2/* GHC.Base.++ */(_19k/* GHC.Show.lvl7 */, _19p/* sfen */);});
              break;
            case 11:
              return new F(function(){return _2/* GHC.Base.++ */(_19j/* GHC.Show.lvl6 */, _19p/* sfen */);});
              break;
            case 12:
              return new F(function(){return _2/* GHC.Base.++ */(_19i/* GHC.Show.lvl5 */, _19p/* sfen */);});
              break;
            case 13:
              return new F(function(){return _2/* GHC.Base.++ */(_19h/* GHC.Show.lvl4 */, _19p/* sfen */);});
              break;
            case 14:
              return new F(function(){return _2/* GHC.Base.++ */(_19g/* GHC.Show.lvl3 */, new T(function(){
                var _19s/* sfex */ = E(_19p/* sfen */);
                if(!_19s/* sfex */._){
                  return __Z/* EXTERNAL */;
                }else{
                  if(E(_19s/* sfex */.a)==72){
                    return B(unAppCStr/* EXTERNAL */("\\&", _19s/* sfex */));
                  }else{
                    return E(_19s/* sfex */);
                  }
                }
              },1));});
              break;
            default:
              return new F(function(){return _2/* GHC.Base.++ */(new T2(1,_19c/* GHC.Show.lvl */,new T(function(){
                return B(_185/* GHC.List.$w!! */(_19b/* GHC.Show.asciiTab */, _19r/* sfet */));
              })), _19p/* sfen */);});
          }
        }else{
          return new T2(1,_19q/* sfeq */,_19p/* sfen */);
        }
    }
  }else{
    var _19t/* sfeW */ = new T(function(){
      var _19u/* sfeH */ = jsShowI/* EXTERNAL */(_19o/* sfem */);
      return B(_2/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_19u/* sfeH */), new T(function(){
        var _19v/* sfeM */ = E(_19p/* sfen */);
        if(!_19v/* sfeM */._){
          return __Z/* EXTERNAL */;
        }else{
          var _19w/* sfeP */ = E(_19v/* sfeM */.a);
          if(_19w/* sfeP */<48){
            return E(_19v/* sfeM */);
          }else{
            if(_19w/* sfeP */>57){
              return E(_19v/* sfeM */);
            }else{
              return B(unAppCStr/* EXTERNAL */("\\&", _19v/* sfeM */));
            }
          }
        }
      },1)));
    });
    return new T2(1,_19c/* GHC.Show.lvl */,_19t/* sfeW */);
  }
},
_19x/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\""));
}),
_19y/* showLitString */ = function(_19z/* sff1 */, _19A/* sff2 */){
  var _19B/* sff3 */ = E(_19z/* sff1 */);
  if(!_19B/* sff3 */._){
    return E(_19A/* sff2 */);
  }else{
    var _19C/* sff5 */ = _19B/* sff3 */.b,
    _19D/* sff8 */ = E(_19B/* sff3 */.a);
    if(_19D/* sff8 */==34){
      return new F(function(){return _2/* GHC.Base.++ */(_19x/* GHC.Show.lvl11 */, new T(function(){
        return B(_19y/* GHC.Show.showLitString */(_19C/* sff5 */, _19A/* sff2 */));
      },1));});
    }else{
      return new F(function(){return _19n/* GHC.Show.$wshowLitChar */(_19D/* sff8 */, new T(function(){
        return B(_19y/* GHC.Show.showLitString */(_19C/* sff5 */, _19A/* sff2 */));
      }));});
    }
  }
},
_19E/* lvl24 */ = new T(function(){
  return B(_19y/* GHC.Show.showLitString */(_17R/* Motion.Resist.lvl22 */, _17T/* Motion.Resist.lvl23 */));
}),
_19F/* lvl25 */ = new T2(1,_17S/* GHC.Show.shows5 */,_19E/* Motion.Resist.lvl24 */),
_19G/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po7"));
}),
_19H/* lvl27 */ = new T(function(){
  return B(_19y/* GHC.Show.showLitString */(_19G/* Motion.Resist.lvl26 */, _17T/* Motion.Resist.lvl23 */));
}),
_19I/* lvl28 */ = new T2(1,_17S/* GHC.Show.shows5 */,_19H/* Motion.Resist.lvl27 */),
_19J/* a8 */ = 200,
_19K/* lvl3 */ = new T1(0,_19J/* Motion.Resist.a8 */),
_19L/* lvl29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po6"));
}),
_19M/* lvl30 */ = new T(function(){
  return B(_19y/* GHC.Show.showLitString */(_19L/* Motion.Resist.lvl29 */, _17T/* Motion.Resist.lvl23 */));
}),
_19N/* lvl31 */ = new T2(1,_17S/* GHC.Show.shows5 */,_19M/* Motion.Resist.lvl30 */),
_19O/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po9"));
}),
_19P/* lvl33 */ = new T(function(){
  return B(_19y/* GHC.Show.showLitString */(_19O/* Motion.Resist.lvl32 */, _17T/* Motion.Resist.lvl23 */));
}),
_19Q/* lvl34 */ = new T2(1,_17S/* GHC.Show.shows5 */,_19P/* Motion.Resist.lvl33 */),
_19R/* lvl35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po5"));
}),
_19S/* lvl36 */ = new T(function(){
  return B(_19y/* GHC.Show.showLitString */(_19R/* Motion.Resist.lvl35 */, _17T/* Motion.Resist.lvl23 */));
}),
_19T/* lvl37 */ = new T2(1,_17S/* GHC.Show.shows5 */,_19S/* Motion.Resist.lvl36 */),
_19U/* lvl38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po4"));
}),
_19V/* lvl39 */ = new T(function(){
  return B(_19y/* GHC.Show.showLitString */(_19U/* Motion.Resist.lvl38 */, _17T/* Motion.Resist.lvl23 */));
}),
_19W/* lvl40 */ = new T2(1,_17S/* GHC.Show.shows5 */,_19V/* Motion.Resist.lvl39 */),
_19X/* lvl41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po3"));
}),
_19Y/* lvl42 */ = new T(function(){
  return B(_19y/* GHC.Show.showLitString */(_19X/* Motion.Resist.lvl41 */, _17T/* Motion.Resist.lvl23 */));
}),
_19Z/* lvl43 */ = new T2(1,_17S/* GHC.Show.shows5 */,_19Y/* Motion.Resist.lvl42 */),
_1a0/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po2"));
}),
_1a1/* lvl45 */ = new T(function(){
  return B(_19y/* GHC.Show.showLitString */(_1a0/* Motion.Resist.lvl44 */, _17T/* Motion.Resist.lvl23 */));
}),
_1a2/* lvl46 */ = new T2(1,_17S/* GHC.Show.shows5 */,_1a1/* Motion.Resist.lvl45 */),
_1a3/* lvl47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("po1"));
}),
_1a4/* lvl48 */ = new T(function(){
  return B(_19y/* GHC.Show.showLitString */(_1a3/* Motion.Resist.lvl47 */, _17T/* Motion.Resist.lvl23 */));
}),
_1a5/* lvl49 */ = new T2(1,_17S/* GHC.Show.shows5 */,_1a4/* Motion.Resist.lvl48 */),
_1a6/* lvl50 */ = new T4(0,_17A/* Motion.Resist.x */,_17A/* Motion.Resist.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_1a7/* lvl51 */ = new T2(0,_17A/* Motion.Resist.x */,_1a6/* Motion.Resist.lvl50 */),
_1a8/* lvl52 */ = new T2(0,_1a7/* Motion.Resist.lvl51 */,_6/* GHC.Types.[] */),
_1a9/* lvl5 */ = new T1(0,5),
_1aa/* lvl6 */ = new T(function(){
  return B(_Vi/* GHC.Enum.enumDeltaToInteger */(_17M/* Motion.Resist.lvl4 */, _17M/* Motion.Resist.lvl4 */, _1a9/* Motion.Resist.lvl5 */));
}),
_1ab/* lvl1 */ = function(_/* EXTERNAL */){
  return new F(function(){return jsMkStdout/* EXTERNAL */();});
},
_1ac/* stdout */ = new T(function(){
  return B(_44/* GHC.IO.unsafeDupablePerformIO */(_1ab/* Haste.Handle.lvl1 */));
}),
_1ad/* $wa */ = function(_1ae/* si2b */, _1af/* si2c */, _1ag/* si2d */){
  return function(_/* EXTERNAL */){
    var _1ah/* si2f */ = nMV/* EXTERNAL */(_1a8/* Motion.Resist.lvl52 */),
    _1ai/* si2h */ = _1ah/* si2f */,
    _1aj/* si2j */ = new T3(0,_17i/* Motion.Resist.dur */,_17k/* Motion.Resist.e */,_1ai/* si2h */),
    _1ak/* si2k */ = new T2(2,_1aj/* si2j */,_2E/* GHC.Base.id */),
    _1al/* si2l */ = new T(function(){
      return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, B(_sg/* Core.Ease.opLift */(_iE/* GHC.Float.divideDouble */, B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _17x/* Motion.Resist.lvl */, new T2(2,_1aj/* si2j */,_17O/* Motion.Resist.lvl21 */))), _17z/* Motion.Resist.lvl1 */)), _17K/* Motion.Resist.lvl2 */));
    }),
    _1am/* si2p */ = new T(function(){
      var _1an/* si2v */ = new T(function(){
        var _1ao/* si2r */ = B(_kB/* Core.Shape.Internal.$wrect */(new T(function(){
          return B(_170/* Core.Ease.$fFloatingValue_$cfmap */(_G5/* GHC.Float.negateDouble */, _1al/* si2l */));
        }), _17B/* Motion.Resist.lvl12 */, _17K/* Motion.Resist.lvl2 */, _17K/* Motion.Resist.lvl2 */));
        return new T3(0,_1ao/* si2r */.a,_1ao/* si2r */.b,_1ao/* si2r */.c);
      });
      return B(_rB/* Core.Render.Internal.fill1 */(_1ae/* si2b */, _1an/* si2v */));
    }),
    _1ap/* si2w */ = new T(function(){
      return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _17i/* Motion.Resist.dur */, _17k/* Motion.Resist.e */, _1ai/* si2h */, _17G/* Motion.Resist.lvl16 */, _Ac/* Core.Ease.easeTo1 */));
    }),
    _1aq/* si6i */ = function(_/* EXTERNAL */){
      var _1ar/* si2y */ = nMV/* EXTERNAL */(_1a8/* Motion.Resist.lvl52 */),
      _1as/* si2A */ = _1ar/* si2y */,
      _1at/* si2C */ = new T(function(){
        return B(_jN/* Core.Ease.$wforceTo */(_1as/* si2A */, _17I/* Motion.Resist.lvl18 */));
      }),
      _1au/* si2D */ = function(_1av/* si2E */, _1aw/* si2F */, _1ax/* si2G */){
        var _1ay/* si2H */ = E(_1av/* si2E */);
        if(!_1ay/* si2H */._){
          return new F(function(){return A1(_1ax/* si2G */,new T2(0,_7/* GHC.Tuple.() */,_1aw/* si2F */));});
        }else{
          var _1az/* si2L */ = function(_1aA/* si2M */){
            var _1aB/* si2V */ = function(_/* EXTERNAL */){
              var _1aC/* si2R */ = B(_17s/* GHC.IO.Handle.Text.hPutStrLn1 */(_1ac/* Haste.Handle.stdout */, _19F/* Motion.Resist.lvl25 */, _/* EXTERNAL */));
              return new T(function(){
                return B(_1au/* si2D */(_1ay/* si2H */.b, E(_1aA/* si2M */).b, _1ax/* si2G */));
              });
            };
            return new T1(0,_1aB/* si2V */);
          },
          _1aD/* si2W */ = function(_1aE/* si2X */){
            var _1aF/* si36 */ = function(_/* EXTERNAL */){
              var _1aG/* si32 */ = B(_17s/* GHC.IO.Handle.Text.hPutStrLn1 */(_1ac/* Haste.Handle.stdout */, _19I/* Motion.Resist.lvl28 */, _/* EXTERNAL */));
              return new T(function(){
                return B(_tv/* Core.World.Internal.sleep1 */(_177/* Motion.Resist.a11 */, E(_1aE/* si2X */).b, _1az/* si2L */));
              });
            };
            return new T1(0,_1aF/* si36 */);
          },
          _1aH/* si3S */ = function(_1aI/* si37 */){
            var _1aJ/* si38 */ = new T(function(){
              var _1aK/* si39 */ = new T(function(){
                return E(E(_1aI/* si37 */).a);
              }),
              _1aL/* si3d */ = new T(function(){
                return E(_1aK/* si39 */)*0.3;
              }),
              _1aM/* si3L */ = function(_1aN/* si3h */){
                var _1aO/* si3i */ = new T(function(){
                  var _1aP/* si3j */ = new T(function(){
                    return E(E(_1aN/* si3h */).a);
                  }),
                  _1aQ/* si3n */ = new T(function(){
                    return B(_jN/* Core.Ease.$wforceTo */(_1as/* si2A */, new T(function(){
                      return E(_1aP/* si3j */)*0.6-E(_1aL/* si3d */);
                    })));
                  }),
                  _1aR/* si3G */ = function(_1aS/* si3w */){
                    var _1aT/* si3F */ = function(_/* EXTERNAL */){
                      var _1aU/* si3B */ = B(_17s/* GHC.IO.Handle.Text.hPutStrLn1 */(_1ac/* Haste.Handle.stdout */, _19N/* Motion.Resist.lvl31 */, _/* EXTERNAL */));
                      return new T(function(){
                        return B(A2(_1aQ/* si3n */,E(_1aS/* si3w */).b, _1aD/* si2W */));
                      });
                    };
                    return new T1(0,_1aT/* si3F */);
                  };
                  return B(A(_jN/* Core.Ease.$wforceTo */,[_1ai/* si2h */, new T(function(){
                    return B(_tr/* GHC.Float.plusDouble */(_1aK/* si39 */, _1aP/* si3j */));
                  }), _1aw/* si2F */, _1aR/* si3G */]));
                });
                return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_1as/* si2A */, _1aN/* si3h */, function(_1aV/* si3H */){
                  return E(_1aO/* si3i */);
                })));
              };
              return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_1as/* si2A */, _1aM/* si3L */)));
            });
            return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_1ai/* si2h */, _1aI/* si37 */, function(_1aW/* si3O */){
              return E(_1aJ/* si38 */);
            })));
          };
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_1ai/* si2h */, _1aH/* si3S */)));
        }
      },
      _1aX/* si6g */ = function(_/* EXTERNAL */){
        var _1aY/* si3W */ = nMV/* EXTERNAL */(_1a8/* Motion.Resist.lvl52 */),
        _1aZ/* si3Y */ = _1aY/* si3W */;
        return new T(function(){
          var _1b0/* si40 */ = new T(function(){
            return B(_jN/* Core.Ease.$wforceTo */(_1aZ/* si3Y */, _17A/* Motion.Resist.x */));
          }),
          _1b1/* si41 */ = function(_1b2/* si42 */){
            return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _17j/* Motion.Resist.dur1 */, _17k/* Motion.Resist.e */, _1aZ/* si3Y */, _17b/* Motion.Resist.a5 */, function(_1b3/* si43 */){
              return E(_1b2/* si42 */);
            });});
          },
          _1b4/* si45 */ = function(_1b5/* si46 */){
            var _1b6/* si47 */ = new T(function(){
              return B(A1(_1ap/* si2w */,_1b5/* si46 */));
            }),
            _1b7/* si5f */ = function(_1b8/* si48 */){
              var _1b9/* si49 */ = function(_1ba/* si4a */){
                var _1bb/* si4j */ = function(_/* EXTERNAL */){
                  var _1bc/* si4f */ = B(_17s/* GHC.IO.Handle.Text.hPutStrLn1 */(_1ac/* Haste.Handle.stdout */, _19Q/* Motion.Resist.lvl34 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(A2(_1b4/* si45 */,E(_1ba/* si4a */).b, _1b8/* si48 */));
                  });
                };
                return new T1(0,_1bb/* si4j */);
              },
              _1bd/* si4k */ = function(_1be/* si4l */){
                var _1bf/* si4u */ = function(_/* EXTERNAL */){
                  var _1bg/* si4q */ = B(_17s/* GHC.IO.Handle.Text.hPutStrLn1 */(_1ac/* Haste.Handle.stdout */, _19T/* Motion.Resist.lvl37 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(_1au/* si2D */(_17N/* Motion.Resist.lvl20 */, E(_1be/* si4l */).b, _1b9/* si49 */));
                  });
                };
                return new T1(0,_1bf/* si4u */);
              },
              _1bh/* si4v */ = function(_1bi/* si4w */){
                var _1bj/* si4F */ = function(_/* EXTERNAL */){
                  var _1bk/* si4B */ = B(_17s/* GHC.IO.Handle.Text.hPutStrLn1 */(_1ac/* Haste.Handle.stdout */, _19W/* Motion.Resist.lvl40 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(A2(_1at/* si2C */,E(_1bi/* si4w */).b, _1bd/* si4k */));
                  });
                };
                return new T1(0,_1bj/* si4F */);
              },
              _1bl/* si4G */ = function(_1bm/* si4H */){
                var _1bn/* si4Q */ = function(_/* EXTERNAL */){
                  var _1bo/* si4M */ = B(_17s/* GHC.IO.Handle.Text.hPutStrLn1 */(_1ac/* Haste.Handle.stdout */, _19Z/* Motion.Resist.lvl43 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(A2(_1b0/* si40 */,E(_1bm/* si4H */).b, _1bh/* si4v */));
                  });
                };
                return new T1(0,_1bn/* si4Q */);
              },
              _1bp/* si4R */ = function(_1bq/* si4S */){
                var _1br/* si53 */ = function(_/* EXTERNAL */){
                  var _1bs/* si4X */ = B(_17s/* GHC.IO.Handle.Text.hPutStrLn1 */(_1ac/* Haste.Handle.stdout */, _1a2/* Motion.Resist.lvl46 */, _/* EXTERNAL */));
                  return new T(function(){
                    return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_1b1/* si41 */, E(_1bq/* si4S */).b, _1bl/* si4G */)));
                  });
                };
                return new T1(0,_1br/* si53 */);
              },
              _1bt/* si5e */ = function(_1bu/* si54 */){
                var _1bv/* si5d */ = function(_/* EXTERNAL */){
                  var _1bw/* si59 */ = B(_17s/* GHC.IO.Handle.Text.hPutStrLn1 */(_1ac/* Haste.Handle.stdout */, _1a5/* Motion.Resist.lvl49 */, _/* EXTERNAL */));
                  return new T(function(){
                    return B(_tv/* Core.World.Internal.sleep1 */(_17H/* Motion.Resist.lvl17 */, E(_1bu/* si54 */).b, _1bp/* si4R */));
                  });
                };
                return new T1(0,_1bv/* si5d */);
              };
              return new F(function(){return A1(_1b6/* si47 */,_1bt/* si5e */);});
            };
            return E(_1b7/* si5f */);
          },
          _1bx/* si6c */ = new T(function(){
            var _1by/* si6a */ = new T(function(){
              var _1bz/* si5j */ = new T2(2,new T3(0,_17j/* Motion.Resist.dur1 */,_17k/* Motion.Resist.e */,_1aZ/* si3Y */),_2E/* GHC.Base.id */),
              _1bA/* si5k */ = function(_1bB/* si5l */){
                var _1bC/* si5m */ = E(_1bB/* si5l */);
                if(!_1bC/* si5m */._){
                  return E(_17a/* Motion.Resist.a2 */);
                }else{
                  var _1bD/* si5n */ = _1bC/* si5m */.a,
                  _1bE/* si5o */ = _1bC/* si5m */.b;
                  if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_1bD/* si5n */, _17F/* Motion.Resist.lvl15 */))){
                    var _1bF/* si5q */ = E(_17h/* Motion.Resist.a9 */),
                    _1bG/* si5r */ = _1bF/* si5q */.a,
                    _1bH/* si5s */ = _1bF/* si5q */.b,
                    _1bI/* si5t */ = new T(function(){
                      var _1bJ/* si5O */ = new T(function(){
                        var _1bK/* si5M */ = new T(function(){
                          var _1bL/* si5u */ = function(_1bM/* si5v */, _1bN/* si5w */){
                            if(!B(_Ry/* GHC.Integer.Type.eqInteger */(_1bM/* si5v */, _17F/* Motion.Resist.lvl15 */))){
                              var _1bO/* si5y */ = new T(function(){
                                var _1bP/* si5C */ = new T(function(){
                                  return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_17E/* Motion.Resist.lvl14 */,new T(function(){
                                    return B(_1bL/* si5u */(B(_M1/* GHC.Integer.Type.minusInteger */(_1bM/* si5v */, _17M/* Motion.Resist.lvl4 */)), _1bN/* si5w */));
                                  }),_7/* GHC.Tuple.() */)));
                                });
                                return B(_rx/* Control.Monad.Skeleton.bone */(new T3(6,_1ak/* si2k */,_1bP/* si5C */,_7/* GHC.Tuple.() */)));
                              }),
                              _1bQ/* si5I */ = function(_1bR/* si5E */){
                                return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T3(6,new T(function(){
                                  return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_1bR/* si5E */), _1bz/* si5j */));
                                }),_1bO/* si5y */,_7/* GHC.Tuple.() */));});
                              };
                              return new T2(0,E(_1bG/* si5r */),E(new T2(2,_1bH/* si5s */,new T1(1,_1bQ/* si5I */))));
                            }else{
                              return E(_1bN/* si5w */);
                            }
                          };
                          return B(_1bL/* si5u */(B(_M1/* GHC.Integer.Type.minusInteger */(_1bD/* si5n */, _17M/* Motion.Resist.lvl4 */)), _1am/* si2p */));
                        });
                        return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_17E/* Motion.Resist.lvl14 */,_1bK/* si5M */,_7/* GHC.Tuple.() */)));
                      });
                      return B(_rx/* Control.Monad.Skeleton.bone */(new T3(6,_1ak/* si2k */,_1bJ/* si5O */,_7/* GHC.Tuple.() */)));
                    }),
                    _1bS/* si5Q */ = new T(function(){
                      return B(_1bA/* si5k */(_1bE/* si5o */));
                    }),
                    _1bT/* si5V */ = function(_1bU/* si5R */){
                      return new F(function(){return _rx/* Control.Monad.Skeleton.bone */(new T3(6,new T(function(){
                        return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, new T1(0,_1bU/* si5R */), _1bz/* si5j */));
                      }),_1bI/* si5t */,_7/* GHC.Tuple.() */));});
                    };
                    return new T2(0,E(_1bG/* si5r */),E(new T2(2,new T2(2,_1bH/* si5s */,new T1(1,_1bT/* si5V */)),new T1(1,function(_1bV/* si5Y */){
                      return E(_1bS/* si5Q */);
                    }))));
                  }else{
                    var _1bW/* si62 */ = E(_1am/* si2p */),
                    _1bX/* si65 */ = new T(function(){
                      return B(_1bA/* si5k */(_1bE/* si5o */));
                    });
                    return new T2(0,E(_1bW/* si62 */.a),E(new T2(2,_1bW/* si62 */.b,new T1(1,function(_1bY/* si66 */){
                      return E(_1bX/* si65 */);
                    }))));
                  }
                }
              };
              return B(_1bA/* si5k */(_1aa/* Motion.Resist.lvl6 */));
            });
            return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,new T(function(){
              return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _17K/* Motion.Resist.lvl2 */, _1al/* si2l */));
            }),_19K/* Motion.Resist.lvl3 */),_1by/* si6a */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_1ag/* si2d */,new T2(0,new T2(0,_1bx/* si6c */,_1b4/* si45 */),_1af/* si2c */)));
        });
      };
      return new T1(0,_1aX/* si6g */);
    };
    return new T1(0,_1aq/* si6i */);
  };
},
_1bZ/* resistMot1 */ = function(_1c0/* si6l */, _1c1/* si6m */, _1c2/* si6n */){
  return new T1(0,B(_1ad/* Motion.Resist.$wa */(_1c0/* si6l */, _1c1/* si6m */, _1c2/* si6n */)));
},
_1c3/* lvl67 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_16T/* Motion.Main.lvl64 */, _1bZ/* Motion.Resist.resistMot1 */, _16U/* Motion.Main.lvl65 */, _16V/* Motion.Main.lvl66 */));
}),
_1c4/* lvl */ = 30,
_1c5/* lvl1 */ = 0,
_1c6/* x */ = 1,
_1c7/* lvl2 */ = new T4(0,_1c6/* Motion.Info.x */,_1c6/* Motion.Info.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_1c8/* lvl3 */ = new T2(0,_1c6/* Motion.Info.x */,_1c7/* Motion.Info.lvl2 */),
_1c9/* lvl4 */ = new T2(0,_1c8/* Motion.Info.lvl3 */,_6/* GHC.Types.[] */),
_1ca/* $wa */ = function(_1cb/* s6yS */, _1cc/* s6yT */, _1cd/* s6yU */){
  return function(_/* EXTERNAL */){
    var _1ce/* s6yW */ = nMV/* EXTERNAL */(_1c9/* Motion.Info.lvl4 */);
    return new T(function(){
      var _1cf/* s6yZ */ = function(_1cg/* s6z0 */, _1ch/* s6z1 */){
        var _1ci/* s6zf */ = B(A1(_1cg/* s6z0 */,new T(function(){
          var _1cj/* s6z4 */ = E(_1ch/* s6z1 */)/0.6-_1cb/* s6yS *//2*0.6666666666666667;
          if(1>_1cj/* s6z4 */){
            if(0>_1cj/* s6z4 */){
              return E(_1c6/* Motion.Info.x */);
            }else{
              return 1-_1cj/* s6z4 */;
            }
          }else{
            return E(_1c5/* Motion.Info.lvl1 */);
          }
        })));
        return 1-_1ci/* s6zf */*_1ci/* s6zf */;
      },
      _1ck/* s6zn */ = new T3(0,_1c4/* Motion.Info.lvl */,function(_1cl/* s6zj */, _1cm/* s6zk */){
        return new F(function(){return _1cf/* s6yZ */(_1cl/* s6zj */, _1cm/* s6zk */);});
      },_1ce/* s6yW */),
      _1cn/* s6zo */ = E(_1cb/* s6yS */);
      if(_1cn/* s6zo */==2){
        return B(A1(_1cd/* s6yU */,new T2(0,new T2(1,_1ck/* s6zn */,_6/* GHC.Types.[] */),_1cc/* s6yT */)));
      }else{
        return new T1(0,B(_1ca/* Motion.Info.$wa */(_1cn/* s6zo */+1|0, _1cc/* s6yT */, function(_1co/* s6zq */){
          var _1cp/* s6zr */ = E(_1co/* s6zq */);
          return new F(function(){return A1(_1cd/* s6yU */,new T2(0,new T2(1,_1ck/* s6zn */,_1cp/* s6zr */.a),_1cp/* s6zr */.b));});
        })));
      }
    });
  };
},
_1cq/* $wa1 */ = function(_1cr/* s6zD */, _1cs/* s6zE */, _1ct/* s6zF */){
  return function(_/* EXTERNAL */){
    var _1cu/* s6zH */ = nMV/* EXTERNAL */(_1c9/* Motion.Info.lvl4 */);
    return new T(function(){
      var _1cv/* s6zK */ = function(_1cw/* s6zL */, _1cx/* s6zM */){
        var _1cy/* s6A0 */ = B(A1(_1cw/* s6zL */,new T(function(){
          var _1cz/* s6zP */ = E(_1cx/* s6zM */)/0.6-_1cr/* s6zD *//2*0.6666666666666667;
          if(1>_1cz/* s6zP */){
            if(0>_1cz/* s6zP */){
              return E(_1c6/* Motion.Info.x */);
            }else{
              return 1-_1cz/* s6zP */;
            }
          }else{
            return E(_1c5/* Motion.Info.lvl1 */);
          }
        })));
        return 1-_1cy/* s6A0 */*_1cy/* s6A0 */*_1cy/* s6A0 */;
      },
      _1cA/* s6A9 */ = new T3(0,_1c4/* Motion.Info.lvl */,function(_1cB/* s6A5 */, _1cC/* s6A6 */){
        return new F(function(){return _1cv/* s6zK */(_1cB/* s6A5 */, _1cC/* s6A6 */);});
      },_1cu/* s6zH */),
      _1cD/* s6Aa */ = E(_1cr/* s6zD */);
      if(_1cD/* s6Aa */==2){
        return B(A1(_1ct/* s6zF */,new T2(0,new T2(1,_1cA/* s6A9 */,_6/* GHC.Types.[] */),_1cs/* s6zE */)));
      }else{
        return new T1(0,B(_1cq/* Motion.Info.$wa1 */(_1cD/* s6Aa */+1|0, _1cs/* s6zE */, function(_1cE/* s6Ac */){
          var _1cF/* s6Ad */ = E(_1cE/* s6Ac */);
          return new F(function(){return A1(_1ct/* s6zF */,new T2(0,new T2(1,_1cA/* s6A9 */,_1cF/* s6Ad */.a),_1cF/* s6Ad */.b));});
        })));
      }
    });
  };
},
_1cG/* a */ = new T1(0,_/* EXTERNAL */),
_1cH/* a1 */ = new T1(0,_7/* GHC.Tuple.() */),
_1cI/* a2 */ = new T2(0,E(_1cH/* Motion.Info.a1 */),E(_1cG/* Motion.Info.a */)),
_1cJ/* b1 */ = 10,
_1cK/* dur */ = 40,
_1cL/* e */ = function(_1cM/* s6yH */, _1cN/* s6yI */){
  var _1cO/* s6yN */ = B(A1(_1cM/* s6yH */,new T(function(){
    return 1-E(_1cN/* s6yI */);
  })));
  return 1-_1cO/* s6yN */*_1cO/* s6yN */*_1cO/* s6yN */;
},
_1cP/* a6 */ = function(_1cQ/* s6At */, _1cR/* s6Au */){
  return new F(function(){return A1(_1cR/* s6Au */,new T2(0,_6/* GHC.Types.[] */,_1cQ/* s6At */));});
},
_1cS/* go */ = function(_1cT/* s6Aw */, _1cU/* s6Ax */){
  var _1cV/* s6Ay */ = E(_1cT/* s6Aw */);
  if(!_1cV/* s6Ay */._){
    return E(_1cP/* Motion.Info.a6 */);
  }else{
    var _1cW/* s6AB */ = E(_1cU/* s6Ax */);
    if(!_1cW/* s6AB */._){
      return E(_1cP/* Motion.Info.a6 */);
    }else{
      var _1cX/* s6AE */ = new T(function(){
        return B(_1cS/* Motion.Info.go */(_1cV/* s6Ay */.b, _1cW/* s6AB */.b));
      }),
      _1cY/* s6AF */ = new T(function(){
        var _1cZ/* s6AG */ = E(_1cW/* s6AB */.a),
        _1d0/* s6AH */ = _1cZ/* s6AG */.a,
        _1d1/* s6AI */ = _1cZ/* s6AG */.b,
        _1d2/* s6AJ */ = new T(function(){
          return B(_jN/* Core.Ease.$wforceTo */(E(_1d0/* s6AH */).c, _1c6/* Motion.Info.x */));
        }),
        _1d3/* s6AO */ = new T(function(){
          return B(_jN/* Core.Ease.$wforceTo */(E(_1d1/* s6AI */).c, _1c6/* Motion.Info.x */));
        }),
        _1d4/* s6AT */ = new T(function(){
          return 1.8-E(_1cV/* s6Ay */.a)/2*0.4;
        }),
        _1d5/* s6B0 */ = new T(function(){
          var _1d6/* s6B1 */ = E(_1d0/* s6AH */);
          return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1d6/* s6B1 */.a, _1d6/* s6B1 */.b, _1d6/* s6B1 */.c, _1d4/* s6AT */, _Ac/* Core.Ease.easeTo1 */));
        }),
        _1d7/* s6B5 */ = new T(function(){
          var _1d8/* s6B6 */ = E(_1d1/* s6AI */);
          return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1d8/* s6B6 */.a, _1d8/* s6B6 */.b, _1d8/* s6B6 */.c, _1d4/* s6AT */, _Ac/* Core.Ease.easeTo1 */));
        }),
        _1d9/* s6Bt */ = function(_1da/* s6Ba */){
          var _1db/* s6Bb */ = new T(function(){
            return B(A1(_1d2/* s6AJ */,_1da/* s6Ba */));
          }),
          _1dc/* s6Bs */ = function(_1dd/* s6Bc */){
            var _1de/* s6Bd */ = function(_1df/* s6Be */){
              return new F(function(){return A2(_1d7/* s6B5 */,E(_1df/* s6Be */).b, _1dd/* s6Bc */);});
            },
            _1dg/* s6Bi */ = function(_1dh/* s6Bj */){
              return new F(function(){return A2(_1d5/* s6B0 */,E(_1dh/* s6Bj */).b, _1de/* s6Bd */);});
            };
            return new F(function(){return A1(_1db/* s6Bb */,function(_1di/* s6Bn */){
              return new F(function(){return A2(_1d3/* s6AO */,E(_1di/* s6Bn */).b, _1dg/* s6Bi */);});
            });});
          };
          return E(_1dc/* s6Bs */);
        };
        return E(_1d9/* s6Bt */);
      }),
      _1dj/* s6BK */ = function(_1dk/* s6Bu */){
        var _1dl/* s6Bv */ = new T(function(){
          return B(A1(_1cY/* s6AF */,_1dk/* s6Bu */));
        }),
        _1dm/* s6BJ */ = function(_1dn/* s6Bw */){
          var _1do/* s6BI */ = function(_1dp/* s6Bx */){
            var _1dq/* s6By */ = E(_1dp/* s6Bx */);
            return new F(function(){return A2(_1cX/* s6AE */,_1dq/* s6By */.b, function(_1dr/* s6BB */){
              var _1ds/* s6BC */ = E(_1dr/* s6BB */);
              return new F(function(){return A1(_1dn/* s6Bw */,new T2(0,new T2(1,_1dq/* s6By */.a,_1ds/* s6BC */.a),_1ds/* s6BC */.b));});
            });});
          };
          return new F(function(){return A1(_1dl/* s6Bv */,_1do/* s6BI */);});
        };
        return E(_1dm/* s6BJ */);
      };
      return E(_1dj/* s6BK */);
    }
  }
},
_1dt/* lvl10 */ = 30,
_1du/* lvl11 */ = 1.2,
_1dv/* lvl12 */ = 10,
_1dw/* a4 */ = 100,
_1dx/* lvl5 */ = new T1(0,_1dw/* Motion.Info.a4 */),
_1dy/* lvl6 */ = new T2(0,_1dx/* Motion.Info.lvl5 */,_1dx/* Motion.Info.lvl5 */),
_1dz/* lvl7 */ = new T1(0,_1c5/* Motion.Info.lvl1 */),
_1dA/* a5 */ = 80,
_1dB/* lvl8 */ = new T1(0,_1dA/* Motion.Info.a5 */),
_1dC/* lvl9 */ = new T(function(){
  var _1dD/* s6Ap */ = B(_GQ/* Core.Shape.Internal.$wcenterRect */(_1dz/* Motion.Info.lvl7 */, _1dz/* Motion.Info.lvl7 */, _1dB/* Motion.Info.lvl8 */, _1dB/* Motion.Info.lvl8 */));
  return new T3(0,_1dD/* s6Ap */.a,_1dD/* s6Ap */.b,_1dD/* s6Ap */.c);
}),
_1dE/* zip */ = function(_1dF/* s9E4 */, _1dG/* s9E5 */){
  var _1dH/* s9E6 */ = E(_1dF/* s9E4 */);
  if(!_1dH/* s9E6 */._){
    return __Z/* EXTERNAL */;
  }else{
    var _1dI/* s9E9 */ = E(_1dG/* s9E5 */);
    return (_1dI/* s9E9 */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T2(0,_1dH/* s9E6 */.a,_1dI/* s9E9 */.a),new T(function(){
      return B(_1dE/* GHC.List.zip */(_1dH/* s9E6 */.b, _1dI/* s9E9 */.b));
    }));
  }
},
_1dJ/* infoMot */ = function(_1dK/* s6BL */){
  var _1dL/* s6BM */ = new T(function(){
    return B(_rB/* Core.Render.Internal.fill1 */(_1dK/* s6BL */, _1dC/* Motion.Info.lvl9 */));
  }),
  _1dM/* s6BN */ = function(_1dN/* s6BO */){
    var _1dO/* s6BP */ = E(_1dN/* s6BO */);
    if(!_1dO/* s6BP */._){
      return E(_1cI/* Motion.Info.a2 */);
    }else{
      var _1dP/* s6BS */ = E(_1dO/* s6BP */.a),
      _1dQ/* s6BV */ = new T(function(){
        return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, _1dx/* Motion.Info.lvl5 */, B(_Is/* Core.Ease.morph */(_1dP/* s6BS */.a))));
      }),
      _1dR/* s6BZ */ = B(_rx/* Control.Monad.Skeleton.bone */(new T1(1,function(_/* EXTERNAL */){
        return new F(function(){return _14m/* Core.Ease.valueIO1 */(_1dQ/* s6BV */, _/* EXTERNAL */);});
      }))),
      _1dS/* s6C2 */ = new T(function(){
        return B(_1dM/* s6BN */(_1dO/* s6BP */.b));
      }),
      _1dT/* s6C3 */ = new T(function(){
        return B(_sg/* Core.Ease.opLift */(_Aq/* GHC.Float.timesDouble */, _1dx/* Motion.Info.lvl5 */, B(_Is/* Core.Ease.morph */(_1dP/* s6BS */.b))));
      }),
      _1dU/* s6C5 */ = new T(function(){
        return B(_rx/* Control.Monad.Skeleton.bone */(new T1(1,function(_/* EXTERNAL */){
          return new F(function(){return _14m/* Core.Ease.valueIO1 */(_1dT/* s6C3 */, _/* EXTERNAL */);});
        })));
      }),
      _1dV/* s6C8 */ = new T(function(){
        var _1dW/* s6Ce */ = B(_rB/* Core.Render.Internal.fill1 */(_1dK/* s6BL */, new T(function(){
          var _1dX/* s6C9 */ = B(_GQ/* Core.Shape.Internal.$wcenterRect */(_1dz/* Motion.Info.lvl7 */, _1dz/* Motion.Info.lvl7 */, _1dT/* s6C3 */, _1dT/* s6C3 */));
          return new T3(0,_1dX/* s6C9 */.a,_1dX/* s6C9 */.b,_1dX/* s6C9 */.c);
        }))),
        _1dY/* s6Ch */ = new T(function(){
          return B(_rB/* Core.Render.Internal.fill1 */(_yZ/* Core.Render.Internal.white */, new T(function(){
            var _1dZ/* s6Ci */ = B(_GQ/* Core.Shape.Internal.$wcenterRect */(_1dz/* Motion.Info.lvl7 */, _1dz/* Motion.Info.lvl7 */, _1dQ/* s6BV */, _1dQ/* s6BV */));
            return new T3(0,_1dZ/* s6Ci */.a,_1dZ/* s6Ci */.b,_1dZ/* s6Ci */.c);
          })));
        });
        return new T2(0,E(_1dW/* s6Ce */.a),E(new T2(2,_1dW/* s6Ce */.b,new T1(1,function(_1e0/* s6Cn */){
          return E(_1dY/* s6Ch */);
        }))));
      }),
      _1e1/* s6CP */ = function(_1e2/* s6Cr */){
        var _1e3/* s6Cs */ = E(_1dU/* s6C5 */);
        return new T2(0,E(_1e3/* s6Cs */.a),E(new T2(2,_1e3/* s6Cs */.b,new T1(1,function(_1e4/* s6Cv */){
          var _1e5/* s6Cw */ = E(_1e2/* s6Cr */);
          if(!_1e5/* s6Cw */._){
            return E(_1cI/* Motion.Info.a2 */);
          }else{
            var _1e6/* s6Cy */ = E(_1e4/* s6Cv */);
            if(!_1e6/* s6Cy */._){
              return E(_1cI/* Motion.Info.a2 */);
            }else{
              var _1e7/* s6CE */ = E(_1e5/* s6Cw */.a)-E(_1e6/* s6Cy */.a);
              return (_1e7/* s6CE */==0) ? E(_1cI/* Motion.Info.a2 */) : (_1e7/* s6CE */<=0) ? ( -_1e7/* s6CE */<=1) ? E(_1cI/* Motion.Info.a2 */) : E(_1dV/* s6C8 */) : (_1e7/* s6CE */<=1) ? E(_1cI/* Motion.Info.a2 */) : E(_1dV/* s6C8 */);
            }
          }
        }))));
      };
      return new T2(0,E(_1dR/* s6BZ */.a),E(new T2(2,new T2(2,_1dR/* s6BZ */.b,new T1(1,_1e1/* s6CP */)),new T1(1,function(_1e8/* s6CS */){
        return E(_1dS/* s6C2 */);
      }))));
    }
  },
  _1e9/* s6Eq */ = function(_1ea/* s6CW */, _1eb/* s6CX */){
    var _1ec/* s6Ep */ = function(_/* EXTERNAL */){
      var _1ed/* s6CZ */ = nMV/* EXTERNAL */(_1c9/* Motion.Info.lvl4 */),
      _1ee/* s6D1 */ = _1ed/* s6CZ */;
      return new T(function(){
        var _1ef/* s6D3 */ = new T(function(){
          var _1eg/* s6D4 */ = new T3(0,_1cK/* Motion.Info.dur */,_1cL/* Motion.Info.e */,_1ee/* s6D1 */);
          return B(_rx/* Control.Monad.Skeleton.bone */(new T3(7,new T2(0,new T2(2,_1eg/* s6D4 */,_2E/* GHC.Base.id */),new T2(2,_1eg/* s6D4 */,_2E/* GHC.Base.id */)),_1dL/* s6BM */,_7/* GHC.Tuple.() */)));
        }),
        _1eh/* s6D9 */ = function(_1ei/* s6Da */){
          return E(_1ef/* s6D3 */);
        },
        _1ej/* s6Dc */ = new T(function(){
          return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1cJ/* Motion.Info.b1 */, _15I/* Core.Ease.cubic */, _1ee/* s6D1 */, _1du/* Motion.Info.lvl11 */, _Ac/* Core.Ease.easeTo1 */));
        }),
        _1ek/* s6Dd */ = new T(function(){
          return B(_jN/* Core.Ease.$wforceTo */(_1ee/* s6D1 */, _1du/* Motion.Info.lvl11 */));
        }),
        _1el/* s6De */ = new T(function(){
          return B(_jN/* Core.Ease.$wforceTo */(_1ee/* s6D1 */, _1c6/* Motion.Info.x */));
        }),
        _1em/* s6Df */ = function(_1en/* s6Dg */){
          return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1cK/* Motion.Info.dur */, _1cL/* Motion.Info.e */, _1ee/* s6D1 */, _1c6/* Motion.Info.x */, function(_1eo/* s6Dh */){
            return E(_1en/* s6Dg */);
          });});
        },
        _1ep/* s6El */ = function(_1eq/* s6Dj */){
          var _1er/* s6Dk */ = E(_1eq/* s6Dj */),
          _1es/* s6Ei */ = function(_1et/* s6Dn */){
            var _1eu/* s6Do */ = E(_1et/* s6Dn */),
            _1ev/* s6Dr */ = new T(function(){
              return B(_1dE/* GHC.List.zip */(_1er/* s6Dk */.a, _1eu/* s6Do */.a));
            }),
            _1ew/* s6Ds */ = new T(function(){
              return B(_1cS/* Motion.Info.go */(_Im/* Core.Util.iforM1 */, _1ev/* s6Dr */));
            }),
            _1ex/* s6Du */ = function(_1ey/* s6DE */){
              return new F(function(){return _1ez/* s6DB */(E(_1ey/* s6DE */).b);});
            },
            _1eA/* s6Dv */ = function(_1eB/* s6DI */){
              return new F(function(){return A2(_1el/* s6De */,E(_1eB/* s6DI */).b, _1ex/* s6Du */);});
            },
            _1eC/* s6Dw */ = function(_1eD/* s6DM */){
              return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_1em/* s6Df */, E(_1eD/* s6DM */).b, _1eA/* s6Dv */)));
            },
            _1eE/* s6Dx */ = function(_1eF/* s6DS */){
              return new F(function(){return A2(_1ek/* s6Dd */,E(_1eF/* s6DS */).b, _1eC/* s6Dw */);});
            },
            _1eG/* s6Dy */ = function(_1eH/* s6DW */){
              return new F(function(){return A2(_1ew/* s6Ds */,E(_1eH/* s6DW */).b, _1eE/* s6Dx */);});
            },
            _1eI/* s6Dz */ = function(_1eJ/* s6E0 */){
              return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_1dv/* Motion.Info.lvl12 */, E(_1eJ/* s6E0 */).b, _1eG/* s6Dy */);});
            },
            _1eK/* s6DA */ = function(_1eL/* s6E4 */){
              return new F(function(){return A2(_1ej/* s6Dc */,E(_1eL/* s6E4 */).b, _1eI/* s6Dz */);});
            },
            _1ez/* s6DB */ = function(_1eM/* s6E8 */){
              return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_1dt/* Motion.Info.lvl10 */, _1eM/* s6E8 */, _1eK/* s6DA */);});
            },
            _1eN/* s6Ef */ = new T(function(){
              return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,_1dy/* Motion.Info.lvl6 */,new T(function(){
                var _1eO/* s6E9 */ = B(_1dM/* s6BN */(_1ev/* s6Dr */));
                return new T2(0,E(_1eO/* s6E9 */.a),E(new T2(2,_1eO/* s6E9 */.b,new T1(1,_1eh/* s6D9 */))));
              }),_7/* GHC.Tuple.() */)));
            });
            return new F(function(){return A1(_1eb/* s6CX */,new T2(0,new T2(0,_1eN/* s6Ef */,function(_1eP/* s6DC */, _1eQ/* s6DD */){
              return new F(function(){return _1ez/* s6DB */(_1eP/* s6DC */);});
            }),_1eu/* s6Do */.b));});
          };
          return new T1(0,B(_1cq/* Motion.Info.$wa1 */(0, _1er/* s6Dk */.b, _1es/* s6Ei */)));
        };
        return new T1(0,B(_1ca/* Motion.Info.$wa */(0, _1ea/* s6CW */, _1ep/* s6El */)));
      });
    };
    return new T1(0,_1ec/* s6Ep */);
  };
  return E(_1e9/* s6Eq */);
},
_1eR/* lvl68 */ = new T4(0,_AC/* Motion.Main.lvl23 */,_Jl/* Motion.Main.lvl45 */,_G0/* Motion.Main.lvl37 */,_Al/* Motion.Main.lvl11 */),
_1eS/* lvl69 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Info"));
}),
_1eT/* lvl70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("easeOutBack & Cubic-Quad difference"));
}),
_1eU/* lvl71 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_1eR/* Motion.Main.lvl68 */, _1dJ/* Motion.Info.infoMot */, _1eS/* Motion.Main.lvl69 */, _1eT/* Motion.Main.lvl70 */));
}),
_1eV/* a2 */ = 0,
_1eW/* a3 */ = 60,
_1eX/* b1 */ = 3,
_1eY/* dur */ = 40,
_1eZ/* a1 */ = 100,
_1f0/* lvl */ = new T1(0,_1eZ/* Motion.Collide.a1 */),
_1f1/* x2 */ = 3.7699111843077517,
_1f2/* lvl9 */ = new T4(0,_1f1/* Motion.Collide.x2 */,_1f1/* Motion.Collide.x2 */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_1f3/* lvl10 */ = new T2(0,_1f1/* Motion.Collide.x2 */,_1f2/* Motion.Collide.lvl9 */),
_1f4/* lvl11 */ = new T2(0,_1f3/* Motion.Collide.lvl10 */,_6/* GHC.Types.[] */),
_1f5/* x1 */ = 20,
_1f6/* lvl12 */ = new T4(0,_1f5/* Motion.Collide.x1 */,_1f5/* Motion.Collide.x1 */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_1f7/* lvl13 */ = new T2(0,_1f5/* Motion.Collide.x1 */,_1f6/* Motion.Collide.lvl12 */),
_1f8/* lvl14 */ = new T2(0,_1f7/* Motion.Collide.lvl13 */,_6/* GHC.Types.[] */),
_1f9/* x */ = -20,
_1fa/* lvl15 */ = new T4(0,_1f9/* Motion.Collide.x */,_1f9/* Motion.Collide.x */,_iH/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_1fb/* lvl16 */ = new T2(0,_1f9/* Motion.Collide.x */,_1fa/* Motion.Collide.lvl15 */),
_1fc/* lvl17 */ = new T2(0,_1fb/* Motion.Collide.lvl16 */,_6/* GHC.Types.[] */),
_1fd/* lvl1 */ = new T1(0,_1eV/* Motion.Collide.a2 */),
_1fe/* lvl2 */ = new T1(0,_1eW/* Motion.Collide.a3 */),
_1ff/* lvl3 */ = new T(function(){
  var _1fg/* s5Ep */ = B(_GQ/* Core.Shape.Internal.$wcenterRect */(_1fd/* Motion.Collide.lvl1 */, _1fd/* Motion.Collide.lvl1 */, _1fe/* Motion.Collide.lvl2 */, _1fe/* Motion.Collide.lvl2 */));
  return new T3(0,_1fg/* s5Ep */.a,_1fg/* s5Ep */.b,_1fg/* s5Ep */.c);
}),
_1fh/* lvl4 */ = function(_1fi/* s5Et */, _1fj/* s5Eu */){
  var _1fk/* s5Ez */ = B(A1(_1fi/* s5Et */,new T(function(){
    return 1-E(_1fj/* s5Eu */);
  })));
  return 1-_1fk/* s5Ez */*_1fk/* s5Ez */*_1fk/* s5Ez */*_1fk/* s5Ez */*_1fk/* s5Ez */;
},
_1fl/* lvl5 */ = function(_1fm/* s5EG */, _1fn/* s5EH */){
  var _1fo/* s5EM */ = B(A1(_1fm/* s5EG */,new T(function(){
    return 1-E(_1fn/* s5EH */);
  })));
  return 1-_1fo/* s5EM */*_1fo/* s5EM */*_1fo/* s5EM */;
},
_1fp/* lvl6 */ = -70,
_1fq/* lvl7 */ = function(_1fr/* s5ER */, _1fs/* s5ES */){
  return 1-B(A1(_1fr/* s5ER */,new T(function(){
    return Math.pow/* EXTERNAL */(2,  -((1-(1-E(_1fs/* s5ES */)))*10));
  })));
},
_1ft/* lvl8 */ = 0.6283185307179586,
_1fu/* quad */ = function(_1fv/* sbey */, _1fw/* sbez */){
  var _1fx/* sbeA */ = B(A1(_1fv/* sbey */,_1fw/* sbez */));
  return _1fx/* sbeA */*_1fx/* sbeA */;
},
_1fy/* collideMot */ = function(_1fz/* s5F4 */){
  var _1fA/* s5F5 */ = new T(function(){
    return B(_rB/* Core.Render.Internal.fill1 */(_1fz/* s5F4 */, _1ff/* Motion.Collide.lvl3 */));
  }),
  _1fB/* s5Ht */ = function(_1fC/* s5F6 */, _1fD/* s5F7 */){
    var _1fE/* s5Hs */ = function(_/* EXTERNAL */){
      var _1fF/* s5F9 */ = nMV/* EXTERNAL */(_1fc/* Motion.Collide.lvl17 */),
      _1fG/* s5Fb */ = _1fF/* s5F9 */,
      _1fH/* s5Fd */ = new T(function(){
        return B(_jN/* Core.Ease.$wforceTo */(_1fG/* s5Fb */, _1eY/* Motion.Collide.dur */));
      }),
      _1fI/* s5Fe */ = new T(function(){
        return B(_jN/* Core.Ease.$wforceTo */(_1fG/* s5Fb */, _1eW/* Motion.Collide.a3 */));
      }),
      _1fJ/* s5Ff */ = new T(function(){
        return B(_jN/* Core.Ease.$wforceTo */(_1fG/* s5Fb */, _1fp/* Motion.Collide.lvl6 */));
      }),
      _1fK/* s5Fg */ = new T(function(){
        return B(_jN/* Core.Ease.$wforceTo */(_1fG/* s5Fb */, _1f9/* Motion.Collide.x */));
      }),
      _1fL/* s5Fh */ = function(_1fM/* s5Fi */){
        return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1eY/* Motion.Collide.dur */, _1fq/* Motion.Collide.lvl7 */, _1fG/* s5Fb */, _1f9/* Motion.Collide.x */, function(_1fN/* s5Fj */){
          return E(_1fM/* s5Fi */);
        });});
      },
      _1fO/* s5Fl */ = function(_1fP/* s5Fm */){
        return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1eX/* Motion.Collide.b1 */, _1fu/* Core.Ease.quad */, _1fG/* s5Fb */, _1fp/* Motion.Collide.lvl6 */, function(_1fQ/* s5Fn */){
          return E(_1fP/* s5Fm */);
        });});
      },
      _1fR/* s5Fp */ = function(_1fS/* s5Fq */){
        return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1eY/* Motion.Collide.dur */, _1fl/* Motion.Collide.lvl5 */, _1fG/* s5Fb */, _1eW/* Motion.Collide.a3 */, function(_1fT/* s5Fr */){
          return E(_1fS/* s5Fq */);
        });});
      },
      _1fU/* s5Ft */ = function(_1fV/* s5Fu */){
        return new F(function(){return _iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1eY/* Motion.Collide.dur */, _1fh/* Motion.Collide.lvl4 */, _1fG/* s5Fb */, _1eY/* Motion.Collide.dur */, function(_1fW/* s5Fv */){
          return E(_1fV/* s5Fu */);
        });});
      },
      _1fX/* s5Hq */ = function(_/* EXTERNAL */){
        var _1fY/* s5Fy */ = nMV/* EXTERNAL */(_1f8/* Motion.Collide.lvl14 */),
        _1fZ/* s5FA */ = _1fY/* s5Fy */,
        _1g0/* s5FC */ = new T(function(){
          return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1eY/* Motion.Collide.dur */, _1fh/* Motion.Collide.lvl4 */, _1fZ/* s5FA */, _1eV/* Motion.Collide.a2 */, _Ac/* Core.Ease.easeTo1 */));
        }),
        _1g1/* s5FD */ = new T(function(){
          return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1eY/* Motion.Collide.dur */, _1fq/* Motion.Collide.lvl7 */, _1fZ/* s5FA */, _1f5/* Motion.Collide.x1 */, _Ac/* Core.Ease.easeTo1 */));
        }),
        _1g2/* s5FE */ = new T(function(){
          return B(_jN/* Core.Ease.$wforceTo */(_1fZ/* s5FA */, _1f5/* Motion.Collide.x1 */));
        }),
        _1g3/* s5Ho */ = function(_/* EXTERNAL */){
          var _1g4/* s5FG */ = nMV/* EXTERNAL */(_1f4/* Motion.Collide.lvl11 */);
          return new T(function(){
            var _1g5/* s5FK */ = new T(function(){
              return B(_jN/* Core.Ease.$wforceTo */(_1g4/* s5FG */, _1f1/* Motion.Collide.x2 */));
            }),
            _1g6/* s5FL */ = new T(function(){
              return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1eY/* Motion.Collide.dur */, _1fq/* Motion.Collide.lvl7 */, _1g4/* s5FG */, _1ft/* Motion.Collide.lvl8 */, _Ac/* Core.Ease.easeTo1 */));
            }),
            _1g7/* s5FM */ = new T(function(){
              return B(_iS/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _1eY/* Motion.Collide.dur */, _1fh/* Motion.Collide.lvl4 */, _1g4/* s5FG */, _1eV/* Motion.Collide.a2 */, _Ac/* Core.Ease.easeTo1 */));
            }),
            _1g8/* s5FN */ = function(_1g9/* s5FO */){
              var _1ga/* s5FP */ = new T(function(){
                return B(A1(_1g7/* s5FM */,_1g9/* s5FO */));
              }),
              _1gb/* s5H7 */ = function(_1gc/* s5FQ */){
                var _1gd/* s5FR */ = function(_1ge/* s5FS */){
                  return new F(function(){return A2(_1g8/* s5FN */,E(_1ge/* s5FS */).b, _1gc/* s5FQ */);});
                },
                _1gf/* s5FW */ = function(_1gg/* s5FX */){
                  return new F(function(){return A2(_1fK/* s5Fg */,E(_1gg/* s5FX */).b, _1gd/* s5FR */);});
                },
                _1gh/* s5G1 */ = function(_1gi/* s5G2 */){
                  return new F(function(){return A2(_1g2/* s5FE */,E(_1gi/* s5G2 */).b, _1gf/* s5FW */);});
                },
                _1gj/* s5G6 */ = function(_1gk/* s5G7 */){
                  return new F(function(){return A2(_1g5/* s5FK */,E(_1gk/* s5G7 */).b, _1gh/* s5G1 */);});
                },
                _1gl/* s5Gb */ = function(_1gm/* s5Gc */){
                  return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_1fL/* s5Fh */, E(_1gm/* s5Gc */).b, _1gj/* s5G6 */)));
                },
                _1gn/* s5Gi */ = function(_1go/* s5Gj */){
                  return new F(function(){return A2(_1g1/* s5FD */,E(_1go/* s5Gj */).b, _1gl/* s5Gb */);});
                },
                _1gp/* s5Gn */ = function(_1gq/* s5Go */){
                  return new F(function(){return A2(_1g6/* s5FL */,E(_1gq/* s5Go */).b, _1gn/* s5Gi */);});
                },
                _1gr/* s5Gs */ = function(_1gs/* s5Gt */){
                  return new F(function(){return A2(_1fJ/* s5Ff */,E(_1gs/* s5Gt */).b, _1gp/* s5Gn */);});
                },
                _1gt/* s5Gx */ = function(_1gu/* s5Gy */){
                  return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_1fO/* s5Fl */, E(_1gu/* s5Gy */).b, _1gr/* s5Gs */)));
                },
                _1gv/* s5GE */ = function(_1gw/* s5GF */){
                  return new F(function(){return A2(_1fI/* s5Fe */,E(_1gw/* s5GF */).b, _1gt/* s5Gx */);});
                },
                _1gx/* s5GJ */ = function(_1gy/* s5GK */){
                  return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_1fR/* s5Fp */, E(_1gy/* s5GK */).b, _1gv/* s5GE */)));
                },
                _1gz/* s5GQ */ = function(_1gA/* s5GR */){
                  return new F(function(){return A2(_1fH/* s5Fd */,E(_1gA/* s5GR */).b, _1gx/* s5GJ */);});
                },
                _1gB/* s5GV */ = function(_1gC/* s5GW */){
                  return new T1(0,B(_ij/* Core.World.Internal.$wa6 */(_1fU/* s5Ft */, E(_1gC/* s5GW */).b, _1gz/* s5GQ */)));
                };
                return new F(function(){return A1(_1ga/* s5FP */,function(_1gD/* s5H2 */){
                  return new F(function(){return A2(_1g0/* s5FC */,E(_1gD/* s5H2 */).b, _1gB/* s5GV */);});
                });});
              };
              return E(_1gb/* s5H7 */);
            },
            _1gE/* s5Hk */ = new T(function(){
              return B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,new T(function(){
                return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _1f0/* Motion.Collide.lvl */, new T2(2,new T3(0,_1eY/* Motion.Collide.dur */,_15I/* Core.Ease.cubic */,_1fG/* s5Fb */),_2E/* GHC.Base.id */)));
              }),new T(function(){
                return B(_sg/* Core.Ease.opLift */(_tr/* GHC.Float.plusDouble */, _1f0/* Motion.Collide.lvl */, new T2(2,new T3(0,_1eY/* Motion.Collide.dur */,_15I/* Core.Ease.cubic */,_1fZ/* s5FA */),_2E/* GHC.Base.id */)));
              })),new T(function(){
                return B(_rx/* Control.Monad.Skeleton.bone */(new T3(6,new T2(2,new T3(0,_1eY/* Motion.Collide.dur */,_15I/* Core.Ease.cubic */,_1g4/* s5FG */),_2E/* GHC.Base.id */),_1fA/* s5F5 */,_7/* GHC.Tuple.() */)));
              }),_7/* GHC.Tuple.() */)));
            });
            return B(A1(_1fD/* s5F7 */,new T2(0,new T2(0,_1gE/* s5Hk */,_1g8/* s5FN */),_1fC/* s5F6 */)));
          });
        };
        return new T1(0,_1g3/* s5Ho */);
      };
      return new T1(0,_1fX/* s5Hq */);
    };
    return new T1(0,_1fE/* s5Hs */);
  };
  return E(_1fB/* s5Ht */);
},
_1gF/* lvl72 */ = new T4(0,_Al/* Motion.Main.lvl11 */,_Jl/* Motion.Main.lvl45 */,_yT/* Motion.Main.lvl4 */,_Al/* Motion.Main.lvl11 */),
_1gG/* lvl73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Collide"));
}),
_1gH/* lvl74 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("easeOutCubic \u2192 easeInQuad \u2192 easeOutExpo"));
}),
_1gI/* lvl75 */ = new T(function(){
  return B(_Fm/* Motion.Main.consView */(_1gF/* Motion.Main.lvl72 */, _1fy/* Motion.Collide.collideMot */, _1gG/* Motion.Main.lvl73 */, _1gH/* Motion.Main.lvl74 */));
}),
_1gJ/* lvl76 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("height"));
}),
_1gK/* lvl77 */ = 1,
_1gL/* lvl78 */ = new T1(1,_6/* GHC.Types.[] */),
_1gM/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.scale(x,y);})");
}),
_1gN/* f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,rad){ctx.rotate(rad);})");
}),
_1gO/* f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.translate(x,y);})");
}),
_1gP/* f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})");
}),
_1gQ/* render2 */ = function(_1gR/*  sFRJ */, _1gS/*  sFRK */, _/* EXTERNAL */){
  while(1){
    var _1gT/*  render2 */ = B((function(_1gU/* sFRJ */, _1gV/* sFRK */, _/* EXTERNAL */){
      var _1gW/* sFRM */ = B(_fo/* Control.Monad.Skeleton.debone */(_1gU/* sFRJ */));
      if(!_1gW/* sFRM */._){
        return _1gW/* sFRM */.a;
      }else{
        var _1gX/* sFRP */ = _1gW/* sFRM */.b,
        _1gY/* sFRQ */ = E(_1gW/* sFRM */.a);
        switch(_1gY/* sFRQ */._){
          case 0:
            var _1gZ/* sFRT */ = B(A2(_1gY/* sFRQ */.a,_1gV/* sFRK */, _/* EXTERNAL */)),
            _1h0/*   sFRK */ = _1gV/* sFRK */;
            _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1gY/* sFRQ */.b));
            _1gS/*  sFRK */ = _1h0/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 1:
            var _1h1/* sFRY */ = B(A1(_1gY/* sFRQ */.a,_/* EXTERNAL */)),
            _1h0/*   sFRK */ = _1gV/* sFRK */;
            _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1h1/* sFRY */));
            _1gS/*  sFRK */ = _1h0/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 2:
            var _1h0/*   sFRK */ = _1gV/* sFRK */;
            _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1gY/* sFRQ */.b));
            _1gS/*  sFRK */ = _1h0/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 3:
            var _1h2/* sFS8 */ = B(_1gQ/* Core.Render.Internal.render2 */(_1gY/* sFRQ */.b, _1gY/* sFRQ */.a, _/* EXTERNAL */)),
            _1h0/*   sFRK */ = _1gV/* sFRK */;
            _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1gY/* sFRQ */.c));
            _1gS/*  sFRK */ = _1h0/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 4:
            var _1h3/* sFSj */ = _1gY/* sFRQ */.h,
            _1h4/* sFSk */ = function(_1h5/* sFSl */, _/* EXTERNAL */){
              var _1h6/* sFTp */ = function(_1h7/* sFSn */, _/* EXTERNAL */){
                var _1h8/* sFTo */ = function(_1h9/* sFSp */, _/* EXTERNAL */){
                  var _1ha/* sFTn */ = function(_1hb/* sFSr */, _/* EXTERNAL */){
                    var _1hc/* sFTm */ = function(_1hd/* sFSt */, _/* EXTERNAL */){
                      return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1gY/* sFRQ */.f, function(_1he/* sFSv */, _/* EXTERNAL */){
                        var _1hf/* sFSx */ = E(_1gV/* sFRK */),
                        _1hg/* sFSC */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _1hf/* sFSx */),
                        _1hh/* sFT9 */ = __apply/* EXTERNAL */(E(_1gP/* Core.Render.Internal.f4 */), new T2(1,E(_1he/* sFSv */),new T2(1,E(_1hd/* sFSt */),new T2(1,E(_1hb/* sFSr */),new T2(1,E(_1h9/* sFSp */),new T2(1,E(_1h7/* sFSn */),new T2(1,E(_1h5/* sFSl */),new T2(1,_1hf/* sFSx */,_6/* GHC.Types.[] */)))))))),
                        _1hi/* sFTc */ = B(_1gQ/* Core.Render.Internal.render2 */(_1gY/* sFRQ */.g, _1hf/* sFSx */, _/* EXTERNAL */)),
                        _1hj/* sFTi */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), _1hf/* sFSx */);
                        return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
                      }, _/* EXTERNAL */);});
                    };
                    return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1gY/* sFRQ */.e, _1hc/* sFTm */, _/* EXTERNAL */);});
                  };
                  return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1gY/* sFRQ */.d, _1ha/* sFTn */, _/* EXTERNAL */);});
                };
                return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1gY/* sFRQ */.c, _1h8/* sFTo */, _/* EXTERNAL */);});
              };
              return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1gY/* sFRQ */.b, _1h6/* sFTp */, _/* EXTERNAL */);});
            },
            _1hk/* sFTq */ = E(_1gY/* sFRQ */.a);
            switch(_1hk/* sFTq */._){
              case 0:
                var _1hl/* sFTs */ = B(_1h4/* sFSk */(_1hk/* sFTq */.a, _/* EXTERNAL */)),
                _1h0/*   sFRK */ = _1gV/* sFRK */;
                _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1h3/* sFSj */));
                _1gS/*  sFRK */ = _1h0/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _1hm/* sFTx */ = B(A1(_1hk/* sFTq */.a,_/* EXTERNAL */)),
                _1hn/* sFTA */ = B(_1h4/* sFSk */(_1hm/* sFTx */, _/* EXTERNAL */)),
                _1h0/*   sFRK */ = _1gV/* sFRK */;
                _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1h3/* sFSj */));
                _1gS/*  sFRK */ = _1h0/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _1ho/* sFTM */ = rMV/* EXTERNAL */(E(E(_1hk/* sFTq */.a).c)),
                _1hp/* sFTP */ = E(_1ho/* sFTM */);
                if(!_1hp/* sFTP */._){
                  var _1hq/* sFTT */ = new T(function(){
                    return B(A1(_1hk/* sFTq */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_1hp/* sFTP */.a));
                    })));
                  },1),
                  _1hr/* sFTU */ = B(_1h4/* sFSk */(_1hq/* sFTT */, _/* EXTERNAL */)),
                  _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1h3/* sFSj */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1h3/* sFSj */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _1hs/* sFU8 */ = rMV/* EXTERNAL */(E(E(_1hk/* sFTq */.a).c)),
                _1ht/* sFUb */ = E(_1hs/* sFU8 */);
                if(!_1ht/* sFUb */._){
                  var _1hu/* sFUh */ = B(A2(_1hk/* sFTq */.b,E(_1ht/* sFUb */.a).a, _/* EXTERNAL */)),
                  _1hv/* sFUk */ = B(_1h4/* sFSk */(_1hu/* sFUh */, _/* EXTERNAL */)),
                  _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1h3/* sFSj */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1h3/* sFSj */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 5:
            var _1hw/* sFUs */ = _1gY/* sFRQ */.c,
            _1hx/* sFUt */ = E(_1gY/* sFRQ */.a),
            _1hy/* sFUw */ = function(_1hz/* sFUx */, _/* EXTERNAL */){
              return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1hx/* sFUt */.b, function(_1hA/* sFUz */, _/* EXTERNAL */){
                var _1hB/* sFUB */ = E(_1gV/* sFRK */),
                _1hC/* sFUG */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _1hB/* sFUB */),
                _1hD/* sFUU */ = __app3/* EXTERNAL */(E(_1gO/* Core.Render.Internal.f3 */), _1hB/* sFUB */, E(_1hz/* sFUx */), E(_1hA/* sFUz */)),
                _1hE/* sFUX */ = B(_1gQ/* Core.Render.Internal.render2 */(_1gY/* sFRQ */.b, _1hB/* sFUB */, _/* EXTERNAL */)),
                _1hF/* sFV3 */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), _1hB/* sFUB */);
                return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _1hG/* sFV7 */ = E(_1hx/* sFUt */.a);
            switch(_1hG/* sFV7 */._){
              case 0:
                var _1hH/* sFV9 */ = B(_1hy/* sFUw */(_1hG/* sFV7 */.a, _/* EXTERNAL */)),
                _1h0/*   sFRK */ = _1gV/* sFRK */;
                _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hw/* sFUs */));
                _1gS/*  sFRK */ = _1h0/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _1hI/* sFVe */ = B(A1(_1hG/* sFV7 */.a,_/* EXTERNAL */)),
                _1hJ/* sFVh */ = B(_1hy/* sFUw */(_1hI/* sFVe */, _/* EXTERNAL */)),
                _1h0/*   sFRK */ = _1gV/* sFRK */;
                _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hw/* sFUs */));
                _1gS/*  sFRK */ = _1h0/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _1hK/* sFVt */ = rMV/* EXTERNAL */(E(E(_1hG/* sFV7 */.a).c)),
                _1hL/* sFVw */ = E(_1hK/* sFVt */);
                if(!_1hL/* sFVw */._){
                  var _1hM/* sFVA */ = new T(function(){
                    return B(A1(_1hG/* sFV7 */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_1hL/* sFVw */.a));
                    })));
                  },1),
                  _1hN/* sFVB */ = B(_1hy/* sFUw */(_1hM/* sFVA */, _/* EXTERNAL */)),
                  _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hw/* sFUs */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hw/* sFUs */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _1hO/* sFVP */ = rMV/* EXTERNAL */(E(E(_1hG/* sFV7 */.a).c)),
                _1hP/* sFVS */ = E(_1hO/* sFVP */);
                if(!_1hP/* sFVS */._){
                  var _1hQ/* sFVY */ = B(A2(_1hG/* sFV7 */.b,E(_1hP/* sFVS */.a).a, _/* EXTERNAL */)),
                  _1hR/* sFW1 */ = B(_1hy/* sFUw */(_1hQ/* sFVY */, _/* EXTERNAL */)),
                  _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hw/* sFUs */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hw/* sFUs */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 6:
            var _1hS/* sFW9 */ = _1gY/* sFRQ */.c,
            _1hT/* sFWa */ = function(_1hU/* sFWb */, _/* EXTERNAL */){
              var _1hV/* sFWd */ = E(_1gV/* sFRK */),
              _1hW/* sFWi */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _1hV/* sFWd */),
              _1hX/* sFWs */ = __app2/* EXTERNAL */(E(_1gN/* Core.Render.Internal.f2 */), _1hV/* sFWd */, E(_1hU/* sFWb */)),
              _1hY/* sFWv */ = B(_1gQ/* Core.Render.Internal.render2 */(_1gY/* sFRQ */.b, _1hV/* sFWd */, _/* EXTERNAL */)),
              _1hZ/* sFWB */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), _1hV/* sFWd */);
              return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
            },
            _1i0/* sFWE */ = E(_1gY/* sFRQ */.a);
            switch(_1i0/* sFWE */._){
              case 0:
                var _1i1/* sFWG */ = B(_1hT/* sFWa */(_1i0/* sFWE */.a, _/* EXTERNAL */)),
                _1h0/*   sFRK */ = _1gV/* sFRK */;
                _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hS/* sFW9 */));
                _1gS/*  sFRK */ = _1h0/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _1i2/* sFWL */ = B(A1(_1i0/* sFWE */.a,_/* EXTERNAL */)),
                _1i3/* sFWO */ = B(_1hT/* sFWa */(_1i2/* sFWL */, _/* EXTERNAL */)),
                _1h0/*   sFRK */ = _1gV/* sFRK */;
                _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hS/* sFW9 */));
                _1gS/*  sFRK */ = _1h0/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _1i4/* sFX0 */ = rMV/* EXTERNAL */(E(E(_1i0/* sFWE */.a).c)),
                _1i5/* sFX3 */ = E(_1i4/* sFX0 */);
                if(!_1i5/* sFX3 */._){
                  var _1i6/* sFX7 */ = new T(function(){
                    return B(A1(_1i0/* sFWE */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_1i5/* sFX3 */.a));
                    })));
                  },1),
                  _1i7/* sFX8 */ = B(_1hT/* sFWa */(_1i6/* sFX7 */, _/* EXTERNAL */)),
                  _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hS/* sFW9 */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hS/* sFW9 */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _1i8/* sFXm */ = rMV/* EXTERNAL */(E(E(_1i0/* sFWE */.a).c)),
                _1i9/* sFXp */ = E(_1i8/* sFXm */);
                if(!_1i9/* sFXp */._){
                  var _1ia/* sFXv */ = B(A2(_1i0/* sFWE */.b,E(_1i9/* sFXp */.a).a, _/* EXTERNAL */)),
                  _1ib/* sFXy */ = B(_1hT/* sFWa */(_1ia/* sFXv */, _/* EXTERNAL */)),
                  _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hS/* sFW9 */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1hS/* sFW9 */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 7:
            var _1ic/* sFXG */ = _1gY/* sFRQ */.c,
            _1id/* sFXH */ = E(_1gY/* sFRQ */.a),
            _1ie/* sFXK */ = function(_1if/* sFXL */, _/* EXTERNAL */){
              return new F(function(){return _xc/* Core.Render.Internal.getImage2 */(_1id/* sFXH */.b, function(_1ig/* sFXN */, _/* EXTERNAL */){
                var _1ih/* sFXP */ = E(_1gV/* sFRK */),
                _1ii/* sFXU */ = __app1/* EXTERNAL */(E(_xb/* Core.Render.Internal.clip_f4 */), _1ih/* sFXP */),
                _1ij/* sFY8 */ = __app3/* EXTERNAL */(E(_1gM/* Core.Render.Internal.f1 */), _1ih/* sFXP */, E(_1if/* sFXL */), E(_1ig/* sFXN */)),
                _1ik/* sFYb */ = B(_1gQ/* Core.Render.Internal.render2 */(_1gY/* sFRQ */.b, _1ih/* sFXP */, _/* EXTERNAL */)),
                _1il/* sFYh */ = __app1/* EXTERNAL */(E(_x2/* Core.Render.Internal.clip_f1 */), _1ih/* sFXP */);
                return new F(function(){return _ky/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _1im/* sFYl */ = E(_1id/* sFXH */.a);
            switch(_1im/* sFYl */._){
              case 0:
                var _1in/* sFYn */ = B(_1ie/* sFXK */(_1im/* sFYl */.a, _/* EXTERNAL */)),
                _1h0/*   sFRK */ = _1gV/* sFRK */;
                _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1ic/* sFXG */));
                _1gS/*  sFRK */ = _1h0/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _1io/* sFYs */ = B(A1(_1im/* sFYl */.a,_/* EXTERNAL */)),
                _1ip/* sFYv */ = B(_1ie/* sFXK */(_1io/* sFYs */, _/* EXTERNAL */)),
                _1h0/*   sFRK */ = _1gV/* sFRK */;
                _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1ic/* sFXG */));
                _1gS/*  sFRK */ = _1h0/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _1iq/* sFYH */ = rMV/* EXTERNAL */(E(E(_1im/* sFYl */.a).c)),
                _1ir/* sFYK */ = E(_1iq/* sFYH */);
                if(!_1ir/* sFYK */._){
                  var _1is/* sFYO */ = new T(function(){
                    return B(A1(_1im/* sFYl */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_1ir/* sFYK */.a));
                    })));
                  },1),
                  _1it/* sFYP */ = B(_1ie/* sFXK */(_1is/* sFYO */, _/* EXTERNAL */)),
                  _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1ic/* sFXG */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1ic/* sFXG */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _1iu/* sFZ3 */ = rMV/* EXTERNAL */(E(E(_1im/* sFYl */.a).c)),
                _1iv/* sFZ6 */ = E(_1iu/* sFZ3 */);
                if(!_1iv/* sFZ6 */._){
                  var _1iw/* sFZc */ = B(A2(_1im/* sFYl */.b,E(_1iv/* sFZ6 */.a).a, _/* EXTERNAL */)),
                  _1ix/* sFZf */ = B(_1ie/* sFXK */(_1iw/* sFZc */, _/* EXTERNAL */)),
                  _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1ic/* sFXG */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _1h0/*   sFRK */ = _1gV/* sFRK */;
                  _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1ic/* sFXG */));
                  _1gS/*  sFRK */ = _1h0/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          default:
            var _1iy/* sFZo */ = B(_1gQ/* Core.Render.Internal.render2 */(_1gY/* sFRQ */.a, _1gV/* sFRK */, _/* EXTERNAL */)),
            _1h0/*   sFRK */ = _1gV/* sFRK */;
            _1gR/*  sFRJ */ = B(A1(_1gX/* sFRP */,_1gY/* sFRQ */.c));
            _1gS/*  sFRK */ = _1h0/*   sFRK */;
            return __continue/* EXTERNAL */;
        }
      }
    })(_1gR/*  sFRJ */, _1gS/*  sFRK */, _/* EXTERNAL */));
    if(_1gT/*  render2 */!=__continue/* EXTERNAL */){
      return _1gT/*  render2 */;
    }
  }
},
_1iz/* a12 */ = new T1(0,_/* EXTERNAL */),
_1iA/* a13 */ = new T1(0,_6/* GHC.Types.[] */),
_1iB/* a14 */ = new T2(0,E(_1iA/* Motion.Main.a13 */),E(_1iz/* Motion.Main.a12 */)),
_1iC/* pad */ = 40,
_1iD/* lvl1 */ = new T1(0,_1iC/* Motion.Main.pad */),
_1iE/* rendering1 */ = function(_1iF/* sWcL */){
  return E(E(_1iF/* sWcL */).b);
},
_1iG/* renderContents_go */ = function(_1iH/* s7KR */, _1iI/* s7KS */){
  var _1iJ/* s7KT */ = E(_1iH/* s7KR */);
  if(!_1iJ/* s7KT */._){
    return E(_1iB/* Motion.Main.a14 */);
  }else{
    var _1iK/* s7KW */ = E(_1iI/* s7KS */);
    if(!_1iK/* s7KW */._){
      return E(_1iB/* Motion.Main.a14 */);
    }else{
      var _1iL/* s7L9 */ = B(_rx/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_1iD/* Motion.Main.lvl1 */,new T1(0,new T(function(){
        return 40+190*E(_1iJ/* s7KT */.a);
      }))),new T(function(){
        return B(_1iE/* Core.View.rendering1 */(_1iK/* s7KW */.a));
      }),_7/* GHC.Tuple.() */))),
      _1iM/* s7Lc */ = new T(function(){
        return B(_1iG/* Motion.Main.renderContents_go */(_1iJ/* s7KT */.b, _1iK/* s7KW */.b));
      }),
      _1iN/* s7Ln */ = function(_1iO/* s7Ld */){
        var _1iP/* s7Le */ = E(_1iM/* s7Lc */);
        return new T2(0,E(_1iP/* s7Le */.a),E(new T2(2,_1iP/* s7Le */.b,new T1(1,function(_1iQ/* s7Lh */){
          return new T2(0,E(new T1(0,new T2(1,_1iO/* s7Ld */,_1iQ/* s7Lh */))),E(_1iz/* Motion.Main.a12 */));
        }))));
      };
      return new T2(0,E(_1iL/* s7L9 */.a),E(new T2(2,_1iL/* s7L9 */.b,new T1(1,_1iN/* s7Ln */))));
    }
  }
},
_1iR/* renderContents1 */ = function(_1iS/* s7Lq */){
  return new F(function(){return _rp/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
    return B(_1iG/* Motion.Main.renderContents_go */(_Im/* Core.Util.iforM1 */, _1iS/* s7Lq */));
  }));});
},
_1iT/* launch1 */ = function(_1iU/* s7MZ */, _1iV/* s7N0 */){
  var _1iW/* s7N1 */ = function(_1iX/* s7N2 */, _/* EXTERNAL */){
    var _1iY/* s7N4 */ = E(_1iU/* s7MZ */),
    _1iZ/* s7Na */ = __app1/* EXTERNAL */(E(_ib/* Haste.Graphics.Canvas.buffer_f1 */), _1iY/* s7N4 */.b);
    return new F(function(){return _1gQ/* Core.Render.Internal.render2 */(B(_1iR/* Motion.Main.renderContents1 */(_1iX/* s7N2 */)), _1iY/* s7N4 */.a, _/* EXTERNAL */);});
  },
  _1j0/* s7Nf */ = new T(function(){
    return B(A1(_G4/* Motion.Main.lvl41 */,_1iV/* s7N0 */));
  }),
  _1j1/* s7Pk */ = function(_1j2/* s7Ng */){
    var _1j3/* s7Pj */ = function(_1j4/* s7Nh */){
      var _1j5/* s7Ni */ = E(_1j4/* s7Nh */),
      _1j6/* s7Pi */ = function(_1j7/* s7Nl */){
        var _1j8/* s7Nm */ = E(_1j7/* s7Nl */),
        _1j9/* s7Ph */ = function(_1ja/* s7Np */){
          var _1jb/* s7Nq */ = E(_1ja/* s7Np */),
          _1jc/* s7Pg */ = function(_1jd/* s7Nt */){
            var _1je/* s7Nu */ = E(_1jd/* s7Nt */),
            _1jf/* s7Pf */ = function(_1jg/* s7Nx */){
              var _1jh/* s7Ny */ = E(_1jg/* s7Nx */),
              _1ji/* s7Pe */ = function(_1jj/* s7NB */){
                var _1jk/* s7NC */ = E(_1jj/* s7NB */),
                _1jl/* s7Pd */ = function(_1jm/* s7NF */){
                  var _1jn/* s7NG */ = E(_1jm/* s7NF */),
                  _1jo/* s7Pc */ = function(_1jp/* s7NJ */){
                    var _1jq/* s7NK */ = E(_1jp/* s7NJ */),
                    _1jr/* s7NU */ = new T2(1,_1j5/* s7Ni */.a,new T2(1,_1j8/* s7Nm */.a,new T2(1,_1jb/* s7Nq */.a,new T2(1,_1je/* s7Nu */.a,new T2(1,_1jh/* s7Ny */.a,new T2(1,_1jk/* s7NC */.a,new T2(1,_1jn/* s7NG */.a,new T2(1,_1jq/* s7NK */.a,_6/* GHC.Types.[] */)))))))),
                    _1js/* s7Pb */ = function(_/* EXTERNAL */){
                      var _1jt/* s7O9 */ = jsShow/* EXTERNAL */(40+B(_eT/* GHC.List.$wlenAcc */(_1jr/* s7NU */, 0))*190),
                      _1ju/* s7Ol */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), E(_1iU/* s7MZ */).b, toJSStr/* EXTERNAL */(E(_1gJ/* Motion.Main.lvl76 */)), toJSStr/* EXTERNAL */(fromJSStr/* EXTERNAL */(_1jt/* s7O9 */))),
                      _1jv/* s7P9 */ = function(_/* EXTERNAL */){
                        var _1jw/* s7Oq */ = nMV/* EXTERNAL */(new T2(0,_1jr/* s7NU */,_6/* GHC.Types.[] */));
                        return new T(function(){
                          var _1jx/* s7Ou */ = new T(function(){
                            return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _1jw/* s7Oq */, _eY/* Motion.Main.a24 */));
                          }),
                          _1jy/* s7Ow */ = function(_1jz/* s7OC */){
                            return new F(function(){return _1jA/* s7Oz */(E(_1jz/* s7OC */).b);});
                          },
                          _1jB/* s7Ox */ = function(_1jC/* s7OG */){
                            return new F(function(){return _tv/* Core.World.Internal.sleep1 */(_1gK/* Motion.Main.lvl77 */, E(_1jC/* s7OG */).b, _1jy/* s7Ow */);});
                          },
                          _1jD/* s7Oy */ = function(_1jE/* s7OK */){
                            var _1jF/* s7OL */ = E(_1jE/* s7OK */);
                            return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[B(_1iR/* Motion.Main.renderContents1 */(_1jF/* s7OL */.a)), _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _1jF/* s7OL */.b, _1jB/* s7Ox */]);});
                          },
                          _1jA/* s7Oz */ = function(_1jG/* s7OP */){
                            return new F(function(){return A2(_1jx/* s7Ou */,_1jG/* s7OP */, _1jD/* s7Oy */);});
                          },
                          _1jH/* s7P5 */ = function(_1jI/* s7OQ */){
                            var _1jJ/* s7OT */ = E(_1jI/* s7OQ */).b,
                            _1jK/* s7P4 */ = function(_/* EXTERNAL */){
                              var _1jL/* s7OV */ = nMV/* EXTERNAL */(_1gL/* Motion.Main.lvl78 */);
                              return new T1(1,new T2(1,new T(function(){
                                return B(A1(_1j2/* s7Ng */,new T2(0,_7/* GHC.Tuple.() */,_1jJ/* s7OT */)));
                              }),new T2(1,new T(function(){
                                return B(_1jA/* s7Oz */(_1jJ/* s7OT */));
                              }),_6/* GHC.Types.[] */)));
                            };
                            return new T1(0,_1jK/* s7P4 */);
                          };
                          return new T1(0,B(_e8/* Core.Front.Internal.$wa */(_1jw/* s7Oq */, _1iW/* s7N1 */, _1jq/* s7NK */.b, _1jH/* s7P5 */)));
                        });
                      };
                      return new T1(0,_1jv/* s7P9 */);
                    };
                    return new T1(0,_1js/* s7Pb */);
                  };
                  return new F(function(){return A2(_1gI/* Motion.Main.lvl75 */,_1jn/* s7NG */.b, _1jo/* s7Pc */);});
                };
                return new F(function(){return A2(_1eU/* Motion.Main.lvl71 */,_1jk/* s7NC */.b, _1jl/* s7Pd */);});
              };
              return new F(function(){return A2(_1c3/* Motion.Main.lvl67 */,_1jh/* s7Ny */.b, _1ji/* s7Pe */);});
            };
            return new F(function(){return A2(_16S/* Motion.Main.lvl63 */,_1je/* s7Nu */.b, _1jf/* s7Pf */);});
          };
          return new F(function(){return A2(_15E/* Motion.Main.lvl59 */,_1jb/* s7Nq */.b, _1jc/* s7Pg */);});
        };
        return new F(function(){return A2(_Z3/* Motion.Main.lvl53 */,_1j8/* s7Nm */.b, _1j9/* s7Ph */);});
      };
      return new F(function(){return A2(_Jp/* Motion.Main.lvl49 */,_1j5/* s7Ni */.b, _1j6/* s7Pi */);});
    };
    return new F(function(){return A1(_1j0/* s7Nf */,_1j3/* s7Pj */);});
  };
  return E(_1j1/* s7Pk */);
},
_1jM/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Canvas not found!"));
}),
_1jN/* main2 */ = new T(function(){
  return B(err/* EXTERNAL */(_1jM/* Main.lvl */));
}),
_1jO/* main3 */ = "canvas",
_1jP/* start_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(Util.onload)");
}),
_1jQ/* main1 */ = function(_/* EXTERNAL */){
  var _1jR/* s11fh */ = __app1/* EXTERNAL */(E(_1jP/* Core.Front.Internal.start_f1 */), E(_48/* Haste.Prim.Any.jsNull */)),
  _1jS/* s11fk */ = B(A3(_e1/* Haste.DOM.JSString.elemById */,_2G/* Control.Monad.IO.Class.$fMonadIOIO */, _1jO/* Main.main3 */, _/* EXTERNAL */)),
  _1jT/* s11fn */ = E(_1jS/* s11fk */);
  if(!_1jT/* s11fn */._){
    return E(_1jN/* Main.main2 */);
  }else{
    var _1jU/* s11fq */ = E(_1jT/* s11fn */.a),
    _1jV/* s11fv */ = __app1/* EXTERNAL */(E(_1/* Haste.Graphics.Canvas.$fFromAnyCanvas_f2 */), _1jU/* s11fq */);
    if(!_1jV/* s11fv */){
      return E(_1jN/* Main.main2 */);
    }else{
      var _1jW/* s11fD */ = __app1/* EXTERNAL */(E(_0/* Haste.Graphics.Canvas.$fFromAnyCanvas_f1 */), _1jU/* s11fq */),
      _1jX/* s11fF */ = _1jW/* s11fD */,
      _1jY/* s11fK */ = new T(function(){
        return new T1(0,B(_d7/* Core.World.Internal.$wa5 */(function(_1jZ/* B1 */){
          return new F(function(){return _1iT/* Motion.Main.launch1 */(new T2(0,_1jX/* s11fF */,_1jU/* s11fq */), _1jZ/* B1 */);});
        }, _2I/* Haste.Concurrent.Monad.forkIO1 */)));
      });
      return new F(function(){return _e/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(_1jY/* s11fK */, _6/* GHC.Types.[] */, _/* EXTERNAL */);});
    }
  }
},
_1k0/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _1jQ/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_1k0, [0]));};window.onload = hasteMain;