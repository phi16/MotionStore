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
_eY/* a22 */ = function(_eZ/* s7Bs */, _f0/* s7Bt */, _f1/* s7Bu */){
  return new F(function(){return A1(_f1/* s7Bu */,new T2(0,new T2(0,_eZ/* s7Bs */,_eZ/* s7Bs */),_f0/* s7Bt */));});
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
_ii/* a7 */ = function(_ij/* slbp */, _ik/* slbq */, _il/* slbr */){
  var _im/* slbs */ = new T(function(){
    return E(E(_ij/* slbp */).b);
  });
  return new F(function(){return A1(_il/* slbr */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,new T(function(){
    return E(E(_ij/* slbp */).a);
  }),new T4(0,new T(function(){
    return E(E(_im/* slbs */).a);
  }),new T(function(){
    return E(E(_im/* slbs */).b);
  }),new T(function(){
    return E(E(_im/* slbs */).c);
  }),_av/* GHC.Types.False */))),_ik/* slbq */));});
},
_in/* divideDouble */ = function(_io/* s18yD */, _ip/* s18yE */){
  return E(_io/* s18yD */)/E(_ip/* s18yE */);
},
_iq/* ease2 */ = 0,
_ir/* easeRegister1 */ = function(_is/* sc33 */, _it/* sc34 */, _iu/* sc35 */, _iv/* sc36 */){
  var _iw/* sc3k */ = function(_ix/* sc38 */, _iy/* sc39 */, _iz/* sc3a */){
    return new F(function(){return A1(_iz/* sc3a */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T(function(){
      var _iA/* sc3b */ = E(_ix/* sc38 */);
      return new T4(0,E(new T2(1,new T2(0,_is/* sc33 */,_it/* sc34 */),_iA/* sc3b */.a)),_iA/* sc3b */.b,E(_iA/* sc3b */.c),E(_iA/* sc3b */.d));
    })),_iy/* sc39 */));});
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _iu/* sc35 */, _iw/* sc3k */, _iu/* sc35 */, _iv/* sc36 */]);});
},
_iB/* $weaseHandle */ = function(_iC/* slbW */, _iD/* slbX */, _iE/* slbY */, _iF/* slbZ */, _iG/* slc0 */, _iH/* slc1 */){
  var _iI/* slc2 */ = new T(function(){
    var _iJ/* slc3 */ = new T(function(){
      return B(A1(_iE/* slbY */,_2E/* GHC.Base.id */));
    }),
    _iK/* slcm */ = function(_iL/* slc4 */, _iM/* slc5 */, _iN/* slc6 */){
      var _iO/* slc7 */ = E(_iL/* slc4 */),
      _iP/* slca */ = E(_iO/* slc7 */.b),
      _iQ/* slch */ = new T(function(){
        var _iR/* slcg */ = new T(function(){
          return B(A1(_iJ/* slc3 */,new T(function(){
            return B(_in/* GHC.Float.divideDouble */(_iP/* slca */.c, _iD/* slbX */));
          })));
        });
        return B(A3(_iC/* slbW */,_iR/* slcg */, _iP/* slca */.a, _iP/* slca */.b));
      });
      return new F(function(){return A1(_iN/* slc6 */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_iO/* slc7 */.a,new T4(0,_iQ/* slch */,_iG/* slc0 */,_iq/* Core.Ease.ease2 */,_iP/* slca */.d))),_iM/* slc5 */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iF/* slbZ */, _iK/* slcm */));
  }),
  _iS/* slcn */ = new T(function(){
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iF/* slbZ */, _ii/* Core.Ease.a7 */));
  }),
  _iT/* slco */ = new T(function(){
    var _iU/* slcp */ = new T(function(){
      return B(A1(_iH/* slc1 */,_av/* GHC.Types.False */));
    }),
    _iV/* slcq */ = new T(function(){
      return B(A1(_iH/* slc1 */,_aw/* GHC.Types.True */));
    }),
    _iW/* slcr */ = new T(function(){
      return B(A1(_iE/* slbY */,_2E/* GHC.Base.id */));
    }),
    _iX/* slde */ = function(_iY/* slcs */, _iZ/* slct */, _j0/* slcu */){
      var _j1/* slcv */ = E(_iY/* slcs */),
      _j2/* slcy */ = E(_j1/* slcv */.b),
      _j3/* slcz */ = _j2/* slcy */.a,
      _j4/* slcA */ = _j2/* slcy */.b;
      if(!E(_j2/* slcy */.d)){
        var _j5/* slcE */ = E(_iD/* slbX */),
        _j6/* slcI */ = E(_j2/* slcy */.c)+1,
        _j7/* slcJ */ = function(_j8/* slcK */, _j9/* slcL */){
          var _ja/* slcM */ = new T(function(){
            var _jb/* slcP */ = new T(function(){
              return B(A1(_iW/* slcr */,new T(function(){
                return _j8/* slcK *//_j5/* slcE */;
              })));
            });
            return B(A3(_iC/* slbW */,_jb/* slcP */, _j3/* slcz */, _j4/* slcA */));
          }),
          _jc/* slcQ */ = new T4(0,_j3/* slcz */,_j4/* slcA */,_j9/* slcL */,_aw/* GHC.Types.True */);
          if(_j8/* slcK */>=_j5/* slcE */){
            return new F(function(){return A2(_iV/* slcq */,_iZ/* slct */, function(_jd/* slcV */){
              return new F(function(){return A1(_j0/* slcu */,new T2(0,new T2(0,_av/* GHC.Types.False */,new T2(0,_ja/* slcM */,_jc/* slcQ */)),E(_jd/* slcV */).b));});
            });});
          }else{
            return new F(function(){return A1(_j0/* slcu */,new T2(0,new T2(0,_aw/* GHC.Types.True */,new T2(0,_ja/* slcM */,_jc/* slcQ */)),_iZ/* slct */));});
          }
        };
        if(_j5/* slcE */>_j6/* slcI */){
          return new F(function(){return _j7/* slcJ */(_j6/* slcI */, _j6/* slcI */);});
        }else{
          return new F(function(){return _j7/* slcJ */(_j5/* slcE */, _j5/* slcE */);});
        }
      }else{
        return new F(function(){return A2(_iU/* slcp */,_iZ/* slct */, function(_je/* sld8 */){
          return new F(function(){return A1(_j0/* slcu */,new T2(0,new T2(0,_av/* GHC.Types.False */,_j1/* slcv */),E(_je/* sld8 */).b));});
        });});
      }
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _iF/* slbZ */, _iX/* slde */));
  }),
  _jf/* sldo */ = function(_jg/* sldf */){
    var _jh/* sldg */ = new T(function(){
      return B(A1(_iI/* slc2 */,_jg/* sldf */));
    }),
    _ji/* sldn */ = function(_jj/* sldh */){
      return new F(function(){return A1(_jh/* sldg */,function(_jk/* sldi */){
        return new F(function(){return _ir/* Core.World.Internal.easeRegister1 */(_iS/* slcn */, _iT/* slco */, E(_jk/* sldi */).b, _jj/* sldh */);});
      });});
    };
    return E(_ji/* sldn */);
  };
  return E(_jf/* sldo */);
},
_jl/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _7/* GHC.Tuple.() */;
},
_jm/* $wa */ = function(_jn/* sFyy */, _jo/* sFyz */, _jp/* sFyA */, _jq/* sFyB */, _/* EXTERNAL */){
  var _jr/* sFyD */ = function(_/* EXTERNAL */, _js/* sFyF */){
    var _jt/* sFyG */ = function(_/* EXTERNAL */, _ju/* sFyI */){
      var _jv/* sFyJ */ = function(_/* EXTERNAL */, _jw/* sFyL */){
        var _jx/* sFyM */ = E(_jq/* sFyB */);
        switch(_jx/* sFyM */._){
          case 0:
            return new T(function(){
              var _jy/* sFyO */ = function(_jz/* sFyP */){
                var _jA/* sFyQ */ = _jz/* sFyP */*256,
                _jB/* sFyR */ = _jA/* sFyQ */&4294967295,
                _jC/* sFyS */ = function(_jD/* sFyT */){
                  var _jE/* sFyW */ = E(_ju/* sFyI */)*256,
                  _jF/* sFyX */ = _jE/* sFyW */&4294967295,
                  _jG/* sFyY */ = function(_jH/* sFyZ */){
                    var _jI/* sFz0 */ = function(_jJ/* sFz1 */){
                      var _jK/* sFz2 */ = _jJ/* sFz1 */*256,
                      _jL/* sFz3 */ = _jK/* sFz2 */&4294967295,
                      _jM/* sFz4 */ = function(_jN/* sFz5 */){
                        var _jO/* sFz6 */ = E(_jx/* sFyM */.a);
                        return (1>_jO/* sFz6 */) ? (0>_jO/* sFz6 */) ? new T4(1,_jD/* sFyT */,_jH/* sFyZ */,_jN/* sFz5 */,0) : new T4(1,_jD/* sFyT */,_jH/* sFyZ */,_jN/* sFz5 */,_jO/* sFz6 */) : new T4(1,_jD/* sFyT */,_jH/* sFyZ */,_jN/* sFz5 */,1);
                      };
                      if(_jK/* sFz2 */>=_jL/* sFz3 */){
                        if(255>_jL/* sFz3 */){
                          if(0>_jL/* sFz3 */){
                            return new F(function(){return _jM/* sFz4 */(0);});
                          }else{
                            return new F(function(){return _jM/* sFz4 */(_jL/* sFz3 */);});
                          }
                        }else{
                          return new F(function(){return _jM/* sFz4 */(255);});
                        }
                      }else{
                        var _jP/* sFzj */ = _jL/* sFz3 */-1|0;
                        if(255>_jP/* sFzj */){
                          if(0>_jP/* sFzj */){
                            return new F(function(){return _jM/* sFz4 */(0);});
                          }else{
                            return new F(function(){return _jM/* sFz4 */(_jP/* sFzj */);});
                          }
                        }else{
                          return new F(function(){return _jM/* sFz4 */(255);});
                        }
                      }
                    },
                    _jQ/* sFzo */ = E(_jw/* sFyL */);
                    if(!_jQ/* sFzo */._){
                      return new F(function(){return _jI/* sFz0 */(0);});
                    }else{
                      return new F(function(){return _jI/* sFz0 */(E(_jQ/* sFzo */.a));});
                    }
                  };
                  if(_jE/* sFyW */>=_jF/* sFyX */){
                    if(255>_jF/* sFyX */){
                      if(0>_jF/* sFyX */){
                        return new F(function(){return _jG/* sFyY */(0);});
                      }else{
                        return new F(function(){return _jG/* sFyY */(_jF/* sFyX */);});
                      }
                    }else{
                      return new F(function(){return _jG/* sFyY */(255);});
                    }
                  }else{
                    var _jR/* sFzz */ = _jF/* sFyX */-1|0;
                    if(255>_jR/* sFzz */){
                      if(0>_jR/* sFzz */){
                        return new F(function(){return _jG/* sFyY */(0);});
                      }else{
                        return new F(function(){return _jG/* sFyY */(_jR/* sFzz */);});
                      }
                    }else{
                      return new F(function(){return _jG/* sFyY */(255);});
                    }
                  }
                };
                if(_jA/* sFyQ */>=_jB/* sFyR */){
                  if(255>_jB/* sFyR */){
                    if(0>_jB/* sFyR */){
                      return new F(function(){return _jC/* sFyS */(0);});
                    }else{
                      return new F(function(){return _jC/* sFyS */(_jB/* sFyR */);});
                    }
                  }else{
                    return new F(function(){return _jC/* sFyS */(255);});
                  }
                }else{
                  var _jS/* sFzL */ = _jB/* sFyR */-1|0;
                  if(255>_jS/* sFzL */){
                    if(0>_jS/* sFzL */){
                      return new F(function(){return _jC/* sFyS */(0);});
                    }else{
                      return new F(function(){return _jC/* sFyS */(_jS/* sFzL */);});
                    }
                  }else{
                    return new F(function(){return _jC/* sFyS */(255);});
                  }
                }
              },
              _jT/* sFzQ */ = E(_js/* sFyF */);
              if(!_jT/* sFzQ */._){
                return B(_jy/* sFyO */(0));
              }else{
                return B(_jy/* sFyO */(E(_jT/* sFzQ */.a)));
              }
            });
          case 1:
            var _jU/* sFzW */ = B(A1(_jx/* sFyM */.a,_/* EXTERNAL */)),
            _jV/* sFzY */ = _jU/* sFzW */;
            return new T(function(){
              var _jW/* sFzZ */ = function(_jX/* sFA0 */){
                var _jY/* sFA1 */ = _jX/* sFA0 */*256,
                _jZ/* sFA2 */ = _jY/* sFA1 */&4294967295,
                _k0/* sFA3 */ = function(_k1/* sFA4 */){
                  var _k2/* sFA7 */ = E(_ju/* sFyI */)*256,
                  _k3/* sFA8 */ = _k2/* sFA7 */&4294967295,
                  _k4/* sFA9 */ = function(_k5/* sFAa */){
                    var _k6/* sFAb */ = function(_k7/* sFAc */){
                      var _k8/* sFAd */ = _k7/* sFAc */*256,
                      _k9/* sFAe */ = _k8/* sFAd */&4294967295,
                      _ka/* sFAf */ = function(_kb/* sFAg */){
                        var _kc/* sFAh */ = E(_jV/* sFzY */);
                        return (1>_kc/* sFAh */) ? (0>_kc/* sFAh */) ? new T4(1,_k1/* sFA4 */,_k5/* sFAa */,_kb/* sFAg */,0) : new T4(1,_k1/* sFA4 */,_k5/* sFAa */,_kb/* sFAg */,_kc/* sFAh */) : new T4(1,_k1/* sFA4 */,_k5/* sFAa */,_kb/* sFAg */,1);
                      };
                      if(_k8/* sFAd */>=_k9/* sFAe */){
                        if(255>_k9/* sFAe */){
                          if(0>_k9/* sFAe */){
                            return new F(function(){return _ka/* sFAf */(0);});
                          }else{
                            return new F(function(){return _ka/* sFAf */(_k9/* sFAe */);});
                          }
                        }else{
                          return new F(function(){return _ka/* sFAf */(255);});
                        }
                      }else{
                        var _kd/* sFAu */ = _k9/* sFAe */-1|0;
                        if(255>_kd/* sFAu */){
                          if(0>_kd/* sFAu */){
                            return new F(function(){return _ka/* sFAf */(0);});
                          }else{
                            return new F(function(){return _ka/* sFAf */(_kd/* sFAu */);});
                          }
                        }else{
                          return new F(function(){return _ka/* sFAf */(255);});
                        }
                      }
                    },
                    _ke/* sFAz */ = E(_jw/* sFyL */);
                    if(!_ke/* sFAz */._){
                      return new F(function(){return _k6/* sFAb */(0);});
                    }else{
                      return new F(function(){return _k6/* sFAb */(E(_ke/* sFAz */.a));});
                    }
                  };
                  if(_k2/* sFA7 */>=_k3/* sFA8 */){
                    if(255>_k3/* sFA8 */){
                      if(0>_k3/* sFA8 */){
                        return new F(function(){return _k4/* sFA9 */(0);});
                      }else{
                        return new F(function(){return _k4/* sFA9 */(_k3/* sFA8 */);});
                      }
                    }else{
                      return new F(function(){return _k4/* sFA9 */(255);});
                    }
                  }else{
                    var _kf/* sFAK */ = _k3/* sFA8 */-1|0;
                    if(255>_kf/* sFAK */){
                      if(0>_kf/* sFAK */){
                        return new F(function(){return _k4/* sFA9 */(0);});
                      }else{
                        return new F(function(){return _k4/* sFA9 */(_kf/* sFAK */);});
                      }
                    }else{
                      return new F(function(){return _k4/* sFA9 */(255);});
                    }
                  }
                };
                if(_jY/* sFA1 */>=_jZ/* sFA2 */){
                  if(255>_jZ/* sFA2 */){
                    if(0>_jZ/* sFA2 */){
                      return new F(function(){return _k0/* sFA3 */(0);});
                    }else{
                      return new F(function(){return _k0/* sFA3 */(_jZ/* sFA2 */);});
                    }
                  }else{
                    return new F(function(){return _k0/* sFA3 */(255);});
                  }
                }else{
                  var _kg/* sFAW */ = _jZ/* sFA2 */-1|0;
                  if(255>_kg/* sFAW */){
                    if(0>_kg/* sFAW */){
                      return new F(function(){return _k0/* sFA3 */(0);});
                    }else{
                      return new F(function(){return _k0/* sFA3 */(_kg/* sFAW */);});
                    }
                  }else{
                    return new F(function(){return _k0/* sFA3 */(255);});
                  }
                }
              },
              _kh/* sFB1 */ = E(_js/* sFyF */);
              if(!_kh/* sFB1 */._){
                return B(_jW/* sFzZ */(0));
              }else{
                return B(_jW/* sFzZ */(E(_kh/* sFB1 */.a)));
              }
            });
          case 2:
            var _ki/* sFBe */ = rMV/* EXTERNAL */(E(E(_jx/* sFyM */.a).c)),
            _kj/* sFBh */ = E(_ki/* sFBe */);
            return (_kj/* sFBh */._==0) ? new T(function(){
              var _kk/* sFBk */ = function(_kl/* sFBl */){
                var _km/* sFBm */ = _kl/* sFBl */*256,
                _kn/* sFBn */ = _km/* sFBm */&4294967295,
                _ko/* sFBo */ = function(_kp/* sFBp */){
                  var _kq/* sFBs */ = E(_ju/* sFyI */)*256,
                  _kr/* sFBt */ = _kq/* sFBs */&4294967295,
                  _ks/* sFBu */ = function(_kt/* sFBv */){
                    var _ku/* sFBw */ = function(_kv/* sFBx */){
                      var _kw/* sFBy */ = _kv/* sFBx */*256,
                      _kx/* sFBz */ = _kw/* sFBy */&4294967295,
                      _ky/* sFBA */ = function(_kz/* sFBB */){
                        var _kA/* sFBD */ = B(A1(_jx/* sFyM */.b,new T(function(){
                          return B(_fB/* Data.Tuple.fst */(_kj/* sFBh */.a));
                        })));
                        return (1>_kA/* sFBD */) ? (0>_kA/* sFBD */) ? new T4(1,_kp/* sFBp */,_kt/* sFBv */,_kz/* sFBB */,0) : new T4(1,_kp/* sFBp */,_kt/* sFBv */,_kz/* sFBB */,_kA/* sFBD */) : new T4(1,_kp/* sFBp */,_kt/* sFBv */,_kz/* sFBB */,1);
                      };
                      if(_kw/* sFBy */>=_kx/* sFBz */){
                        if(255>_kx/* sFBz */){
                          if(0>_kx/* sFBz */){
                            return new F(function(){return _ky/* sFBA */(0);});
                          }else{
                            return new F(function(){return _ky/* sFBA */(_kx/* sFBz */);});
                          }
                        }else{
                          return new F(function(){return _ky/* sFBA */(255);});
                        }
                      }else{
                        var _kB/* sFBQ */ = _kx/* sFBz */-1|0;
                        if(255>_kB/* sFBQ */){
                          if(0>_kB/* sFBQ */){
                            return new F(function(){return _ky/* sFBA */(0);});
                          }else{
                            return new F(function(){return _ky/* sFBA */(_kB/* sFBQ */);});
                          }
                        }else{
                          return new F(function(){return _ky/* sFBA */(255);});
                        }
                      }
                    },
                    _kC/* sFBV */ = E(_jw/* sFyL */);
                    if(!_kC/* sFBV */._){
                      return new F(function(){return _ku/* sFBw */(0);});
                    }else{
                      return new F(function(){return _ku/* sFBw */(E(_kC/* sFBV */.a));});
                    }
                  };
                  if(_kq/* sFBs */>=_kr/* sFBt */){
                    if(255>_kr/* sFBt */){
                      if(0>_kr/* sFBt */){
                        return new F(function(){return _ks/* sFBu */(0);});
                      }else{
                        return new F(function(){return _ks/* sFBu */(_kr/* sFBt */);});
                      }
                    }else{
                      return new F(function(){return _ks/* sFBu */(255);});
                    }
                  }else{
                    var _kD/* sFC6 */ = _kr/* sFBt */-1|0;
                    if(255>_kD/* sFC6 */){
                      if(0>_kD/* sFC6 */){
                        return new F(function(){return _ks/* sFBu */(0);});
                      }else{
                        return new F(function(){return _ks/* sFBu */(_kD/* sFC6 */);});
                      }
                    }else{
                      return new F(function(){return _ks/* sFBu */(255);});
                    }
                  }
                };
                if(_km/* sFBm */>=_kn/* sFBn */){
                  if(255>_kn/* sFBn */){
                    if(0>_kn/* sFBn */){
                      return new F(function(){return _ko/* sFBo */(0);});
                    }else{
                      return new F(function(){return _ko/* sFBo */(_kn/* sFBn */);});
                    }
                  }else{
                    return new F(function(){return _ko/* sFBo */(255);});
                  }
                }else{
                  var _kE/* sFCi */ = _kn/* sFBn */-1|0;
                  if(255>_kE/* sFCi */){
                    if(0>_kE/* sFCi */){
                      return new F(function(){return _ko/* sFBo */(0);});
                    }else{
                      return new F(function(){return _ko/* sFBo */(_kE/* sFCi */);});
                    }
                  }else{
                    return new F(function(){return _ko/* sFBo */(255);});
                  }
                }
              },
              _kF/* sFCn */ = E(_js/* sFyF */);
              if(!_kF/* sFCn */._){
                return B(_kk/* sFBk */(0));
              }else{
                return B(_kk/* sFBk */(E(_kF/* sFCn */.a)));
              }
            }) : new T(function(){
              var _kG/* sFCt */ = function(_kH/* sFCu */){
                var _kI/* sFCv */ = _kH/* sFCu */*256,
                _kJ/* sFCw */ = _kI/* sFCv */&4294967295,
                _kK/* sFCx */ = function(_kL/* sFCy */){
                  var _kM/* sFCB */ = E(_ju/* sFyI */)*256,
                  _kN/* sFCC */ = _kM/* sFCB */&4294967295,
                  _kO/* sFCD */ = function(_kP/* sFCE */){
                    var _kQ/* sFCF */ = function(_kR/* sFCG */){
                      var _kS/* sFCH */ = _kR/* sFCG */*256,
                      _kT/* sFCI */ = _kS/* sFCH */&4294967295;
                      if(_kS/* sFCH */>=_kT/* sFCI */){
                        return (255>_kT/* sFCI */) ? (0>_kT/* sFCI */) ? new T4(1,_kL/* sFCy */,_kP/* sFCE */,0,1) : new T4(1,_kL/* sFCy */,_kP/* sFCE */,_kT/* sFCI */,1) : new T4(1,_kL/* sFCy */,_kP/* sFCE */,255,1);
                      }else{
                        var _kU/* sFCQ */ = _kT/* sFCI */-1|0;
                        return (255>_kU/* sFCQ */) ? (0>_kU/* sFCQ */) ? new T4(1,_kL/* sFCy */,_kP/* sFCE */,0,1) : new T4(1,_kL/* sFCy */,_kP/* sFCE */,_kU/* sFCQ */,1) : new T4(1,_kL/* sFCy */,_kP/* sFCE */,255,1);
                      }
                    },
                    _kV/* sFCV */ = E(_jw/* sFyL */);
                    if(!_kV/* sFCV */._){
                      return new F(function(){return _kQ/* sFCF */(0);});
                    }else{
                      return new F(function(){return _kQ/* sFCF */(E(_kV/* sFCV */.a));});
                    }
                  };
                  if(_kM/* sFCB */>=_kN/* sFCC */){
                    if(255>_kN/* sFCC */){
                      if(0>_kN/* sFCC */){
                        return new F(function(){return _kO/* sFCD */(0);});
                      }else{
                        return new F(function(){return _kO/* sFCD */(_kN/* sFCC */);});
                      }
                    }else{
                      return new F(function(){return _kO/* sFCD */(255);});
                    }
                  }else{
                    var _kW/* sFD6 */ = _kN/* sFCC */-1|0;
                    if(255>_kW/* sFD6 */){
                      if(0>_kW/* sFD6 */){
                        return new F(function(){return _kO/* sFCD */(0);});
                      }else{
                        return new F(function(){return _kO/* sFCD */(_kW/* sFD6 */);});
                      }
                    }else{
                      return new F(function(){return _kO/* sFCD */(255);});
                    }
                  }
                };
                if(_kI/* sFCv */>=_kJ/* sFCw */){
                  if(255>_kJ/* sFCw */){
                    if(0>_kJ/* sFCw */){
                      return new F(function(){return _kK/* sFCx */(0);});
                    }else{
                      return new F(function(){return _kK/* sFCx */(_kJ/* sFCw */);});
                    }
                  }else{
                    return new F(function(){return _kK/* sFCx */(255);});
                  }
                }else{
                  var _kX/* sFDi */ = _kJ/* sFCw */-1|0;
                  if(255>_kX/* sFDi */){
                    if(0>_kX/* sFDi */){
                      return new F(function(){return _kK/* sFCx */(0);});
                    }else{
                      return new F(function(){return _kK/* sFCx */(_kX/* sFDi */);});
                    }
                  }else{
                    return new F(function(){return _kK/* sFCx */(255);});
                  }
                }
              },
              _kY/* sFDn */ = E(_js/* sFyF */);
              if(!_kY/* sFDn */._){
                return B(_kG/* sFCt */(0));
              }else{
                return B(_kG/* sFCt */(E(_kY/* sFDn */.a)));
              }
            });
          default:
            var _kZ/* sFDA */ = rMV/* EXTERNAL */(E(E(_jx/* sFyM */.a).c)),
            _l0/* sFDD */ = E(_kZ/* sFDA */);
            if(!_l0/* sFDD */._){
              var _l1/* sFDJ */ = B(A2(_jx/* sFyM */.b,E(_l0/* sFDD */.a).a, _/* EXTERNAL */)),
              _l2/* sFDL */ = _l1/* sFDJ */;
              return new T(function(){
                var _l3/* sFDM */ = function(_l4/* sFDN */){
                  var _l5/* sFDO */ = _l4/* sFDN */*256,
                  _l6/* sFDP */ = _l5/* sFDO */&4294967295,
                  _l7/* sFDQ */ = function(_l8/* sFDR */){
                    var _l9/* sFDU */ = E(_ju/* sFyI */)*256,
                    _la/* sFDV */ = _l9/* sFDU */&4294967295,
                    _lb/* sFDW */ = function(_lc/* sFDX */){
                      var _ld/* sFDY */ = function(_le/* sFDZ */){
                        var _lf/* sFE0 */ = _le/* sFDZ */*256,
                        _lg/* sFE1 */ = _lf/* sFE0 */&4294967295,
                        _lh/* sFE2 */ = function(_li/* sFE3 */){
                          var _lj/* sFE4 */ = E(_l2/* sFDL */);
                          return (1>_lj/* sFE4 */) ? (0>_lj/* sFE4 */) ? new T4(1,_l8/* sFDR */,_lc/* sFDX */,_li/* sFE3 */,0) : new T4(1,_l8/* sFDR */,_lc/* sFDX */,_li/* sFE3 */,_lj/* sFE4 */) : new T4(1,_l8/* sFDR */,_lc/* sFDX */,_li/* sFE3 */,1);
                        };
                        if(_lf/* sFE0 */>=_lg/* sFE1 */){
                          if(255>_lg/* sFE1 */){
                            if(0>_lg/* sFE1 */){
                              return new F(function(){return _lh/* sFE2 */(0);});
                            }else{
                              return new F(function(){return _lh/* sFE2 */(_lg/* sFE1 */);});
                            }
                          }else{
                            return new F(function(){return _lh/* sFE2 */(255);});
                          }
                        }else{
                          var _lk/* sFEh */ = _lg/* sFE1 */-1|0;
                          if(255>_lk/* sFEh */){
                            if(0>_lk/* sFEh */){
                              return new F(function(){return _lh/* sFE2 */(0);});
                            }else{
                              return new F(function(){return _lh/* sFE2 */(_lk/* sFEh */);});
                            }
                          }else{
                            return new F(function(){return _lh/* sFE2 */(255);});
                          }
                        }
                      },
                      _ll/* sFEm */ = E(_jw/* sFyL */);
                      if(!_ll/* sFEm */._){
                        return new F(function(){return _ld/* sFDY */(0);});
                      }else{
                        return new F(function(){return _ld/* sFDY */(E(_ll/* sFEm */.a));});
                      }
                    };
                    if(_l9/* sFDU */>=_la/* sFDV */){
                      if(255>_la/* sFDV */){
                        if(0>_la/* sFDV */){
                          return new F(function(){return _lb/* sFDW */(0);});
                        }else{
                          return new F(function(){return _lb/* sFDW */(_la/* sFDV */);});
                        }
                      }else{
                        return new F(function(){return _lb/* sFDW */(255);});
                      }
                    }else{
                      var _lm/* sFEx */ = _la/* sFDV */-1|0;
                      if(255>_lm/* sFEx */){
                        if(0>_lm/* sFEx */){
                          return new F(function(){return _lb/* sFDW */(0);});
                        }else{
                          return new F(function(){return _lb/* sFDW */(_lm/* sFEx */);});
                        }
                      }else{
                        return new F(function(){return _lb/* sFDW */(255);});
                      }
                    }
                  };
                  if(_l5/* sFDO */>=_l6/* sFDP */){
                    if(255>_l6/* sFDP */){
                      if(0>_l6/* sFDP */){
                        return new F(function(){return _l7/* sFDQ */(0);});
                      }else{
                        return new F(function(){return _l7/* sFDQ */(_l6/* sFDP */);});
                      }
                    }else{
                      return new F(function(){return _l7/* sFDQ */(255);});
                    }
                  }else{
                    var _ln/* sFEJ */ = _l6/* sFDP */-1|0;
                    if(255>_ln/* sFEJ */){
                      if(0>_ln/* sFEJ */){
                        return new F(function(){return _l7/* sFDQ */(0);});
                      }else{
                        return new F(function(){return _l7/* sFDQ */(_ln/* sFEJ */);});
                      }
                    }else{
                      return new F(function(){return _l7/* sFDQ */(255);});
                    }
                  }
                },
                _lo/* sFEO */ = E(_js/* sFyF */);
                if(!_lo/* sFEO */._){
                  return B(_l3/* sFDM */(0));
                }else{
                  return B(_l3/* sFDM */(E(_lo/* sFEO */.a)));
                }
              });
            }else{
              return new T(function(){
                var _lp/* sFEU */ = function(_lq/* sFEV */){
                  var _lr/* sFEW */ = _lq/* sFEV */*256,
                  _ls/* sFEX */ = _lr/* sFEW */&4294967295,
                  _lt/* sFEY */ = function(_lu/* sFEZ */){
                    var _lv/* sFF2 */ = E(_ju/* sFyI */)*256,
                    _lw/* sFF3 */ = _lv/* sFF2 */&4294967295,
                    _lx/* sFF4 */ = function(_ly/* sFF5 */){
                      var _lz/* sFF6 */ = function(_lA/* sFF7 */){
                        var _lB/* sFF8 */ = _lA/* sFF7 */*256,
                        _lC/* sFF9 */ = _lB/* sFF8 */&4294967295;
                        if(_lB/* sFF8 */>=_lC/* sFF9 */){
                          return (255>_lC/* sFF9 */) ? (0>_lC/* sFF9 */) ? new T4(1,_lu/* sFEZ */,_ly/* sFF5 */,0,1) : new T4(1,_lu/* sFEZ */,_ly/* sFF5 */,_lC/* sFF9 */,1) : new T4(1,_lu/* sFEZ */,_ly/* sFF5 */,255,1);
                        }else{
                          var _lD/* sFFh */ = _lC/* sFF9 */-1|0;
                          return (255>_lD/* sFFh */) ? (0>_lD/* sFFh */) ? new T4(1,_lu/* sFEZ */,_ly/* sFF5 */,0,1) : new T4(1,_lu/* sFEZ */,_ly/* sFF5 */,_lD/* sFFh */,1) : new T4(1,_lu/* sFEZ */,_ly/* sFF5 */,255,1);
                        }
                      },
                      _lE/* sFFm */ = E(_jw/* sFyL */);
                      if(!_lE/* sFFm */._){
                        return new F(function(){return _lz/* sFF6 */(0);});
                      }else{
                        return new F(function(){return _lz/* sFF6 */(E(_lE/* sFFm */.a));});
                      }
                    };
                    if(_lv/* sFF2 */>=_lw/* sFF3 */){
                      if(255>_lw/* sFF3 */){
                        if(0>_lw/* sFF3 */){
                          return new F(function(){return _lx/* sFF4 */(0);});
                        }else{
                          return new F(function(){return _lx/* sFF4 */(_lw/* sFF3 */);});
                        }
                      }else{
                        return new F(function(){return _lx/* sFF4 */(255);});
                      }
                    }else{
                      var _lF/* sFFx */ = _lw/* sFF3 */-1|0;
                      if(255>_lF/* sFFx */){
                        if(0>_lF/* sFFx */){
                          return new F(function(){return _lx/* sFF4 */(0);});
                        }else{
                          return new F(function(){return _lx/* sFF4 */(_lF/* sFFx */);});
                        }
                      }else{
                        return new F(function(){return _lx/* sFF4 */(255);});
                      }
                    }
                  };
                  if(_lr/* sFEW */>=_ls/* sFEX */){
                    if(255>_ls/* sFEX */){
                      if(0>_ls/* sFEX */){
                        return new F(function(){return _lt/* sFEY */(0);});
                      }else{
                        return new F(function(){return _lt/* sFEY */(_ls/* sFEX */);});
                      }
                    }else{
                      return new F(function(){return _lt/* sFEY */(255);});
                    }
                  }else{
                    var _lG/* sFFJ */ = _ls/* sFEX */-1|0;
                    if(255>_lG/* sFFJ */){
                      if(0>_lG/* sFFJ */){
                        return new F(function(){return _lt/* sFEY */(0);});
                      }else{
                        return new F(function(){return _lt/* sFEY */(_lG/* sFFJ */);});
                      }
                    }else{
                      return new F(function(){return _lt/* sFEY */(255);});
                    }
                  }
                },
                _lH/* sFFO */ = E(_js/* sFyF */);
                if(!_lH/* sFFO */._){
                  return B(_lp/* sFEU */(0));
                }else{
                  return B(_lp/* sFEU */(E(_lH/* sFFO */.a)));
                }
              });
            }
        }
      },
      _lI/* sFFT */ = E(_jp/* sFyA */);
      switch(_lI/* sFFT */._){
        case 0:
          return new F(function(){return _jv/* sFyJ */(_/* EXTERNAL */, new T1(1,_lI/* sFFT */.a));});
          break;
        case 1:
          var _lJ/* sFFX */ = B(A1(_lI/* sFFT */.a,_/* EXTERNAL */));
          return new F(function(){return _jv/* sFyJ */(_/* EXTERNAL */, new T1(1,_lJ/* sFFX */));});
          break;
        case 2:
          var _lK/* sFG9 */ = rMV/* EXTERNAL */(E(E(_lI/* sFFT */.a).c)),
          _lL/* sFGc */ = E(_lK/* sFG9 */);
          if(!_lL/* sFGc */._){
            var _lM/* sFGg */ = new T(function(){
              return B(A1(_lI/* sFFT */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_lL/* sFGc */.a));
              })));
            });
            return new F(function(){return _jv/* sFyJ */(_/* EXTERNAL */, new T1(1,_lM/* sFGg */));});
          }else{
            return new F(function(){return _jv/* sFyJ */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _lN/* sFGr */ = rMV/* EXTERNAL */(E(E(_lI/* sFFT */.a).c)),
          _lO/* sFGu */ = E(_lN/* sFGr */);
          if(!_lO/* sFGu */._){
            var _lP/* sFGA */ = B(A2(_lI/* sFFT */.b,E(_lO/* sFGu */.a).a, _/* EXTERNAL */));
            return new F(function(){return _jv/* sFyJ */(_/* EXTERNAL */, new T1(1,_lP/* sFGA */));});
          }else{
            return new F(function(){return _jv/* sFyJ */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _lQ/* sFGF */ = function(_/* EXTERNAL */){
      var _lR/* sFGH */ = function(_/* EXTERNAL */, _lS/* sFGJ */){
        var _lT/* sFGK */ = E(_jq/* sFyB */);
        switch(_lT/* sFGK */._){
          case 0:
            return new T(function(){
              var _lU/* sFGM */ = function(_lV/* sFGN */){
                var _lW/* sFGO */ = _lV/* sFGN */*256,
                _lX/* sFGP */ = _lW/* sFGO */&4294967295,
                _lY/* sFGQ */ = function(_lZ/* sFGR */){
                  var _m0/* sFGS */ = function(_m1/* sFGT */){
                    var _m2/* sFGU */ = _m1/* sFGT */*256,
                    _m3/* sFGV */ = _m2/* sFGU */&4294967295,
                    _m4/* sFGW */ = function(_m5/* sFGX */){
                      var _m6/* sFGY */ = E(_lT/* sFGK */.a);
                      return (1>_m6/* sFGY */) ? (0>_m6/* sFGY */) ? new T4(1,_lZ/* sFGR */,0,_m5/* sFGX */,0) : new T4(1,_lZ/* sFGR */,0,_m5/* sFGX */,_m6/* sFGY */) : new T4(1,_lZ/* sFGR */,0,_m5/* sFGX */,1);
                    };
                    if(_m2/* sFGU */>=_m3/* sFGV */){
                      if(255>_m3/* sFGV */){
                        if(0>_m3/* sFGV */){
                          return new F(function(){return _m4/* sFGW */(0);});
                        }else{
                          return new F(function(){return _m4/* sFGW */(_m3/* sFGV */);});
                        }
                      }else{
                        return new F(function(){return _m4/* sFGW */(255);});
                      }
                    }else{
                      var _m7/* sFHb */ = _m3/* sFGV */-1|0;
                      if(255>_m7/* sFHb */){
                        if(0>_m7/* sFHb */){
                          return new F(function(){return _m4/* sFGW */(0);});
                        }else{
                          return new F(function(){return _m4/* sFGW */(_m7/* sFHb */);});
                        }
                      }else{
                        return new F(function(){return _m4/* sFGW */(255);});
                      }
                    }
                  },
                  _m8/* sFHg */ = E(_lS/* sFGJ */);
                  if(!_m8/* sFHg */._){
                    return new F(function(){return _m0/* sFGS */(0);});
                  }else{
                    return new F(function(){return _m0/* sFGS */(E(_m8/* sFHg */.a));});
                  }
                };
                if(_lW/* sFGO */>=_lX/* sFGP */){
                  if(255>_lX/* sFGP */){
                    if(0>_lX/* sFGP */){
                      return new F(function(){return _lY/* sFGQ */(0);});
                    }else{
                      return new F(function(){return _lY/* sFGQ */(_lX/* sFGP */);});
                    }
                  }else{
                    return new F(function(){return _lY/* sFGQ */(255);});
                  }
                }else{
                  var _m9/* sFHr */ = _lX/* sFGP */-1|0;
                  if(255>_m9/* sFHr */){
                    if(0>_m9/* sFHr */){
                      return new F(function(){return _lY/* sFGQ */(0);});
                    }else{
                      return new F(function(){return _lY/* sFGQ */(_m9/* sFHr */);});
                    }
                  }else{
                    return new F(function(){return _lY/* sFGQ */(255);});
                  }
                }
              },
              _ma/* sFHw */ = E(_js/* sFyF */);
              if(!_ma/* sFHw */._){
                return B(_lU/* sFGM */(0));
              }else{
                return B(_lU/* sFGM */(E(_ma/* sFHw */.a)));
              }
            });
          case 1:
            var _mb/* sFHC */ = B(A1(_lT/* sFGK */.a,_/* EXTERNAL */)),
            _mc/* sFHE */ = _mb/* sFHC */;
            return new T(function(){
              var _md/* sFHF */ = function(_me/* sFHG */){
                var _mf/* sFHH */ = _me/* sFHG */*256,
                _mg/* sFHI */ = _mf/* sFHH */&4294967295,
                _mh/* sFHJ */ = function(_mi/* sFHK */){
                  var _mj/* sFHL */ = function(_mk/* sFHM */){
                    var _ml/* sFHN */ = _mk/* sFHM */*256,
                    _mm/* sFHO */ = _ml/* sFHN */&4294967295,
                    _mn/* sFHP */ = function(_mo/* sFHQ */){
                      var _mp/* sFHR */ = E(_mc/* sFHE */);
                      return (1>_mp/* sFHR */) ? (0>_mp/* sFHR */) ? new T4(1,_mi/* sFHK */,0,_mo/* sFHQ */,0) : new T4(1,_mi/* sFHK */,0,_mo/* sFHQ */,_mp/* sFHR */) : new T4(1,_mi/* sFHK */,0,_mo/* sFHQ */,1);
                    };
                    if(_ml/* sFHN */>=_mm/* sFHO */){
                      if(255>_mm/* sFHO */){
                        if(0>_mm/* sFHO */){
                          return new F(function(){return _mn/* sFHP */(0);});
                        }else{
                          return new F(function(){return _mn/* sFHP */(_mm/* sFHO */);});
                        }
                      }else{
                        return new F(function(){return _mn/* sFHP */(255);});
                      }
                    }else{
                      var _mq/* sFI4 */ = _mm/* sFHO */-1|0;
                      if(255>_mq/* sFI4 */){
                        if(0>_mq/* sFI4 */){
                          return new F(function(){return _mn/* sFHP */(0);});
                        }else{
                          return new F(function(){return _mn/* sFHP */(_mq/* sFI4 */);});
                        }
                      }else{
                        return new F(function(){return _mn/* sFHP */(255);});
                      }
                    }
                  },
                  _mr/* sFI9 */ = E(_lS/* sFGJ */);
                  if(!_mr/* sFI9 */._){
                    return new F(function(){return _mj/* sFHL */(0);});
                  }else{
                    return new F(function(){return _mj/* sFHL */(E(_mr/* sFI9 */.a));});
                  }
                };
                if(_mf/* sFHH */>=_mg/* sFHI */){
                  if(255>_mg/* sFHI */){
                    if(0>_mg/* sFHI */){
                      return new F(function(){return _mh/* sFHJ */(0);});
                    }else{
                      return new F(function(){return _mh/* sFHJ */(_mg/* sFHI */);});
                    }
                  }else{
                    return new F(function(){return _mh/* sFHJ */(255);});
                  }
                }else{
                  var _ms/* sFIk */ = _mg/* sFHI */-1|0;
                  if(255>_ms/* sFIk */){
                    if(0>_ms/* sFIk */){
                      return new F(function(){return _mh/* sFHJ */(0);});
                    }else{
                      return new F(function(){return _mh/* sFHJ */(_ms/* sFIk */);});
                    }
                  }else{
                    return new F(function(){return _mh/* sFHJ */(255);});
                  }
                }
              },
              _mt/* sFIp */ = E(_js/* sFyF */);
              if(!_mt/* sFIp */._){
                return B(_md/* sFHF */(0));
              }else{
                return B(_md/* sFHF */(E(_mt/* sFIp */.a)));
              }
            });
          case 2:
            var _mu/* sFIC */ = rMV/* EXTERNAL */(E(E(_lT/* sFGK */.a).c)),
            _mv/* sFIF */ = E(_mu/* sFIC */);
            return (_mv/* sFIF */._==0) ? new T(function(){
              var _mw/* sFII */ = function(_mx/* sFIJ */){
                var _my/* sFIK */ = _mx/* sFIJ */*256,
                _mz/* sFIL */ = _my/* sFIK */&4294967295,
                _mA/* sFIM */ = function(_mB/* sFIN */){
                  var _mC/* sFIO */ = function(_mD/* sFIP */){
                    var _mE/* sFIQ */ = _mD/* sFIP */*256,
                    _mF/* sFIR */ = _mE/* sFIQ */&4294967295,
                    _mG/* sFIS */ = function(_mH/* sFIT */){
                      var _mI/* sFIV */ = B(A1(_lT/* sFGK */.b,new T(function(){
                        return B(_fB/* Data.Tuple.fst */(_mv/* sFIF */.a));
                      })));
                      return (1>_mI/* sFIV */) ? (0>_mI/* sFIV */) ? new T4(1,_mB/* sFIN */,0,_mH/* sFIT */,0) : new T4(1,_mB/* sFIN */,0,_mH/* sFIT */,_mI/* sFIV */) : new T4(1,_mB/* sFIN */,0,_mH/* sFIT */,1);
                    };
                    if(_mE/* sFIQ */>=_mF/* sFIR */){
                      if(255>_mF/* sFIR */){
                        if(0>_mF/* sFIR */){
                          return new F(function(){return _mG/* sFIS */(0);});
                        }else{
                          return new F(function(){return _mG/* sFIS */(_mF/* sFIR */);});
                        }
                      }else{
                        return new F(function(){return _mG/* sFIS */(255);});
                      }
                    }else{
                      var _mJ/* sFJ8 */ = _mF/* sFIR */-1|0;
                      if(255>_mJ/* sFJ8 */){
                        if(0>_mJ/* sFJ8 */){
                          return new F(function(){return _mG/* sFIS */(0);});
                        }else{
                          return new F(function(){return _mG/* sFIS */(_mJ/* sFJ8 */);});
                        }
                      }else{
                        return new F(function(){return _mG/* sFIS */(255);});
                      }
                    }
                  },
                  _mK/* sFJd */ = E(_lS/* sFGJ */);
                  if(!_mK/* sFJd */._){
                    return new F(function(){return _mC/* sFIO */(0);});
                  }else{
                    return new F(function(){return _mC/* sFIO */(E(_mK/* sFJd */.a));});
                  }
                };
                if(_my/* sFIK */>=_mz/* sFIL */){
                  if(255>_mz/* sFIL */){
                    if(0>_mz/* sFIL */){
                      return new F(function(){return _mA/* sFIM */(0);});
                    }else{
                      return new F(function(){return _mA/* sFIM */(_mz/* sFIL */);});
                    }
                  }else{
                    return new F(function(){return _mA/* sFIM */(255);});
                  }
                }else{
                  var _mL/* sFJo */ = _mz/* sFIL */-1|0;
                  if(255>_mL/* sFJo */){
                    if(0>_mL/* sFJo */){
                      return new F(function(){return _mA/* sFIM */(0);});
                    }else{
                      return new F(function(){return _mA/* sFIM */(_mL/* sFJo */);});
                    }
                  }else{
                    return new F(function(){return _mA/* sFIM */(255);});
                  }
                }
              },
              _mM/* sFJt */ = E(_js/* sFyF */);
              if(!_mM/* sFJt */._){
                return B(_mw/* sFII */(0));
              }else{
                return B(_mw/* sFII */(E(_mM/* sFJt */.a)));
              }
            }) : new T(function(){
              var _mN/* sFJz */ = function(_mO/* sFJA */){
                var _mP/* sFJB */ = _mO/* sFJA */*256,
                _mQ/* sFJC */ = _mP/* sFJB */&4294967295,
                _mR/* sFJD */ = function(_mS/* sFJE */){
                  var _mT/* sFJF */ = function(_mU/* sFJG */){
                    var _mV/* sFJH */ = _mU/* sFJG */*256,
                    _mW/* sFJI */ = _mV/* sFJH */&4294967295;
                    if(_mV/* sFJH */>=_mW/* sFJI */){
                      return (255>_mW/* sFJI */) ? (0>_mW/* sFJI */) ? new T4(1,_mS/* sFJE */,0,0,1) : new T4(1,_mS/* sFJE */,0,_mW/* sFJI */,1) : new T4(1,_mS/* sFJE */,0,255,1);
                    }else{
                      var _mX/* sFJQ */ = _mW/* sFJI */-1|0;
                      return (255>_mX/* sFJQ */) ? (0>_mX/* sFJQ */) ? new T4(1,_mS/* sFJE */,0,0,1) : new T4(1,_mS/* sFJE */,0,_mX/* sFJQ */,1) : new T4(1,_mS/* sFJE */,0,255,1);
                    }
                  },
                  _mY/* sFJV */ = E(_lS/* sFGJ */);
                  if(!_mY/* sFJV */._){
                    return new F(function(){return _mT/* sFJF */(0);});
                  }else{
                    return new F(function(){return _mT/* sFJF */(E(_mY/* sFJV */.a));});
                  }
                };
                if(_mP/* sFJB */>=_mQ/* sFJC */){
                  if(255>_mQ/* sFJC */){
                    if(0>_mQ/* sFJC */){
                      return new F(function(){return _mR/* sFJD */(0);});
                    }else{
                      return new F(function(){return _mR/* sFJD */(_mQ/* sFJC */);});
                    }
                  }else{
                    return new F(function(){return _mR/* sFJD */(255);});
                  }
                }else{
                  var _mZ/* sFK6 */ = _mQ/* sFJC */-1|0;
                  if(255>_mZ/* sFK6 */){
                    if(0>_mZ/* sFK6 */){
                      return new F(function(){return _mR/* sFJD */(0);});
                    }else{
                      return new F(function(){return _mR/* sFJD */(_mZ/* sFK6 */);});
                    }
                  }else{
                    return new F(function(){return _mR/* sFJD */(255);});
                  }
                }
              },
              _n0/* sFKb */ = E(_js/* sFyF */);
              if(!_n0/* sFKb */._){
                return B(_mN/* sFJz */(0));
              }else{
                return B(_mN/* sFJz */(E(_n0/* sFKb */.a)));
              }
            });
          default:
            var _n1/* sFKo */ = rMV/* EXTERNAL */(E(E(_lT/* sFGK */.a).c)),
            _n2/* sFKr */ = E(_n1/* sFKo */);
            if(!_n2/* sFKr */._){
              var _n3/* sFKx */ = B(A2(_lT/* sFGK */.b,E(_n2/* sFKr */.a).a, _/* EXTERNAL */)),
              _n4/* sFKz */ = _n3/* sFKx */;
              return new T(function(){
                var _n5/* sFKA */ = function(_n6/* sFKB */){
                  var _n7/* sFKC */ = _n6/* sFKB */*256,
                  _n8/* sFKD */ = _n7/* sFKC */&4294967295,
                  _n9/* sFKE */ = function(_na/* sFKF */){
                    var _nb/* sFKG */ = function(_nc/* sFKH */){
                      var _nd/* sFKI */ = _nc/* sFKH */*256,
                      _ne/* sFKJ */ = _nd/* sFKI */&4294967295,
                      _nf/* sFKK */ = function(_ng/* sFKL */){
                        var _nh/* sFKM */ = E(_n4/* sFKz */);
                        return (1>_nh/* sFKM */) ? (0>_nh/* sFKM */) ? new T4(1,_na/* sFKF */,0,_ng/* sFKL */,0) : new T4(1,_na/* sFKF */,0,_ng/* sFKL */,_nh/* sFKM */) : new T4(1,_na/* sFKF */,0,_ng/* sFKL */,1);
                      };
                      if(_nd/* sFKI */>=_ne/* sFKJ */){
                        if(255>_ne/* sFKJ */){
                          if(0>_ne/* sFKJ */){
                            return new F(function(){return _nf/* sFKK */(0);});
                          }else{
                            return new F(function(){return _nf/* sFKK */(_ne/* sFKJ */);});
                          }
                        }else{
                          return new F(function(){return _nf/* sFKK */(255);});
                        }
                      }else{
                        var _ni/* sFKZ */ = _ne/* sFKJ */-1|0;
                        if(255>_ni/* sFKZ */){
                          if(0>_ni/* sFKZ */){
                            return new F(function(){return _nf/* sFKK */(0);});
                          }else{
                            return new F(function(){return _nf/* sFKK */(_ni/* sFKZ */);});
                          }
                        }else{
                          return new F(function(){return _nf/* sFKK */(255);});
                        }
                      }
                    },
                    _nj/* sFL4 */ = E(_lS/* sFGJ */);
                    if(!_nj/* sFL4 */._){
                      return new F(function(){return _nb/* sFKG */(0);});
                    }else{
                      return new F(function(){return _nb/* sFKG */(E(_nj/* sFL4 */.a));});
                    }
                  };
                  if(_n7/* sFKC */>=_n8/* sFKD */){
                    if(255>_n8/* sFKD */){
                      if(0>_n8/* sFKD */){
                        return new F(function(){return _n9/* sFKE */(0);});
                      }else{
                        return new F(function(){return _n9/* sFKE */(_n8/* sFKD */);});
                      }
                    }else{
                      return new F(function(){return _n9/* sFKE */(255);});
                    }
                  }else{
                    var _nk/* sFLf */ = _n8/* sFKD */-1|0;
                    if(255>_nk/* sFLf */){
                      if(0>_nk/* sFLf */){
                        return new F(function(){return _n9/* sFKE */(0);});
                      }else{
                        return new F(function(){return _n9/* sFKE */(_nk/* sFLf */);});
                      }
                    }else{
                      return new F(function(){return _n9/* sFKE */(255);});
                    }
                  }
                },
                _nl/* sFLk */ = E(_js/* sFyF */);
                if(!_nl/* sFLk */._){
                  return B(_n5/* sFKA */(0));
                }else{
                  return B(_n5/* sFKA */(E(_nl/* sFLk */.a)));
                }
              });
            }else{
              return new T(function(){
                var _nm/* sFLq */ = function(_nn/* sFLr */){
                  var _no/* sFLs */ = _nn/* sFLr */*256,
                  _np/* sFLt */ = _no/* sFLs */&4294967295,
                  _nq/* sFLu */ = function(_nr/* sFLv */){
                    var _ns/* sFLw */ = function(_nt/* sFLx */){
                      var _nu/* sFLy */ = _nt/* sFLx */*256,
                      _nv/* sFLz */ = _nu/* sFLy */&4294967295;
                      if(_nu/* sFLy */>=_nv/* sFLz */){
                        return (255>_nv/* sFLz */) ? (0>_nv/* sFLz */) ? new T4(1,_nr/* sFLv */,0,0,1) : new T4(1,_nr/* sFLv */,0,_nv/* sFLz */,1) : new T4(1,_nr/* sFLv */,0,255,1);
                      }else{
                        var _nw/* sFLH */ = _nv/* sFLz */-1|0;
                        return (255>_nw/* sFLH */) ? (0>_nw/* sFLH */) ? new T4(1,_nr/* sFLv */,0,0,1) : new T4(1,_nr/* sFLv */,0,_nw/* sFLH */,1) : new T4(1,_nr/* sFLv */,0,255,1);
                      }
                    },
                    _nx/* sFLM */ = E(_lS/* sFGJ */);
                    if(!_nx/* sFLM */._){
                      return new F(function(){return _ns/* sFLw */(0);});
                    }else{
                      return new F(function(){return _ns/* sFLw */(E(_nx/* sFLM */.a));});
                    }
                  };
                  if(_no/* sFLs */>=_np/* sFLt */){
                    if(255>_np/* sFLt */){
                      if(0>_np/* sFLt */){
                        return new F(function(){return _nq/* sFLu */(0);});
                      }else{
                        return new F(function(){return _nq/* sFLu */(_np/* sFLt */);});
                      }
                    }else{
                      return new F(function(){return _nq/* sFLu */(255);});
                    }
                  }else{
                    var _ny/* sFLX */ = _np/* sFLt */-1|0;
                    if(255>_ny/* sFLX */){
                      if(0>_ny/* sFLX */){
                        return new F(function(){return _nq/* sFLu */(0);});
                      }else{
                        return new F(function(){return _nq/* sFLu */(_ny/* sFLX */);});
                      }
                    }else{
                      return new F(function(){return _nq/* sFLu */(255);});
                    }
                  }
                },
                _nz/* sFM2 */ = E(_js/* sFyF */);
                if(!_nz/* sFM2 */._){
                  return B(_nm/* sFLq */(0));
                }else{
                  return B(_nm/* sFLq */(E(_nz/* sFM2 */.a)));
                }
              });
            }
        }
      },
      _nA/* sFM7 */ = E(_jp/* sFyA */);
      switch(_nA/* sFM7 */._){
        case 0:
          return new F(function(){return _lR/* sFGH */(_/* EXTERNAL */, new T1(1,_nA/* sFM7 */.a));});
          break;
        case 1:
          var _nB/* sFMb */ = B(A1(_nA/* sFM7 */.a,_/* EXTERNAL */));
          return new F(function(){return _lR/* sFGH */(_/* EXTERNAL */, new T1(1,_nB/* sFMb */));});
          break;
        case 2:
          var _nC/* sFMn */ = rMV/* EXTERNAL */(E(E(_nA/* sFM7 */.a).c)),
          _nD/* sFMq */ = E(_nC/* sFMn */);
          if(!_nD/* sFMq */._){
            var _nE/* sFMu */ = new T(function(){
              return B(A1(_nA/* sFM7 */.b,new T(function(){
                return B(_fB/* Data.Tuple.fst */(_nD/* sFMq */.a));
              })));
            });
            return new F(function(){return _lR/* sFGH */(_/* EXTERNAL */, new T1(1,_nE/* sFMu */));});
          }else{
            return new F(function(){return _lR/* sFGH */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
          break;
        default:
          var _nF/* sFMF */ = rMV/* EXTERNAL */(E(E(_nA/* sFM7 */.a).c)),
          _nG/* sFMI */ = E(_nF/* sFMF */);
          if(!_nG/* sFMI */._){
            var _nH/* sFMO */ = B(A2(_nA/* sFM7 */.b,E(_nG/* sFMI */.a).a, _/* EXTERNAL */));
            return new F(function(){return _lR/* sFGH */(_/* EXTERNAL */, new T1(1,_nH/* sFMO */));});
          }else{
            return new F(function(){return _lR/* sFGH */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
          }
      }
    },
    _nI/* sFMT */ = E(_jo/* sFyz */);
    switch(_nI/* sFMT */._){
      case 0:
        return new F(function(){return _jt/* sFyG */(_/* EXTERNAL */, _nI/* sFMT */.a);});
        break;
      case 1:
        var _nJ/* sFMW */ = B(A1(_nI/* sFMT */.a,_/* EXTERNAL */));
        return new F(function(){return _jt/* sFyG */(_/* EXTERNAL */, _nJ/* sFMW */);});
        break;
      case 2:
        var _nK/* sFN7 */ = rMV/* EXTERNAL */(E(E(_nI/* sFMT */.a).c)),
        _nL/* sFNa */ = E(_nK/* sFN7 */);
        if(!_nL/* sFNa */._){
          var _nM/* sFNh */ = new T(function(){
            return B(A1(_nI/* sFMT */.b,new T(function(){
              return E(E(_nL/* sFNa */.a).a);
            })));
          });
          return new F(function(){return _jt/* sFyG */(_/* EXTERNAL */, _nM/* sFNh */);});
        }else{
          return new F(function(){return _lQ/* sFGF */(_/* EXTERNAL */);});
        }
        break;
      default:
        var _nN/* sFNr */ = rMV/* EXTERNAL */(E(E(_nI/* sFMT */.a).c)),
        _nO/* sFNu */ = E(_nN/* sFNr */);
        if(!_nO/* sFNu */._){
          var _nP/* sFNA */ = B(A2(_nI/* sFMT */.b,E(_nO/* sFNu */.a).a, _/* EXTERNAL */));
          return new F(function(){return _jt/* sFyG */(_/* EXTERNAL */, _nP/* sFNA */);});
        }else{
          return new F(function(){return _lQ/* sFGF */(_/* EXTERNAL */);});
        }
    }
  },
  _nQ/* sFNE */ = E(_jn/* sFyy */);
  switch(_nQ/* sFNE */._){
    case 0:
      return new F(function(){return _jr/* sFyD */(_/* EXTERNAL */, new T1(1,_nQ/* sFNE */.a));});
      break;
    case 1:
      var _nR/* sFNI */ = B(A1(_nQ/* sFNE */.a,_/* EXTERNAL */));
      return new F(function(){return _jr/* sFyD */(_/* EXTERNAL */, new T1(1,_nR/* sFNI */));});
      break;
    case 2:
      var _nS/* sFNU */ = rMV/* EXTERNAL */(E(E(_nQ/* sFNE */.a).c)),
      _nT/* sFNX */ = E(_nS/* sFNU */);
      if(!_nT/* sFNX */._){
        var _nU/* sFO1 */ = new T(function(){
          return B(A1(_nQ/* sFNE */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_nT/* sFNX */.a));
          })));
        });
        return new F(function(){return _jr/* sFyD */(_/* EXTERNAL */, new T1(1,_nU/* sFO1 */));});
      }else{
        return new F(function(){return _jr/* sFyD */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
      }
      break;
    default:
      var _nV/* sFOc */ = rMV/* EXTERNAL */(E(E(_nQ/* sFNE */.a).c)),
      _nW/* sFOf */ = E(_nV/* sFOc */);
      if(!_nW/* sFOf */._){
        var _nX/* sFOl */ = B(A2(_nQ/* sFNE */.b,E(_nW/* sFOf */.a).a, _/* EXTERNAL */));
        return new F(function(){return _jr/* sFyD */(_/* EXTERNAL */, new T1(1,_nX/* sFOl */));});
      }else{
        return new F(function(){return _jr/* sFyD */(_/* EXTERNAL */, _2o/* GHC.Base.Nothing */);});
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
_o4/* $wcolor2JSString */ = function(_o5/* sFk6 */){
  var _o6/* sFk7 */ = E(_o5/* sFk6 */);
  if(!_o6/* sFk7 */._){
    var _o7/* sFkG */ = jsCat/* EXTERNAL */(new T2(1,_nZ/* Core.Render.Internal.lvl2 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sFk7 */.a);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sFk7 */.b);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sFk7 */.c);
    }),_o3/* Core.Render.Internal.lvl6 */)))))), E(_nY/* Core.Render.Internal.lvl1 */));
    return E(_o7/* sFkG */);
  }else{
    var _o8/* sFlp */ = jsCat/* EXTERNAL */(new T2(1,_o1/* Core.Render.Internal.lvl5 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sFk7 */.a);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sFk7 */.b);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sFk7 */.c);
    }),new T2(1,_o0/* Core.Render.Internal.lvl3 */,new T2(1,new T(function(){
      return String/* EXTERNAL */(_o6/* sFk7 */.d);
    }),_o3/* Core.Render.Internal.lvl6 */)))))))), E(_nY/* Core.Render.Internal.lvl1 */));
    return E(_o8/* sFlp */);
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
_pi/* clip5 */ = function(_pj/* sFxI */, _/* EXTERNAL */){
  var _pk/* sFxP */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), E(_pj/* sFxI */));
  return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_pl/* clip4 */ = new T2(0,_pi/* Core.Render.Internal.clip5 */,_7/* GHC.Tuple.() */),
_pm/* clip3 */ = new T(function(){
  return B(_pg/* Control.Monad.Skeleton.bone */(_pl/* Core.Render.Internal.clip4 */));
}),
_pn/* clip2 */ = function(_po/* sFxS */){
  return E(_pm/* Core.Render.Internal.clip3 */);
},
_pp/* clip1 */ = new T1(1,_pn/* Core.Render.Internal.clip2 */),
_pq/* clip_f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.beginPath();})");
}),
_pr/* clip_f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.save();})");
}),
_ps/* getImage2 */ = function(_pt/* sFgp */, _pu/* sFgq */, _/* EXTERNAL */){
  var _pv/* sFgs */ = E(_pt/* sFgp */);
  switch(_pv/* sFgs */._){
    case 0:
      return new F(function(){return A2(_pu/* sFgq */,_pv/* sFgs */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _pw/* sFgv */ = B(A1(_pv/* sFgs */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_pu/* sFgq */,_pw/* sFgv */, _/* EXTERNAL */);});
      break;
    case 2:
      var _px/* sFgG */ = rMV/* EXTERNAL */(E(E(_pv/* sFgs */.a).c)),
      _py/* sFgJ */ = E(_px/* sFgG */);
      if(!_py/* sFgJ */._){
        var _pz/* sFgN */ = new T(function(){
          return B(A1(_pv/* sFgs */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_py/* sFgJ */.a));
          })));
        });
        return new F(function(){return A2(_pu/* sFgq */,_pz/* sFgN */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _pA/* sFgX */ = rMV/* EXTERNAL */(E(E(_pv/* sFgs */.a).c)),
      _pB/* sFh0 */ = E(_pA/* sFgX */);
      if(!_pB/* sFh0 */._){
        var _pC/* sFh6 */ = B(A2(_pv/* sFgs */.b,E(_pB/* sFh0 */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_pu/* sFgq */,_pC/* sFh6 */, _/* EXTERNAL */);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
  }
},
_pD/* lvl10 */ = "shadowBlur",
_pE/* lvl7 */ = "shadowColor",
_pF/* lvl8 */ = "shadowOffsetX",
_pG/* lvl9 */ = "shadowOffsetY",
_pH/* $wshadowed */ = function(_pI/* sFQ7 */, _pJ/* sFQ8 */, _pK/* sFQ9 */, _pL/* sFQa */, _pM/* sFQb */){
  var _pN/* sFRs */ = function(_pO/* sFQc */, _/* EXTERNAL */){
    var _pP/* sFRr */ = function(_pQ/* sFQe */, _/* EXTERNAL */){
      var _pR/* sFRq */ = function(_pS/* sFQg */, _/* EXTERNAL */){
        return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_pK/* sFQ9 */, function(_pT/* sFQi */, _/* EXTERNAL */){
          var _pU/* sFQk */ = E(_pL/* sFQa */),
          _pV/* sFQp */ = B(_jm/* Core.Render.Internal.$wa */(_pU/* sFQk */.a, _pU/* sFQk */.b, _pU/* sFQk */.c, _pU/* sFQk */.d, _/* EXTERNAL */)),
          _pW/* sFQs */ = E(_pO/* sFQc */),
          _pX/* sFQx */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _pW/* sFQs */),
          _pY/* sFQD */ = E(_ic/* Haste.DOM.Core.jsSet_f1 */),
          _pZ/* sFQG */ = __app3/* EXTERNAL */(_pY/* sFQD */, _pW/* sFQs */, E(_pE/* Core.Render.Internal.lvl7 */), B(_o4/* Core.Render.Internal.$wcolor2JSString */(_pV/* sFQp */))),
          _q0/* sFQO */ = String/* EXTERNAL */(E(_pQ/* sFQe */)),
          _q1/* sFQS */ = __app3/* EXTERNAL */(_pY/* sFQD */, _pW/* sFQs */, E(_pF/* Core.Render.Internal.lvl8 */), _q0/* sFQO */),
          _q2/* sFR0 */ = String/* EXTERNAL */(E(_pS/* sFQg */)),
          _q3/* sFR4 */ = __app3/* EXTERNAL */(_pY/* sFQD */, _pW/* sFQs */, E(_pG/* Core.Render.Internal.lvl9 */), _q2/* sFR0 */),
          _q4/* sFRc */ = String/* EXTERNAL */(E(_pT/* sFQi */)),
          _q5/* sFRg */ = __app3/* EXTERNAL */(_pY/* sFQD */, _pW/* sFQs */, E(_pD/* Core.Render.Internal.lvl10 */), _q4/* sFRc */),
          _q6/* sFRm */ = __app1/* EXTERNAL */(E(_pq/* Core.Render.Internal.clip_f3 */), _pW/* sFQs */);
          return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _/* EXTERNAL */);});
      };
      return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_pJ/* sFQ8 */, _pR/* sFRq */, _/* EXTERNAL */);});
    };
    return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_pI/* sFQ7 */, _pP/* sFRr */, _/* EXTERNAL */);});
  },
  _q7/* sFRu */ = B(_pg/* Control.Monad.Skeleton.bone */(new T2(0,_pN/* sFRs */,_7/* GHC.Tuple.() */)));
  return new T2(0,E(_q7/* sFRu */.a),E(new T2(2,new T2(2,_q7/* sFRu */.b,new T1(1,function(_q8/* sFRx */){
    return E(_pM/* sFQb */);
  })),_pp/* Core.Render.Internal.clip1 */)));
},
_q9/* $fAffineShape2 */ = function(_qa/* stet */, _qb/* steu */, _qc/* stev */, _qd/* stew */, _/* EXTERNAL */){
  var _qe/* stey */ = E(_qa/* stet */);
  switch(_qe/* stey */._){
    case 0:
      return new F(function(){return A(_qb/* steu */,[_qe/* stey */.a, _qc/* stev */, _qd/* stew */, _/* EXTERNAL */]);});
      break;
    case 1:
      var _qf/* steB */ = B(A1(_qe/* stey */.a,_/* EXTERNAL */));
      return new F(function(){return A(_qb/* steu */,[_qf/* steB */, _qc/* stev */, _qd/* stew */, _/* EXTERNAL */]);});
      break;
    case 2:
      var _qg/* steM */ = rMV/* EXTERNAL */(E(E(_qe/* stey */.a).c)),
      _qh/* steP */ = E(_qg/* steM */);
      if(!_qh/* steP */._){
        var _qi/* steT */ = new T(function(){
          return B(A1(_qe/* stey */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_qh/* steP */.a));
          })));
        });
        return new F(function(){return A(_qb/* steu */,[_qi/* steT */, _qc/* stev */, _qd/* stew */, _/* EXTERNAL */]);});
      }else{
        return _7/* GHC.Tuple.() */;
      }
      break;
    default:
      var _qj/* stf3 */ = rMV/* EXTERNAL */(E(E(_qe/* stey */.a).c)),
      _qk/* stf6 */ = E(_qj/* stf3 */);
      if(!_qk/* stf6 */._){
        var _ql/* stfc */ = B(A2(_qe/* stey */.b,E(_qk/* stf6 */.a).a, _/* EXTERNAL */));
        return new F(function(){return A(_qb/* steu */,[_ql/* stfc */, _qc/* stev */, _qd/* stew */, _/* EXTERNAL */]);});
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
_qo/* $fApplicativeShape3 */ = function(_qp/* stcD */, _/* EXTERNAL */){
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
_qC/* $wtext */ = function(_qD/* stTg */, _qE/* stTh */, _qF/* stTi */, _qG/* stTj */, _qH/* stTk */, _qI/* stTl */, _qJ/* stTm */){
  var _qK/* stVu */ = function(_qL/* stTn */, _qM/* stTo */, _qN/* stTp */, _/* EXTERNAL */){
    var _qO/* stVt */ = function(_qP/* stTr */, _qQ/* stTs */, _qR/* stTt */, _/* EXTERNAL */){
      var _qS/* stVs */ = function(_qT/* stTv */, _qU/* stTw */, _qV/* stTx */, _/* EXTERNAL */){
        var _qW/* stVr */ = function(_qX/* stTz */, _qY/* stTA */, _qZ/* stTB */, _/* EXTERNAL */){
          var _r0/* stTD */ = E(_qY/* stTA */),
          _r1/* stTH */ = E(_qZ/* stTB */),
          _r2/* stTK */ = __app2/* EXTERNAL */(E(_qq/* Core.Shape.Internal.f1 */), _r0/* stTD */, _r1/* stTH */),
          _r3/* stTP */ = function(_r4/* stTQ */){
            var _r5/* stTR */ = function(_r6/* stTS */){
              var _r7/* stTW */ = eval/* EXTERNAL */(E(_qB/* Core.Shape.Internal.lvl6 */)),
              _r8/* stU4 */ = __app4/* EXTERNAL */(E(_r7/* stTW */), E(_qD/* stTg */), _r4/* stTQ */, _r6/* stTS */, _r0/* stTD */),
              _r9/* stUi */ = __app4/* EXTERNAL */(E(_qu/* Core.Shape.Internal.f5 */), E(_qP/* stTr */), E(_qT/* stTv */), _r0/* stTD */, _r1/* stTH */),
              _ra/* stUn */ = E(_qX/* stTz */)/10,
              _rb/* stUt */ = __app4/* EXTERNAL */(E(_qr/* Core.Shape.Internal.f2 */), _ra/* stUn */, _ra/* stUn */, _r0/* stTD */, _r1/* stTH */);
              if(!_r1/* stTH */){
                var _rc/* stUJ */ = __app5/* EXTERNAL */(E(_qs/* Core.Shape.Internal.f3 */), toJSStr/* EXTERNAL */(E(_qL/* stTn */)), 0, 0, _r0/* stTD */, false),
                _rd/* stUP */ = __app2/* EXTERNAL */(E(_qm/* Core.Shape.Internal.$fAffineShape_f1 */), _r0/* stTD */, false);
                return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }else{
                var _re/* stV4 */ = __app5/* EXTERNAL */(E(_qt/* Core.Shape.Internal.f4 */), toJSStr/* EXTERNAL */(E(_qL/* stTn */)), 0, 0, _r0/* stTD */, true),
                _rf/* stVa */ = __app2/* EXTERNAL */(E(_qm/* Core.Shape.Internal.$fAffineShape_f1 */), _r0/* stTD */, true);
                return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }
            };
            switch(E(_qG/* stTj */)){
              case 0:
                return new F(function(){return _r5/* stTR */(E(_qx/* Core.Shape.Internal.lvl2 */));});
                break;
              case 1:
                return new F(function(){return _r5/* stTR */(E(_qw/* Core.Shape.Internal.lvl1 */));});
                break;
              default:
                return new F(function(){return _r5/* stTR */(E(_qv/* Core.Shape.Internal.lvl */));});
            }
          };
          switch(E(_qF/* stTi */)){
            case 0:
              return new F(function(){return _r3/* stTP */(E(_qA/* Core.Shape.Internal.lvl5 */));});
              break;
            case 1:
              return new F(function(){return _r3/* stTP */(E(_qz/* Core.Shape.Internal.lvl4 */));});
              break;
            default:
              return new F(function(){return _r3/* stTP */(E(_qy/* Core.Shape.Internal.lvl3 */));});
          }
        };
        return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_qJ/* stTm */, _qW/* stVr */, _qU/* stTw */, _qV/* stTx */, _/* EXTERNAL */);});
      };
      return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_qI/* stTl */, _qS/* stVs */, _qQ/* stTs */, _qR/* stTt */, _/* EXTERNAL */);});
    };
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_qH/* stTk */, _qO/* stVt */, _qM/* stTo */, _qN/* stTp */, _/* EXTERNAL */);});
  };
  return new T3(0,_qo/* Core.Shape.Internal.$fApplicativeShape3 */,function(_rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_qE/* stTh */, _qK/* stVu */, _rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */);});
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
_ro/* fill1 */ = function(_rp/* sFOq */, _rq/* sFOr */){
  return new F(function(){return _pg/* Control.Monad.Skeleton.bone */(new T2(0,function(_rr/* sFOs */, _/* EXTERNAL */){
    var _rs/* sFOu */ = E(_rp/* sFOq */),
    _rt/* sFOz */ = B(_jm/* Core.Render.Internal.$wa */(_rs/* sFOu */.a, _rs/* sFOu */.b, _rs/* sFOu */.c, _rs/* sFOu */.d, _/* EXTERNAL */)),
    _ru/* sFOC */ = E(_rr/* sFOs */),
    _rv/* sFOK */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), _ru/* sFOC */, E(_rm/* Core.Render.Internal.fill2 */), B(_o4/* Core.Render.Internal.$wcolor2JSString */(_rt/* sFOz */))),
    _rw/* sFOQ */ = __app1/* EXTERNAL */(E(_pq/* Core.Render.Internal.clip_f3 */), _ru/* sFOC */),
    _rx/* sFOX */ = B(A3(E(_rq/* sFOr */).b,_ru/* sFOC */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _ry/* sFP3 */ = __app1/* EXTERNAL */(E(_rn/* Core.Render.Internal.fill_f1 */), _ru/* sFOC */);
    return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */));});
},
_rz/* $fAffineShape3 */ = function(_rA/* stfg */, _rB/* stfh */, _/* EXTERNAL */){
  var _rC/* stfj */ = E(_rA/* stfg */);
  switch(_rC/* stfj */._){
    case 0:
      return new F(function(){return A2(_rB/* stfh */,_rC/* stfj */.a, _/* EXTERNAL */);});
      break;
    case 1:
      var _rD/* stfm */ = B(A1(_rC/* stfj */.a,_/* EXTERNAL */));
      return new F(function(){return A2(_rB/* stfh */,_rD/* stfm */, _/* EXTERNAL */);});
      break;
    case 2:
      var _rE/* stfx */ = rMV/* EXTERNAL */(E(E(_rC/* stfj */.a).c)),
      _rF/* stfA */ = E(_rE/* stfx */);
      if(!_rF/* stfA */._){
        var _rG/* stfE */ = new T(function(){
          return B(A1(_rC/* stfj */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_rF/* stfA */.a));
          })));
        });
        return new F(function(){return A2(_rB/* stfh */,_rG/* stfE */, _/* EXTERNAL */);});
      }else{
        return _av/* GHC.Types.False */;
      }
      break;
    default:
      var _rH/* stfO */ = rMV/* EXTERNAL */(E(E(_rC/* stfj */.a).c)),
      _rI/* stfR */ = E(_rH/* stfO */);
      if(!_rI/* stfR */._){
        var _rJ/* stfX */ = B(A2(_rC/* stfj */.b,E(_rI/* stfR */.a).a, _/* EXTERNAL */));
        return new F(function(){return A2(_rB/* stfh */,_rJ/* stfX */, _/* EXTERNAL */);});
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
_rM/* $wrect */ = function(_rN/* stAy */, _rO/* stAz */, _rP/* stAA */, _rQ/* stAB */){
  var _rR/* stCD */ = function(_rS/* stBA */, _rT/* stBB */, _rU/* stBC */, _/* EXTERNAL */){
    var _rV/* stCC */ = function(_rW/* stBE */, _rX/* stBF */, _rY/* stBG */, _/* EXTERNAL */){
      var _rZ/* stCB */ = function(_s0/* stBI */, _s1/* stBJ */, _s2/* stBK */, _/* EXTERNAL */){
        return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_rQ/* stAB */, function(_s3/* stBM */, _s4/* stBN */, _s5/* stBO */, _/* EXTERNAL */){
          var _s6/* stBQ */ = E(_rS/* stBA */),
          _s7/* stBU */ = E(_rW/* stBE */),
          _s8/* stBY */ = E(_s4/* stBN */),
          _s9/* stC2 */ = E(_s5/* stBO */),
          _sa/* stC5 */ = __app4/* EXTERNAL */(E(_rK/* Core.Shape.Internal.bezier_f2 */), _s6/* stBQ */, _s7/* stBU */, _s8/* stBY */, _s9/* stC2 */),
          _sb/* stCa */ = _s6/* stBQ */+E(_s0/* stBI */),
          _sc/* stCd */ = E(_rL/* Core.Shape.Internal.line_f1 */),
          _sd/* stCg */ = __app4/* EXTERNAL */(_sc/* stCd */, _sb/* stCa */, _s7/* stBU */, _s8/* stBY */, _s9/* stC2 */),
          _se/* stCl */ = _s7/* stBU */+E(_s3/* stBM */),
          _sf/* stCp */ = __app4/* EXTERNAL */(_sc/* stCd */, _sb/* stCa */, _se/* stCl */, _s8/* stBY */, _s9/* stC2 */),
          _sg/* stCt */ = __app4/* EXTERNAL */(_sc/* stCd */, _s6/* stBQ */, _se/* stCl */, _s8/* stBY */, _s9/* stC2 */),
          _sh/* stCx */ = __app4/* EXTERNAL */(_sc/* stCd */, _s6/* stBQ */, _s7/* stBU */, _s8/* stBY */, _s9/* stC2 */);
          return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        }, _s1/* stBJ */, _s2/* stBK */, _/* EXTERNAL */);});
      };
      return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_rP/* stAA */, _rZ/* stCB */, _rX/* stBF */, _rY/* stBG */, _/* EXTERNAL */);});
    };
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_rO/* stAz */, _rV/* stCC */, _rT/* stBB */, _rU/* stBC */, _/* EXTERNAL */);});
  },
  _si/* stBz */ = function(_sj/* stAC */, _/* EXTERNAL */){
    var _sk/* stAE */ = E(_sj/* stAC */),
    _sl/* stBy */ = function(_sm/* stAH */, _/* EXTERNAL */){
      var _sn/* stBx */ = function(_so/* stAJ */, _/* EXTERNAL */){
        var _sp/* stBw */ = function(_sq/* stAL */, _/* EXTERNAL */){
          var _sr/* stBv */ = function(_ss/* stAN */, _/* EXTERNAL */){
            return new T(function(){
              var _st/* stAT */ = E(_sq/* stAL */),
              _su/* stAV */ = function(_sv/* stAW */){
                var _sw/* stB1 */ = E(_ss/* stAN */),
                _sx/* stB5 */ = E(_sk/* stAE */.b)-E(_so/* stAJ */)-_sw/* stB1 *//2;
                return (_sx/* stB5 */==0) ? 0<_sw/* stB1 *//2 : (_sx/* stB5 */<=0) ?  -_sx/* stB5 */<_sw/* stB1 *//2 : _sx/* stB5 */<_sw/* stB1 *//2;
              },
              _sy/* stBh */ = E(_sk/* stAE */.a)-E(_sm/* stAH */)-_st/* stAT *//2;
              if(!_sy/* stBh */){
                if(0>=_st/* stAT *//2){
                  return false;
                }else{
                  return B(_su/* stAV */(_/* EXTERNAL */));
                }
              }else{
                if(_sy/* stBh */<=0){
                  if( -_sy/* stBh */>=_st/* stAT *//2){
                    return false;
                  }else{
                    return B(_su/* stAV */(_/* EXTERNAL */));
                  }
                }else{
                  if(_sy/* stBh */>=_st/* stAT *//2){
                    return false;
                  }else{
                    return B(_su/* stAV */(_/* EXTERNAL */));
                  }
                }
              }
            });
          };
          return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_rQ/* stAB */, _sr/* stBv */, _/* EXTERNAL */);});
        };
        return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_rP/* stAA */, _sp/* stBw */, _/* EXTERNAL */);});
      };
      return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_rO/* stAz */, _sn/* stBx */, _/* EXTERNAL */);});
    };
    return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_rN/* stAy */, _sl/* stBy */, _/* EXTERNAL */);});
  };
  return new T3(0,_si/* stBz */,function(_rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_rN/* stAy */, _rR/* stCD */, _rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_sz/* a15 */ = 0,
_sA/* lvl4 */ = new T1(0,_sz/* Motion.Main.a15 */),
_sB/* size */ = 200,
_sC/* sz */ = new T1(0,_sB/* Motion.Main.size */),
_sD/* shape */ = new T(function(){
  var _sE/* s7Ad */ = B(_rM/* Core.Shape.Internal.$wrect */(_sA/* Motion.Main.lvl4 */, _sA/* Motion.Main.lvl4 */, _sC/* Motion.Main.sz */, _sC/* Motion.Main.sz */));
  return new T3(0,_sE/* s7Ad */.a,_sE/* s7Ad */.b,_sE/* s7Ad */.c);
}),
_sF/* black1 */ = new T1(0,_f3/* Core.Render.Internal.applyTransform2 */),
_sG/* white */ = new T4(0,_sF/* Core.Render.Internal.black1 */,_sF/* Core.Render.Internal.black1 */,_sF/* Core.Render.Internal.black1 */,_sF/* Core.Render.Internal.black1 */),
_sH/* a17 */ = new T(function(){
  return B(_ro/* Core.Render.Internal.fill1 */(_sG/* Core.Render.Internal.white */, _sD/* Motion.Main.shape */));
}),
_sI/* a21 */ = function(_sJ/* s7Ah */, _sK/* s7Ai */){
  return new F(function(){return A1(_sK/* s7Ai */,new T2(0,_7/* GHC.Tuple.() */,_sJ/* s7Ah */));});
},
_sL/* black2 */ = new T1(0,_f2/* Core.Render.Internal.applyTransform1 */),
_sM/* black */ = new T4(0,_sL/* Core.Render.Internal.black2 */,_sL/* Core.Render.Internal.black2 */,_sL/* Core.Render.Internal.black2 */,_sF/* Core.Render.Internal.black1 */),
_sN/* Leave */ = 2,
_sO/* lvl2 */ = function(_sP/* sZro */){
  switch(E(_sP/* sZro */)){
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
_sQ/* lvl3 */ = function(_sR/* sZrq */){
  return (E(_sR/* sZrq */)==2) ? true : false;
},
_sS/* lvl4 */ = function(_sT/* sZrs */){
  switch(E(_sT/* sZrs */)){
    case 5:
      return true;
    case 6:
      return true;
    default:
      return false;
  }
},
_sU/* waitFor */ = function(_sV/* s6dr */, _sW/* s6ds */, _sX/* s6dt */){
  var _sY/* s6du */ = new T(function(){
    return B(_sU/* Core.Util.waitFor */(_sV/* s6dr */, _sW/* s6ds */, _sX/* s6dt */));
  });
  return new F(function(){return A3(_6u/* GHC.Base.>>= */,_sV/* s6dr */, _sX/* s6dt */, function(_sZ/* s6dv */){
    if(!B(A1(_sW/* s6ds */,_sZ/* s6dv */))){
      return E(_sY/* s6du */);
    }else{
      return new F(function(){return A2(_6T/* GHC.Base.return */,_sV/* s6dr */, _sZ/* s6dv */);});
    }
  });});
},
_t0/* button */ = function(_t1/* sZru */, _t2/* sZrv */, _t3/* sZrw */, _t4/* sZrx */){
  var _t5/* sZry */ = new T(function(){
    var _t6/* sZrz */ = new T(function(){
      var _t7/* sZrH */ = function(_t8/* sZrA */, _t9/* sZrB */){
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_t4/* sZrx */, function(_ta/* sZrC */){
          return new F(function(){return A1(_t9/* sZrB */,new T2(0,_ta/* sZrC */,_t8/* sZrA */));});
        })));
      };
      return B(_sU/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _sS/* Core.UI.lvl4 */, _t7/* sZrH */));
    }),
    _tb/* sZs4 */ = function(_tc/* sZrI */, _td/* sZrJ */){
      var _te/* sZrK */ = new T(function(){
        var _tf/* sZrX */ = function(_tg/* sZrL */){
          var _th/* sZrM */ = E(_tg/* sZrL */),
          _ti/* sZrO */ = _th/* sZrM */.b,
          _tj/* sZrP */ = E(_th/* sZrM */.a);
          if(_tj/* sZrP */==6){
            return new F(function(){return A1(_td/* sZrJ */,new T2(0,_sN/* Core.View.Leave */,_ti/* sZrO */));});
          }else{
            return new F(function(){return A2(_t3/* sZrw */,_ti/* sZrO */, function(_tk/* sZrQ */){
              return new F(function(){return A1(_td/* sZrJ */,new T2(0,_tj/* sZrP */,E(_tk/* sZrQ */).b));});
            });});
          }
        };
        return B(A2(_t6/* sZrz */,_tc/* sZrI */, _tf/* sZrX */));
      });
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_t4/* sZrx */, function(_tl/* sZrY */){
        var _tm/* sZrZ */ = E(_tl/* sZrY */);
        if(_tm/* sZrZ */==3){
          return E(_te/* sZrK */);
        }else{
          return new F(function(){return A1(_td/* sZrJ */,new T2(0,_tm/* sZrZ */,_tc/* sZrI */));});
        }
      })));
    };
    return B(_sU/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _sQ/* Core.UI.lvl3 */, _tb/* sZs4 */));
  }),
  _tn/* sZs5 */ = new T(function(){
    var _to/* sZsd */ = function(_tp/* sZs6 */, _tq/* sZs7 */){
      return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_t4/* sZrx */, function(_tr/* sZs8 */){
        return new F(function(){return A1(_tq/* sZs7 */,new T2(0,_tr/* sZs8 */,_tp/* sZs6 */));});
      })));
    };
    return B(_sU/* Core.Util.waitFor */(_8f/* Core.World.Internal.$fMonadWorld */, _sO/* Core.UI.lvl2 */, _to/* sZsd */));
  }),
  _ts/* sZse */ = function(_tt/* sZsf */){
    var _tu/* sZsg */ = new T(function(){
      return B(A1(_t1/* sZru */,_tt/* sZsf */));
    }),
    _tv/* sZsC */ = function(_tw/* sZsh */){
      var _tx/* sZsi */ = function(_ty/* sZsj */){
        return new F(function(){return A2(_ts/* sZse */,E(_ty/* sZsj */).b, _tw/* sZsh */);});
      },
      _tz/* sZsn */ = function(_tA/* sZso */){
        return new F(function(){return A2(_t5/* sZry */,E(_tA/* sZso */).b, _tx/* sZsi */);});
      },
      _tB/* sZss */ = function(_tC/* sZst */){
        return new F(function(){return A2(_t2/* sZrv */,E(_tC/* sZst */).b, _tz/* sZsn */);});
      };
      return new F(function(){return A1(_tu/* sZsg */,function(_tD/* sZsx */){
        return new F(function(){return A2(_tn/* sZs5 */,E(_tD/* sZsx */).b, _tB/* sZss */);});
      });});
    };
    return E(_tv/* sZsC */);
  };
  return E(_ts/* sZse */);
},
_tE/* clip_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx){ctx.clip();})");
}),
_tF/* clip */ = function(_tG/* sFxT */, _tH/* sFxU */){
  var _tI/* sFyq */ = B(_pg/* Control.Monad.Skeleton.bone */(new T2(0,function(_tJ/* sFxV */, _/* EXTERNAL */){
    var _tK/* sFxX */ = E(_tJ/* sFxV */),
    _tL/* sFy2 */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _tK/* sFxX */),
    _tM/* sFy8 */ = __app1/* EXTERNAL */(E(_pq/* Core.Render.Internal.clip_f3 */), _tK/* sFxX */),
    _tN/* sFyf */ = B(A3(E(_tG/* sFxT */).b,_tK/* sFxX */, _aw/* GHC.Types.True */, _/* EXTERNAL */)),
    _tO/* sFyl */ = __app1/* EXTERNAL */(E(_tE/* Core.Render.Internal.clip_f2 */), _tK/* sFxX */);
    return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */)));
  return new T2(0,E(_tI/* sFyq */.a),E(new T2(2,new T2(2,_tI/* sFyq */.b,new T1(1,function(_tP/* sFyt */){
    return E(_tH/* sFxU */);
  })),_pp/* Core.Render.Internal.clip1 */)));
},
_tQ/* easeTo2 */ = function(_tR/* sldx */, _tS/* sldy */){
  return new F(function(){return A1(_tS/* sldy */,new T2(0,_7/* GHC.Tuple.() */,_tR/* sldx */));});
},
_tT/* easeTo1 */ = function(_tU/* sldA */, _tV/* B2 */, _tW/* B1 */){
  return new F(function(){return _tQ/* Core.Ease.easeTo2 */(_tV/* B2 */, _tW/* B1 */);});
},
_tX/* easeIn */ = function(_tY/* skZK */, _tZ/* skZL */){
  return new F(function(){return A1(_tY/* skZK */,_tZ/* skZL */);});
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
_ug/* $wpoly_fail */ = function(_uh/* sl4z */){
  return new F(function(){return err/* EXTERNAL */(_uf/* Core.Ease.lvl */);});
},
_ui/* lvl1 */ = new T(function(){
  return B(_ug/* Core.Ease.$wpoly_fail */(_/* EXTERNAL */));
}),
_uj/* opLift */ = function(_uk/* sl4A */, _ul/* sl4B */, _um/* sl4C */){
  var _un/* sl4D */ = function(_uo/* sl4E */){
    var _up/* sl76 */ = function(_/* EXTERNAL */){
      var _uq/* sl4G */ = function(_/* EXTERNAL */, _ur/* sl4I */){
        var _us/* sl4J */ = E(_um/* sl4C */);
        switch(_us/* sl4J */._){
          case 0:
            return new T(function(){
              return B(A2(_uk/* sl4A */,_ur/* sl4I */, _us/* sl4J */.a));
            });
          case 1:
            var _ut/* sl4N */ = B(A1(_us/* sl4J */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sl4A */,_ur/* sl4I */, _ut/* sl4N */));
            });
          case 2:
            var _uu/* sl4Z */ = rMV/* EXTERNAL */(E(E(_us/* sl4J */.a).c)),
            _uv/* sl52 */ = E(_uu/* sl4Z */);
            return (_uv/* sl52 */._==0) ? new T(function(){
              var _uw/* sl56 */ = new T(function(){
                return B(A1(_us/* sl4J */.b,new T(function(){
                  return B(_fB/* Data.Tuple.fst */(_uv/* sl52 */.a));
                })));
              });
              return B(A2(_uk/* sl4A */,_ur/* sl4I */, _uw/* sl56 */));
            }) : E(_ui/* Core.Ease.lvl1 */);
          default:
            var _ux/* sl5i */ = rMV/* EXTERNAL */(E(E(_us/* sl4J */.a).c)),
            _uy/* sl5l */ = E(_ux/* sl5i */);
            if(!_uy/* sl5l */._){
              var _uz/* sl5r */ = B(A2(_us/* sl4J */.b,E(_uy/* sl5l */.a).a, _/* EXTERNAL */));
              return new T(function(){
                return B(A2(_uk/* sl4A */,_ur/* sl4I */, _uz/* sl5r */));
              });
            }else{
              return E(_ui/* Core.Ease.lvl1 */);
            }
        }
      },
      _uA/* sl5x */ = function(_/* EXTERNAL */){
        var _uB/* sl5z */ = E(_um/* sl4C */);
        switch(_uB/* sl5z */._){
          case 0:
            return E(_ui/* Core.Ease.lvl1 */);
          case 1:
            var _uC/* sl5D */ = B(A1(_uB/* sl5z */.a,_/* EXTERNAL */));
            return E(_ui/* Core.Ease.lvl1 */);
          case 2:
            var _uD/* sl5P */ = rMV/* EXTERNAL */(E(E(_uB/* sl5z */.a).c));
            return (E(_uD/* sl5P */)._==0) ? E(_ui/* Core.Ease.lvl1 */) : E(_ui/* Core.Ease.lvl1 */);
          default:
            var _uE/* sl66 */ = rMV/* EXTERNAL */(E(E(_uB/* sl5z */.a).c)),
            _uF/* sl69 */ = E(_uE/* sl66 */);
            if(!_uF/* sl69 */._){
              var _uG/* sl6f */ = B(A2(_uB/* sl5z */.b,E(_uF/* sl69 */.a).a, _/* EXTERNAL */));
              return E(_ui/* Core.Ease.lvl1 */);
            }else{
              return E(_ui/* Core.Ease.lvl1 */);
            }
        }
      },
      _uH/* sl6l */ = E(_ul/* sl4B */);
      switch(_uH/* sl6l */._){
        case 0:
          return new F(function(){return _uq/* sl4G */(_/* EXTERNAL */, _uH/* sl6l */.a);});
          break;
        case 1:
          var _uI/* sl6o */ = B(A1(_uH/* sl6l */.a,_/* EXTERNAL */));
          return new F(function(){return _uq/* sl4G */(_/* EXTERNAL */, _uI/* sl6o */);});
          break;
        case 2:
          var _uJ/* sl6z */ = rMV/* EXTERNAL */(E(E(_uH/* sl6l */.a).c)),
          _uK/* sl6C */ = E(_uJ/* sl6z */);
          if(!_uK/* sl6C */._){
            var _uL/* sl6J */ = new T(function(){
              return B(A1(_uH/* sl6l */.b,new T(function(){
                return E(E(_uK/* sl6C */.a).a);
              })));
            });
            return new F(function(){return _uq/* sl4G */(_/* EXTERNAL */, _uL/* sl6J */);});
          }else{
            return new F(function(){return _uA/* sl5x */(_/* EXTERNAL */);});
          }
          break;
        default:
          var _uM/* sl6T */ = rMV/* EXTERNAL */(E(E(_uH/* sl6l */.a).c)),
          _uN/* sl6W */ = E(_uM/* sl6T */);
          if(!_uN/* sl6W */._){
            var _uO/* sl72 */ = B(A2(_uH/* sl6l */.b,E(_uN/* sl6W */.a).a, _/* EXTERNAL */));
            return new F(function(){return _uq/* sl4G */(_/* EXTERNAL */, _uO/* sl72 */);});
          }else{
            return new F(function(){return _uA/* sl5x */(_/* EXTERNAL */);});
          }
      }
    };
    return new T1(1,_up/* sl76 */);
  },
  _uP/* sl77 */ = E(_ul/* sl4B */);
  switch(_uP/* sl77 */._){
    case 0:
      var _uQ/* sl78 */ = _uP/* sl77 */.a,
      _uR/* sl79 */ = E(_um/* sl4C */);
      switch(_uR/* sl79 */._){
        case 0:
          return new T1(0,new T(function(){
            return B(A2(_uk/* sl4A */,_uQ/* sl78 */, _uR/* sl79 */.a));
          }));
        case 1:
          var _uS/* sl7i */ = function(_/* EXTERNAL */){
            var _uT/* sl7e */ = B(A1(_uR/* sl79 */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sl4A */,_uQ/* sl78 */, _uT/* sl7e */));
            });
          };
          return new T1(1,_uS/* sl7i */);
        case 2:
          var _uU/* sl7l */ = new T(function(){
            return B(A1(_uk/* sl4A */,_uQ/* sl78 */));
          }),
          _uV/* sl7o */ = function(_uW/* sl7m */){
            return new F(function(){return A1(_uU/* sl7l */,new T(function(){
              return B(A1(_uR/* sl79 */.b,_uW/* sl7m */));
            }));});
          };
          return new T2(2,_uR/* sl79 */.a,_uV/* sl7o */);
        default:
          var _uX/* sl7r */ = new T(function(){
            return B(A1(_uk/* sl4A */,_uQ/* sl78 */));
          }),
          _uY/* sl7y */ = function(_uZ/* sl7s */, _/* EXTERNAL */){
            var _v0/* sl7u */ = B(A2(_uR/* sl79 */.b,_uZ/* sl7s */, _/* EXTERNAL */));
            return new T(function(){
              return B(A1(_uX/* sl7r */,_v0/* sl7u */));
            });
          };
          return new T2(3,_uR/* sl79 */.a,_uY/* sl7y */);
      }
      break;
    case 1:
      var _v1/* sl7z */ = _uP/* sl77 */.a,
      _v2/* sl7A */ = E(_um/* sl4C */);
      switch(_v2/* sl7A */._){
        case 0:
          var _v3/* sl7H */ = function(_/* EXTERNAL */){
            var _v4/* sl7D */ = B(A1(_v1/* sl7z */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sl4A */,_v4/* sl7D */, _v2/* sl7A */.a));
            });
          };
          return new T1(1,_v3/* sl7H */);
        case 1:
          return new T1(1,function(_/* EXTERNAL */){
            return new F(function(){return _u9/* GHC.Base.liftA1 */(_uk/* sl4A */, _v1/* sl7z */, _v2/* sl7A */.a, _/* EXTERNAL */);});
          });
        case 2:
          var _v5/* sl7T */ = function(_v6/* sl7M */, _/* EXTERNAL */){
            var _v7/* sl7O */ = B(A1(_v1/* sl7z */,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sl4A */,_v7/* sl7O */, new T(function(){
                return B(A1(_v2/* sl7A */.b,_v6/* sl7M */));
              })));
            });
          };
          return new T2(3,_v2/* sl7A */.a,_v5/* sl7T */);
        default:
          var _v8/* sl85 */ = function(_v9/* sl7W */, _/* EXTERNAL */){
            var _va/* sl7Y */ = B(A1(_v1/* sl7z */,_/* EXTERNAL */)),
            _vb/* sl81 */ = B(A2(_v2/* sl7A */.b,_v9/* sl7W */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sl4A */,_va/* sl7Y */, _vb/* sl81 */));
            });
          };
          return new T2(3,_v2/* sl7A */.a,_v8/* sl85 */);
      }
      break;
    case 2:
      var _vc/* sl86 */ = _uP/* sl77 */.a,
      _vd/* sl87 */ = _uP/* sl77 */.b,
      _ve/* sl88 */ = E(_um/* sl4C */);
      switch(_ve/* sl88 */._){
        case 0:
          var _vf/* sl8c */ = function(_vg/* sl8a */){
            return new F(function(){return A2(_uk/* sl4A */,new T(function(){
              return B(A1(_vd/* sl87 */,_vg/* sl8a */));
            }), _ve/* sl88 */.a);});
          };
          return new T2(2,_vc/* sl86 */,_vf/* sl8c */);
        case 1:
          var _vh/* sl8l */ = function(_vi/* sl8e */, _/* EXTERNAL */){
            var _vj/* sl8g */ = B(A1(_ve/* sl88 */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sl4A */,new T(function(){
                return B(A1(_vd/* sl87 */,_vi/* sl8e */));
              }), _vj/* sl8g */));
            });
          };
          return new T2(3,_vc/* sl86 */,_vh/* sl8l */);
        default:
          return new F(function(){return _un/* sl4D */(_/* EXTERNAL */);});
      }
      break;
    default:
      var _vk/* sl8m */ = _uP/* sl77 */.a,
      _vl/* sl8n */ = _uP/* sl77 */.b,
      _vm/* sl8o */ = E(_um/* sl4C */);
      switch(_vm/* sl8o */._){
        case 0:
          var _vn/* sl8w */ = function(_vo/* sl8q */, _/* EXTERNAL */){
            var _vp/* sl8s */ = B(A2(_vl/* sl8n */,_vo/* sl8q */, _/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sl4A */,_vp/* sl8s */, _vm/* sl8o */.a));
            });
          };
          return new T2(3,_vk/* sl8m */,_vn/* sl8w */);
        case 1:
          var _vq/* sl8H */ = function(_vr/* sl8y */, _/* EXTERNAL */){
            var _vs/* sl8A */ = B(A2(_vl/* sl8n */,_vr/* sl8y */, _/* EXTERNAL */)),
            _vt/* sl8D */ = B(A1(_vm/* sl8o */.a,_/* EXTERNAL */));
            return new T(function(){
              return B(A2(_uk/* sl4A */,_vs/* sl8A */, _vt/* sl8D */));
            });
          };
          return new T2(3,_vk/* sl8m */,_vq/* sl8H */);
        default:
          return new F(function(){return _un/* sl4D */(_/* EXTERNAL */);});
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
_vE/* lvl20 */ = function(_vF/* s7Ak */){
  var _vG/* s7Al */ = E(_vF/* s7Ak */);
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
_vQ/* $fAffineShape1 */ = function(_vR/* stnh */, _vS/* stni */, _vT/* stnj */, _/* EXTERNAL */){
  var _vU/* stns */ = __app2/* EXTERNAL */(E(_qm/* Core.Shape.Internal.$fAffineShape_f1 */), E(_vS/* stni */), E(_vT/* stnj */));
  return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_vV/* $w$caffine */ = function(_vW/* stnv */, _vX/* stnw */, _vY/* stnx */, _vZ/* stny */, _w0/* stnz */, _w1/* stnA */, _w2/* stnB */){
  var _w3/* stpl */ = function(_w4/* stoX */, _w5/* stoY */, _w6/* stoZ */, _/* EXTERNAL */){
    var _w7/* stpk */ = function(_w8/* stp1 */, _w9/* stp2 */, _wa/* stp3 */, _/* EXTERNAL */){
      var _wb/* stpj */ = function(_wc/* stp5 */, _wd/* stp6 */, _we/* stp7 */, _/* EXTERNAL */){
        var _wf/* stpi */ = function(_wg/* stp9 */, _wh/* stpa */, _wi/* stpb */, _/* EXTERNAL */){
          return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_w0/* stnz */, function(_wj/* stpd */, _wk/* stpe */, _wl/* stpf */, _/* EXTERNAL */){
            return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_w1/* stnA */, _vQ/* Core.Shape.Internal.$fAffineShape1 */, _wk/* stpe */, _wl/* stpf */, _/* EXTERNAL */);});
          }, _wh/* stpa */, _wi/* stpb */, _/* EXTERNAL */);});
        };
        return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_vZ/* stny */, _wf/* stpi */, _wd/* stp6 */, _we/* stp7 */, _/* EXTERNAL */);});
      };
      return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_vY/* stnx */, _wb/* stpj */, _w9/* stp2 */, _wa/* stp3 */, _/* EXTERNAL */);});
    };
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_vX/* stnw */, _w7/* stpk */, _w5/* stoY */, _w6/* stoZ */, _/* EXTERNAL */);});
  },
  _wm/* stoW */ = function(_wn/* stnC */, _/* EXTERNAL */){
    var _wo/* stnE */ = E(_wn/* stnC */),
    _wp/* stnF */ = _wo/* stnE */.a,
    _wq/* stnG */ = _wo/* stnE */.b,
    _wr/* stoV */ = function(_ws/* stnH */, _/* EXTERNAL */){
      var _wt/* stoU */ = function(_wu/* stnJ */, _/* EXTERNAL */){
        var _wv/* stoT */ = function(_ww/* stnL */, _/* EXTERNAL */){
          var _wx/* stoS */ = function(_wy/* stnN */, _/* EXTERNAL */){
            var _wz/* stoR */ = function(_wA/* stnP */, _/* EXTERNAL */){
              var _wB/* stoQ */ = function(_wC/* stnR */){
                var _wD/* stnS */ = new T(function(){
                  return E(_wu/* stnJ */)*E(_wy/* stnN */)-E(_ws/* stnH */)*E(_wA/* stnP */);
                });
                return new F(function(){return A1(_w2/* stnB */,new T2(0,new T(function(){
                  var _wE/* sto4 */ = E(_wu/* stnJ */),
                  _wF/* stoa */ = E(_wA/* stnP */);
                  return ( -(_wE/* sto4 */*E(_wC/* stnR */))+_wE/* sto4 */*E(_wq/* stnG */)+_wF/* stoa */*E(_ww/* stnL */)-_wF/* stoa */*E(_wp/* stnF */))/E(_wD/* stnS */);
                }),new T(function(){
                  var _wG/* stos */ = E(_ws/* stnH */),
                  _wH/* stoy */ = E(_wy/* stnN */);
                  return (_wG/* stos */*E(_wC/* stnR */)-_wG/* stos */*E(_wq/* stnG */)-_wH/* stoy */*E(_ww/* stnL */)+_wH/* stoy */*E(_wp/* stnF */))/E(_wD/* stnS */);
                })));});
              };
              return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_w1/* stnA */, _wB/* stoQ */, _/* EXTERNAL */);});
            };
            return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_w0/* stnz */, _wz/* stoR */, _/* EXTERNAL */);});
          };
          return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_vZ/* stny */, _wx/* stoS */, _/* EXTERNAL */);});
        };
        return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_vY/* stnx */, _wv/* stoT */, _/* EXTERNAL */);});
      };
      return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_vX/* stnw */, _wt/* stoU */, _/* EXTERNAL */);});
    };
    return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_vW/* stnv */, _wr/* stoV */, _/* EXTERNAL */);});
  };
  return new T3(0,_wm/* stoW */,function(_rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_vW/* stnv */, _w3/* stpl */, _rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_wI/* forceTo_b1 */ = 1,
_wJ/* $wforceTo */ = function(_wK/* skZM */, _wL/* skZN */){
  var _wM/* skZO */ = new T(function(){
    var _wN/* sl05 */ = function(_wO/* skZP */, _wP/* skZQ */, _wQ/* skZR */){
      return new F(function(){return A1(_wQ/* skZR */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,new T2(0,_wL/* skZN */,new T4(0,_wL/* skZN */,_wL/* skZN */,_wI/* Core.Ease.forceTo_b1 */,new T(function(){
        return E(E(E(_wO/* skZP */).b).d);
      })))),_wP/* skZQ */));});
    };
    return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _wK/* skZM */, _wN/* sl05 */));
  }),
  _wR/* sl0w */ = function(_wS/* sl06 */, _wT/* sl07 */){
    var _wU/* sl08 */ = new T(function(){
      return B(A2(_wM/* skZO */,_wS/* sl06 */, _wT/* sl07 */));
    }),
    _wV/* sl0t */ = function(_wW/* sl09 */){
      var _wX/* sl0a */ = new T(function(){
        var _wY/* sl0b */ = E(_wW/* sl09 */),
        _wZ/* sl0e */ = E(_wY/* sl0b */.a),
        _x0/* sl0f */ = E(_wY/* sl0b */.b),
        _x1/* sl0k */ = E(_x0/* sl0f */.a),
        _x2/* sl0l */ = E(_x0/* sl0f */.b),
        _x3/* sl0n */ = E(_x0/* sl0f */.c),
        _x4/* sl0o */ = E(_x0/* sl0f */.d);
        return E(_wU/* sl08 */);
      });
      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_wK/* skZM */, _wW/* sl09 */, function(_x5/* sl0p */){
        return E(_wX/* sl0a */);
      })));
    };
    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_wK/* skZM */, _wV/* sl0t */)));
  };
  return E(_wR/* sl0w */);
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
_xE/* lvl23 */ = function(_xF/* sWfn */, _xG/* sWfo */){
  return new F(function(){return A1(_xG/* sWfo */,new T2(0,_7/* GHC.Tuple.() */,_xF/* sWfn */));});
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
_y5/* makeView */ = function(_y6/* sWfq */, _y7/* sWfr */, _y8/* sWfs */, _y9/* sWft */){
  var _ya/* sWfu */ = new T(function(){
    return B(A1(_y6/* sWfq */,_sN/* Core.View.Leave */));
  }),
  _yb/* sWfv */ = new T(function(){
    return B(A1(_y6/* sWfq */,_xA/* Core.View.Enter */));
  }),
  _yc/* sWfw */ = new T(function(){
    return B(A1(_y6/* sWfq */,_xz/* Core.View.Drag */));
  }),
  _yd/* sWfx */ = new T(function(){
    return B(_xX/* Haste.Concurrent.spawn */(_8l/* Core.World.Internal.$fMonadConcWorld */, _y9/* sWft */));
  }),
  _ye/* sWfy */ = new T(function(){
    return B(A1(_y6/* sWfq */,_xy/* Core.View.Cancel */));
  }),
  _yf/* sWfz */ = new T(function(){
    return B(A1(_y6/* sWfq */,_xD/* Core.View.Release */));
  }),
  _yg/* sWfA */ = new T(function(){
    return B(A1(_y6/* sWfq */,_xC/* Core.View.Press */));
  }),
  _yh/* sWfB */ = new T(function(){
    return B(A1(_y6/* sWfq */,_xB/* Core.View.Move */));
  }),
  _yi/* sWkQ */ = function(_yj/* sWfC */){
    var _yk/* sWfD */ = new T(function(){
      return B(A1(_yd/* sWfx */,_yj/* sWfC */));
    }),
    _yl/* sWkP */ = function(_ym/* sWfE */){
      var _yn/* sWkO */ = function(_yo/* sWfF */){
        var _yp/* sWfG */ = E(_yo/* sWfF */),
        _yq/* sWfH */ = _yp/* sWfG */.a,
        _yr/* sWfI */ = _yp/* sWfG */.b,
        _ys/* sWfJ */ = new T(function(){
          var _yt/* sWfK */ = E(_ya/* sWfu */);
          if(!_yt/* sWfK */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sWfH */, _yt/* sWfK */.a));
          }
        }),
        _yu/* sWfM */ = new T(function(){
          var _yv/* sWfN */ = E(_yb/* sWfv */);
          if(!_yv/* sWfN */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sWfH */, _yv/* sWfN */.a));
          }
        }),
        _yw/* sWfP */ = new T(function(){
          var _yx/* sWfQ */ = E(_yc/* sWfw */);
          if(!_yx/* sWfQ */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sWfH */, _yx/* sWfQ */.a));
          }
        }),
        _yy/* sWfS */ = new T(function(){
          var _yz/* sWfT */ = E(_ye/* sWfy */);
          if(!_yz/* sWfT */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sWfH */, _yz/* sWfT */.a));
          }
        }),
        _yA/* sWfV */ = new T(function(){
          var _yB/* sWfW */ = E(_yf/* sWfz */);
          if(!_yB/* sWfW */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sWfH */, _yB/* sWfW */.a));
          }
        }),
        _yC/* sWfY */ = new T(function(){
          var _yD/* sWfZ */ = E(_yg/* sWfA */);
          if(!_yD/* sWfZ */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sWfH */, _yD/* sWfZ */.a));
          }
        }),
        _yE/* sWg1 */ = new T(function(){
          var _yF/* sWg2 */ = E(_yh/* sWfB */);
          if(!_yF/* sWg2 */._){
            return E(_xE/* Core.View.lvl23 */);
          }else{
            return B(_2X/* Haste.Concurrent.! */(_8l/* Core.World.Internal.$fMonadConcWorld */, _yq/* sWfH */, _yF/* sWg2 */.a));
          }
        }),
        _yG/* sWkN */ = function(_/* EXTERNAL */){
          var _yH/* sWg5 */ = nMV/* EXTERNAL */(_xP/* Core.View.lvl30 */),
          _yI/* sWg7 */ = _yH/* sWg5 */,
          _yJ/* sWkL */ = function(_/* EXTERNAL */){
            var _yK/* sWga */ = nMV/* EXTERNAL */(_xL/* Core.View.lvl27 */),
            _yL/* sWgc */ = _yK/* sWga */,
            _yM/* sWkJ */ = function(_/* EXTERNAL */){
              var _yN/* sWgf */ = nMV/* EXTERNAL */(_xL/* Core.View.lvl27 */),
              _yO/* sWgh */ = _yN/* sWgf */,
              _yP/* sWkH */ = function(_/* EXTERNAL */){
                var _yQ/* sWgk */ = nMV/* EXTERNAL */(_xL/* Core.View.lvl27 */),
                _yR/* sWgm */ = _yQ/* sWgk */,
                _yS/* sWkF */ = function(_/* EXTERNAL */){
                  var _yT/* sWgp */ = nMV/* EXTERNAL */(_xP/* Core.View.lvl30 */),
                  _yU/* sWgr */ = _yT/* sWgp */,
                  _yV/* sWkD */ = function(_/* EXTERNAL */){
                    var _yW/* sWgu */ = nMV/* EXTERNAL */(_xL/* Core.View.lvl27 */),
                    _yX/* sWgw */ = _yW/* sWgu */,
                    _yY/* sWgy */ = new T(function(){
                      var _yZ/* sWhl */ = function(_z0/* sWgz */, _z1/* sWgA */, _z2/* sWgB */, _z3/* sWgC */, _z4/* sWgD */, _z5/* sWgE */){
                        var _z6/* sWgF */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yI/* sWg7 */, _z0/* sWgz */));
                        }),
                        _z7/* sWgG */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yL/* sWgc */, _z1/* sWgA */));
                        }),
                        _z8/* sWgH */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yO/* sWgh */, _z2/* sWgB */));
                        }),
                        _z9/* sWgI */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yR/* sWgm */, _z3/* sWgC */));
                        }),
                        _za/* sWgJ */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yU/* sWgr */, _z4/* sWgD */));
                        }),
                        _zb/* sWgK */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_yX/* sWgw */, _z5/* sWgE */));
                        }),
                        _zc/* sWhk */ = function(_zd/* sWgL */){
                          var _ze/* sWgM */ = new T(function(){
                            return B(A1(_z6/* sWgF */,_zd/* sWgL */));
                          }),
                          _zf/* sWhj */ = function(_zg/* sWgN */){
                            var _zh/* sWgO */ = function(_zi/* sWgP */){
                              return new F(function(){return A1(_zg/* sWgN */,new T2(0,_7/* GHC.Tuple.() */,E(_zi/* sWgP */).b));});
                            },
                            _zj/* sWgU */ = function(_zk/* sWgV */){
                              return new F(function(){return A2(_zb/* sWgK */,E(_zk/* sWgV */).b, _zh/* sWgO */);});
                            },
                            _zl/* sWgZ */ = function(_zm/* sWh0 */){
                              return new F(function(){return A2(_za/* sWgJ */,E(_zm/* sWh0 */).b, _zj/* sWgU */);});
                            },
                            _zn/* sWh4 */ = function(_zo/* sWh5 */){
                              return new F(function(){return A2(_z9/* sWgI */,E(_zo/* sWh5 */).b, _zl/* sWgZ */);});
                            },
                            _zp/* sWh9 */ = function(_zq/* sWha */){
                              return new F(function(){return A2(_z8/* sWgH */,E(_zq/* sWha */).b, _zn/* sWh4 */);});
                            };
                            return new F(function(){return A1(_ze/* sWgM */,function(_zr/* sWhe */){
                              return new F(function(){return A2(_z7/* sWgG */,E(_zr/* sWhe */).b, _zp/* sWh9 */);});
                            });});
                          };
                          return E(_zf/* sWhj */);
                        };
                        return E(_zc/* sWhk */);
                      };
                      return B(_pg/* Control.Monad.Skeleton.bone */(new T2(2,_yZ/* sWhl */,_7/* GHC.Tuple.() */)));
                    }),
                    _zs/* sWhn */ = new T(function(){
                      var _zt/* sWho */ = E(_y8/* sWfs */);
                      return new T2(0,E(_zt/* sWho */.a),E(new T2(2,_zt/* sWho */.b,new T1(1,function(_zu/* sWhr */){
                        return E(_yY/* sWgy */);
                      }))));
                    }),
                    _zv/* sWhv */ = new T(function(){
                      var _zw/* sWhM */ = B(_vV/* Core.Shape.Internal.$w$caffine */(new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yI/* sWg7 */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yL/* sWgc */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yO/* sWgh */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yR/* sWgm */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yU/* sWgr */),_2E/* GHC.Base.id */), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_yX/* sWgw */),_2E/* GHC.Base.id */), E(_y7/* sWfr */).a));
                      return new T3(0,_zw/* sWhM */.a,_zw/* sWhM */.b,_zw/* sWhM */.c);
                    }),
                    _zx/* sWkB */ = function(_/* EXTERNAL */){
                      var _zy/* sWhR */ = nMV/* EXTERNAL */(_xH/* Core.View.lvl24 */),
                      _zz/* sWhT */ = _zy/* sWhR */,
                      _zA/* sWkx */ = new T(function(){
                        var _zB/* sWiH */ = function(_zC/* sWjf */){
                          return new F(function(){return _zD/* sWiG */(E(_zC/* sWjf */).b);});
                        },
                        _zE/* sWiJ */ = function(_zF/* sWjn */){
                          var _zG/* sWjo */ = new T(function(){
                            return B(A2(_yE/* sWg1 */,_zF/* sWjn */, _zH/* sWiI */));
                          }),
                          _zI/* sWjp */ = new T(function(){
                            return B(A2(_ys/* sWfJ */,_zF/* sWjn */, _zB/* sWiH */));
                          }),
                          _zJ/* sWjq */ = new T(function(){
                            return B(A2(_yC/* sWfY */,_zF/* sWjn */, _zK/* sWiF */));
                          }),
                          _zL/* sWjr */ = new T(function(){
                            return B(_zE/* sWiJ */(_zF/* sWjn */));
                          }),
                          _zM/* sWjI */ = function(_zN/* sWjs */){
                            var _zO/* sWjt */ = E(_zN/* sWjs */);
                            if(!_zO/* sWjt */._){
                              return (!E(_zO/* sWjt */.a)) ? E(_zL/* sWjr */) : E(_zJ/* sWjq */);
                            }else{
                              var _zP/* sWjH */ = function(_/* EXTERNAL */){
                                var _zQ/* sWjC */ = B(A2(E(_zv/* sWhv */).a,_zO/* sWjt */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_zQ/* sWjC */)){
                                    return E(_zI/* sWjp */);
                                  }else{
                                    return E(_zG/* sWjo */);
                                  }
                                });
                              };
                              return new T1(0,_zP/* sWjH */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zz/* sWhT */, _zM/* sWjI */)));
                        },
                        _zH/* sWiI */ = function(_zR/* sWjj */){
                          return new F(function(){return _zE/* sWiJ */(E(_zR/* sWjj */).b);});
                        },
                        _zD/* sWiG */ = function(_zS/* sWiU */){
                          var _zT/* sWiV */ = new T(function(){
                            return B(_zD/* sWiG */(_zS/* sWiU */));
                          }),
                          _zU/* sWiW */ = new T(function(){
                            return B(A2(_yu/* sWfM */,_zS/* sWiU */, _zH/* sWiI */));
                          }),
                          _zV/* sWjc */ = function(_zW/* sWiX */){
                            var _zX/* sWiY */ = E(_zW/* sWiX */);
                            if(!_zX/* sWiY */._){
                              return E(_zT/* sWiV */);
                            }else{
                              var _zY/* sWjb */ = function(_/* EXTERNAL */){
                                var _zZ/* sWj6 */ = B(A2(E(_zv/* sWhv */).a,_zX/* sWiY */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_zZ/* sWj6 */)){
                                    return E(_zT/* sWiV */);
                                  }else{
                                    return E(_zU/* sWiW */);
                                  }
                                });
                              };
                              return new T1(0,_zY/* sWjb */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zz/* sWhT */, _zV/* sWjc */)));
                        },
                        _A0/* sWiK */ = function(_A1/* sWjL */){
                          var _A2/* sWjM */ = new T(function(){
                            return B(A2(_yw/* sWfP */,_A1/* sWjL */, _zK/* sWiF */));
                          }),
                          _A3/* sWjN */ = new T(function(){
                            return B(A2(_ys/* sWfJ */,_A1/* sWjL */, _A4/* sWiE */));
                          }),
                          _A5/* sWjO */ = new T(function(){
                            return B(_A0/* sWiK */(_A1/* sWjL */));
                          }),
                          _A6/* sWjP */ = new T(function(){
                            return B(A2(_yA/* sWfV */,_A1/* sWjL */, _zH/* sWiI */));
                          }),
                          _A7/* sWk6 */ = function(_A8/* sWjQ */){
                            var _A9/* sWjR */ = E(_A8/* sWjQ */);
                            if(!_A9/* sWjR */._){
                              return (!E(_A9/* sWjR */.a)) ? E(_A6/* sWjP */) : E(_A5/* sWjO */);
                            }else{
                              var _Aa/* sWk5 */ = function(_/* EXTERNAL */){
                                var _Ab/* sWk0 */ = B(A2(E(_zv/* sWhv */).a,_A9/* sWjR */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_Ab/* sWk0 */)){
                                    return E(_A3/* sWjN */);
                                  }else{
                                    return E(_A2/* sWjM */);
                                  }
                                });
                              };
                              return new T1(0,_Aa/* sWk5 */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zz/* sWhT */, _A7/* sWk6 */)));
                        },
                        _zK/* sWiF */ = function(_Ac/* sWiQ */){
                          return new F(function(){return _A0/* sWiK */(E(_Ac/* sWiQ */).b);});
                        },
                        _Ad/* sWiL */ = function(_Ae/* sWk9 */){
                          var _Af/* sWka */ = new T(function(){
                            return B(A2(_yu/* sWfM */,_Ae/* sWk9 */, _zK/* sWiF */));
                          }),
                          _Ag/* sWkb */ = new T(function(){
                            return B(A2(_yw/* sWfP */,_Ae/* sWk9 */, _A4/* sWiE */));
                          }),
                          _Ah/* sWkc */ = new T(function(){
                            return B(_Ad/* sWiL */(_Ae/* sWk9 */));
                          }),
                          _Ai/* sWkd */ = new T(function(){
                            return B(A2(_yy/* sWfS */,_Ae/* sWk9 */, _zB/* sWiH */));
                          }),
                          _Aj/* sWku */ = function(_Ak/* sWke */){
                            var _Al/* sWkf */ = E(_Ak/* sWke */);
                            if(!_Al/* sWkf */._){
                              return (!E(_Al/* sWkf */.a)) ? E(_Ai/* sWkd */) : E(_Ah/* sWkc */);
                            }else{
                              var _Am/* sWkt */ = function(_/* EXTERNAL */){
                                var _An/* sWko */ = B(A2(E(_zv/* sWhv */).a,_Al/* sWkf */.a, _/* EXTERNAL */));
                                return new T(function(){
                                  if(!E(_An/* sWko */)){
                                    return E(_Ag/* sWkb */);
                                  }else{
                                    return E(_Af/* sWka */);
                                  }
                                });
                              };
                              return new T1(0,_Am/* sWkt */);
                            }
                          };
                          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_zz/* sWhT */, _Aj/* sWku */)));
                        },
                        _A4/* sWiE */ = function(_Ao/* sWiM */){
                          return new F(function(){return _Ad/* sWiL */(E(_Ao/* sWiM */).b);});
                        };
                        return B(_zD/* sWiG */(_yr/* sWfI */));
                      }),
                      _Ap/* sWiD */ = new T(function(){
                        var _Aq/* sWiC */ = function(_Ar/* sWis */){
                          var _As/* sWit */ = E(_Ar/* sWis */);
                          return new F(function(){return A1(_ym/* sWfE */,new T2(0,new T(function(){
                            return new T3(0,E(_As/* sWit */.a),_zs/* sWhn */,E(_yq/* sWfH */));
                          }),_As/* sWit */.b));});
                        },
                        _At/* sWir */ = function(_Au/* sWhV */, _Av/* sWhW */, _Aw/* sWhX */){
                          var _Ax/* sWhY */ = new T(function(){
                            return E(E(_Au/* sWhV */).d);
                          }),
                          _Ay/* sWi4 */ = new T(function(){
                            return E(E(_Ax/* sWhY */).a);
                          }),
                          _Az/* sWio */ = new T(function(){
                            var _AA/* sWi8 */ = E(_Au/* sWhV */);
                            return new T4(0,E(_AA/* sWi8 */.a),_AA/* sWi8 */.b,E(_AA/* sWi8 */.c),E(new T2(0,new T(function(){
                              return E(_Ay/* sWi4 */)+1|0;
                            }),new T(function(){
                              return B(_x6/* Data.IntMap.Strict.$winsert */(E(_Ay/* sWi4 */), _zz/* sWhT */, E(_Ax/* sWhY */).b));
                            }))));
                          });
                          return new F(function(){return A1(_Aw/* sWhX */,new T2(0,new T2(0,_Ay/* sWi4 */,_Az/* sWio */),_Av/* sWhW */));});
                        };
                        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _yr/* sWfI */, _At/* sWir */, _yr/* sWfI */, _Aq/* sWiC */]));
                      });
                      return new T1(1,new T2(1,_Ap/* sWiD */,new T2(1,_zA/* sWkx */,_6/* GHC.Types.[] */)));
                    };
                    return new T1(0,_zx/* sWkB */);
                  };
                  return new T1(0,_yV/* sWkD */);
                };
                return new T1(0,_yS/* sWkF */);
              };
              return new T1(0,_yP/* sWkH */);
            };
            return new T1(0,_yM/* sWkJ */);
          };
          return new T1(0,_yJ/* sWkL */);
        };
        return new T1(0,_yG/* sWkN */);
      };
      return new F(function(){return A1(_yk/* sWfD */,_yn/* sWkO */);});
    };
    return E(_yl/* sWkP */);
  };
  return E(_yi/* sWkQ */);
},
_AB/* $wconsView */ = function(_AC/* s7Ao */, _AD/* s7Ap */, _AE/* s7Aq */){
  var _AF/* s7Ar */ = new T(function(){
    var _AG/* s7Ay */ = new T(function(){
      return B(_ro/* Core.Render.Internal.fill1 */(_u5/* Motion.Main.lvl10 */, new T(function(){
        var _AH/* s7At */ = B(_qC/* Core.Shape.Internal.$wtext */(_u6/* Motion.Main.lvl11 */, new T1(0,_AE/* s7Aq */), _rl/* Core.Shape.Internal.LeftAlign */, _ri/* Core.Shape.Internal.BottomBase */, _vx/* Motion.Main.lvl14 */, _vA/* Motion.Main.lvl17 */, _vB/* Motion.Main.lvl18 */));
        return new T3(0,_AH/* s7At */.a,_AH/* s7At */.b,_AH/* s7At */.c);
      })));
    });
    return B(_pH/* Core.Render.Internal.$wshadowed */(_sA/* Motion.Main.lvl4 */, _vM/* Motion.Main.lvl5 */, _vO/* Motion.Main.lvl6 */, _vP/* Motion.Main.lvl8 */, _AG/* s7Ay */));
  }),
  _AI/* s7Az */ = function(_AJ/* s7AA */){
    return E(_AF/* s7Ar */);
  },
  _AK/* s7AC */ = new T(function(){
    return B(A1(_AD/* s7Ap */,_AC/* s7Ao */));
  }),
  _AL/* s7Bn */ = function(_AM/* s7AD */){
    var _AN/* s7AE */ = new T(function(){
      return B(A1(_AK/* s7AC */,_AM/* s7AD */));
    }),
    _AO/* s7Bm */ = function(_AP/* s7AF */){
      var _AQ/* s7Bl */ = function(_AR/* s7AG */){
        var _AS/* s7AH */ = E(_AR/* s7AG */),
        _AT/* s7AK */ = E(_AS/* s7AH */.a),
        _AU/* s7AN */ = new T(function(){
          var _AV/* s7AO */ = B(_tF/* Core.Render.Internal.clip */(_sD/* Motion.Main.shape */, _AT/* s7AK */.a));
          return new T2(0,E(_AV/* s7AO */.a),E(new T2(2,_AV/* s7AO */.b,new T1(1,_AI/* s7Az */))));
        }),
        _AW/* s7Bk */ = function(_/* EXTERNAL */){
          var _AX/* s7AT */ = nMV/* EXTERNAL */(_vJ/* Motion.Main.lvl23 */);
          return new T(function(){
            var _AY/* s7AX */ = new T(function(){
              return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _vK/* Motion.Main.lvl3 */, _u0/* Core.Ease.linear */, _AX/* s7AT */, _vD/* Motion.Main.lvl2 */, _tT/* Core.Ease.easeTo1 */));
            }),
            _AZ/* s7AY */ = new T(function(){
              return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _vK/* Motion.Main.lvl3 */, _u0/* Core.Ease.linear */, _AX/* s7AT */, _vC/* Motion.Main.lvl19 */, _tT/* Core.Ease.easeTo1 */));
            }),
            _B0/* s7Bi */ = function(_B1/* s7B9 */){
              var _B2/* s7Ba */ = new T(function(){
                return B(_t0/* Core.UI.button */(_AY/* s7AX */, _AZ/* s7AY */, _sI/* Motion.Main.a21 */, _B1/* s7B9 */));
              }),
              _B3/* s7Bh */ = function(_B4/* s7Bb */, _B5/* s7Bc */){
                return new T1(1,new T2(1,new T(function(){
                  return B(A2(_B2/* s7Ba */,_B4/* s7Bb */, _B5/* s7Bc */));
                }),new T2(1,new T(function(){
                  return B(A2(_AT/* s7AK */.b,_B4/* s7Bb */, _vE/* Motion.Main.lvl20 */));
                }),_6/* GHC.Types.[] */)));
              };
              return E(_B3/* s7Bh */);
            },
            _B6/* s7B8 */ = new T(function(){
              var _B7/* s7B1 */ = B(_pH/* Core.Render.Internal.$wshadowed */(_sA/* Motion.Main.lvl4 */, _vM/* Motion.Main.lvl5 */, new T2(2,new T3(0,_vK/* Motion.Main.lvl3 */,_u0/* Core.Ease.linear */,_AX/* s7AT */),_2E/* GHC.Base.id */), _sM/* Core.Render.Internal.black */, _sH/* Motion.Main.a17 */));
              return new T2(0,E(_B7/* s7B1 */.a),E(new T2(2,_B7/* s7B1 */.b,new T1(1,function(_B8/* s7B4 */){
                return E(_AU/* s7AN */);
              }))));
            });
            return B(A(_y5/* Core.View.makeView */,[_rj/* GHC.Base.Just */, _sD/* Motion.Main.shape */, _B6/* s7B8 */, _B0/* s7Bi */, _AS/* s7AH */.b, _AP/* s7AF */]));
          });
        };
        return new T1(0,_AW/* s7Bk */);
      };
      return new F(function(){return A1(_AN/* s7AE */,_AQ/* s7Bl */);});
    };
    return E(_AO/* s7Bm */);
  };
  return E(_AL/* s7Bn */);
},
_B9/* waitUntil2 */ = new T1(1,_6/* GHC.Types.[] */),
_Ba/* $wa6 */ = function(_Bb/* sbVt */, _Bc/* sbVu */, _Bd/* sbVv */){
  return function(_/* EXTERNAL */){
    var _Be/* sbVx */ = nMV/* EXTERNAL */(_B9/* Core.World.Internal.waitUntil2 */),
    _Bf/* sbVz */ = _Be/* sbVx */;
    return new T(function(){
      var _Bg/* sbVX */ = function(_Bh/* sbVJ */){
        var _Bi/* sbVN */ = new T(function(){
          return B(A1(_Bd/* sbVv */,new T2(0,_7/* GHC.Tuple.() */,E(_Bh/* sbVJ */).b)));
        }),
        _Bj/* sbVP */ = function(_Bk/* sbVQ */){
          return E(_Bi/* sbVN */);
        };
        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Bf/* sbVz */, function(_Bl/* sbVR */){
          return new T1(0,B(_9p/* Haste.Concurrent.$wa */(_cp/* Core.World.Internal.switch2 */, _Bj/* sbVP */)));
        })));
      },
      _Bm/* sbVI */ = function(_Bn/* sbVB */, _Bo/* sbVC */){
        return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Bf/* sbVz */, _7/* GHC.Tuple.() */, function(_Bp/* sbVD */){
          return new F(function(){return A1(_Bo/* sbVC */,new T2(0,_Bp/* sbVD */,_Bn/* sbVB */));});
        })));
      };
      return B(A3(_Bb/* sbVt */,_Bm/* sbVI */, _Bc/* sbVu */, _Bg/* sbVX */));
    });
  };
},
_Bq/* a */ = 100,
_Br/* a4 */ = function(_Bs/* sNuv */, _Bt/* sNuw */){
  var _Bu/* sNuC */ = B(A1(_Bs/* sNuv */,new T(function(){
    return 1-(1-E(_Bt/* sNuw */));
  })));
  return 1-(1-_Bu/* sNuC */*_Bu/* sNuC */);
},
_Bv/* dur */ = 20,
_Bw/* e */ = function(_Bx/* sNul */, _By/* sNum */){
  var _Bz/* sNur */ = B(A1(_Bx/* sNul */,new T(function(){
    return 1-E(_By/* sNum */);
  })));
  return 1-_Bz/* sNur */*_Bz/* sNur */;
},
_BA/* lvl */ = 50,
_BB/* lvl1 */ = 3,
_BC/* lvl10 */ = function(_BD/* sNuH */){
  return  -E(_BD/* sNuH */);
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
_BY/* sleep1 */ = function(_BZ/* sc1a */, _C0/* sc1b */, _C1/* sc1c */){
  var _C2/* sc32 */ = function(_C3/* sc1d */){
    var _C4/* sc1e */ = E(_C3/* sc1d */),
    _C5/* sc1g */ = _C4/* sc1e */.b,
    _C6/* sc1h */ = new T(function(){
      return E(_C4/* sc1e */.a)+E(_BZ/* sc1a */)|0;
    }),
    _C7/* sc31 */ = function(_/* EXTERNAL */){
      var _C8/* sc1o */ = nMV/* EXTERNAL */(_B9/* Core.World.Internal.waitUntil2 */),
      _C9/* sc1q */ = _C8/* sc1o */;
      return new T(function(){
        var _Ca/* sc2Z */ = function(_Cb/* sc2P */){
          var _Cc/* sc2T */ = new T(function(){
            return B(A1(_C1/* sc1c */,new T2(0,_7/* GHC.Tuple.() */,E(_Cb/* sc2P */).b)));
          });
          return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_C9/* sc1q */, function(_Cd/* sc2V */){
            return E(_Cc/* sc2T */);
          })));
        },
        _Ce/* sc1s */ = new T2(0,_C6/* sc1h */,_C9/* sc1q */),
        _Cf/* sc2O */ = function(_Cg/* sc1u */){
          var _Ch/* sc1v */ = new T(function(){
            var _Ci/* sc1w */ = E(_Cg/* sc1u */),
            _Cj/* sc1B */ = E(_Ci/* sc1w */.c);
            if(!_Cj/* sc1B */._){
              var _Ck/* sc1B#result */ = E(new T3(1,1,_Ce/* sc1s */,E(_ax/* Data.PQueue.Internals.Nil */)));
            }else{
              var _Cl/* sc1C */ = _Cj/* sc1B */.a,
              _Cm/* sc1E */ = _Cj/* sc1B */.c,
              _Cn/* sc1F */ = E(_Cj/* sc1B */.b),
              _Co/* sc1I */ = E(_C6/* sc1h */),
              _Cp/* sc1K */ = E(_Cn/* sc1F */.a);
              if(_Co/* sc1I */>=_Cp/* sc1K */){
                if(_Co/* sc1I */!=_Cp/* sc1K */){
                  var _Cq/* sc1P#result */ = new T3(1,_Cl/* sc1C */+1|0,_Cn/* sc1F */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_Cr/* sc1Q */, _Cs/* sc1R */){
                    var _Ct/* sc1Y */ = E(E(_Cr/* sc1Q */).a),
                    _Cu/* sc20 */ = E(E(_Cs/* sc1R */).a);
                    return (_Ct/* sc1Y */>=_Cu/* sc20 */) ? _Ct/* sc1Y */==_Cu/* sc20 */ : true;
                  }, _Ce/* sc1s */, _BX/* Data.PQueue.Internals.Zero */, _Cm/* sc1E */))));
                }else{
                  var _Cq/* sc1P#result */ = new T3(1,_Cl/* sc1C */+1|0,_Ce/* sc1s */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_Cv/* sc28 */, _Cw/* sc29 */){
                    var _Cx/* sc2g */ = E(E(_Cv/* sc28 */).a),
                    _Cy/* sc2i */ = E(E(_Cw/* sc29 */).a);
                    return (_Cx/* sc2g */>=_Cy/* sc2i */) ? _Cx/* sc2g */==_Cy/* sc2i */ : true;
                  }, _Cn/* sc1F */, _BX/* Data.PQueue.Internals.Zero */, _Cm/* sc1E */))));
                }
                var _Cz/* sc1N#result */ = _Cq/* sc1P#result */;
              }else{
                var _Cz/* sc1N#result */ = new T3(1,_Cl/* sc1C */+1|0,_Ce/* sc1s */,E(B(_ay/* Data.PQueue.Internals.$wincr */(function(_CA/* sc2q */, _CB/* sc2r */){
                  var _CC/* sc2y */ = E(E(_CA/* sc2q */).a),
                  _CD/* sc2A */ = E(E(_CB/* sc2r */).a);
                  return (_CC/* sc2y */>=_CD/* sc2A */) ? _CC/* sc2y */==_CD/* sc2A */ : true;
                }, _Cn/* sc1F */, _BX/* Data.PQueue.Internals.Zero */, _Cm/* sc1E */))));
              }
              var _Ck/* sc1B#result */ = _Cz/* sc1N#result */;
            }
            return new T4(0,E(_Ci/* sc1w */.a),_Ci/* sc1w */.b,E(_Ck/* sc1B#result */),E(_Ci/* sc1w */.d));
          });
          return function(_CE/* sc2K */, _CF/* sc2L */){
            return new F(function(){return A1(_CF/* sc2L */,new T2(0,new T2(0,_7/* GHC.Tuple.() */,_Ch/* sc1v */),_CE/* sc2K */));});
          };
        };
        return B(A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _C5/* sc1g */, _Cf/* sc2O */, _C5/* sc1g */, _Ca/* sc2Z */]));
      });
    };
    return new T1(0,_C7/* sc31 */);
  };
  return new F(function(){return A(_9I/* Core.Util.$wwithMVar */,[_8l/* Core.World.Internal.$fMonadConcWorld */, _C0/* sc1b */, _ar/* Core.World.Internal.a */, _C0/* sc1b */, _C2/* sc32 */]);});
},
_CG/* $wa */ = function(_CH/* sNuL */, _CI/* sNuM */, _CJ/* sNuN */){
  return function(_/* EXTERNAL */){
    var _CK/* sNuP */ = nMV/* EXTERNAL */(_BK/* Motion.Bounce.lvl16 */),
    _CL/* sNuR */ = _CK/* sNuP */,
    _CM/* sNuT */ = function(_CN/* sNuU */){
      return new F(function(){return _iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Bv/* Motion.Bounce.dur */, _Br/* Motion.Bounce.a4 */, _CL/* sNuR */, _Bq/* Motion.Bounce.a */, function(_CO/* sNuV */){
        return E(_CN/* sNuU */);
      });});
    },
    _CP/* sNuX */ = function(_CQ/* sNuY */){
      return new F(function(){return _iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Bv/* Motion.Bounce.dur */, _Bw/* Motion.Bounce.e */, _CL/* sNuR */, _BM/* Motion.Bounce.lvl3 */, function(_CR/* sNuZ */){
        return E(_CQ/* sNuY */);
      });});
    },
    _CS/* sNCB */ = function(_/* EXTERNAL */){
      var _CT/* sNv2 */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
      _CU/* sNv4 */ = _CT/* sNv2 */,
      _CV/* sNv6 */ = new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_CU/* sNv4 */),
      _CW/* sNCz */ = function(_/* EXTERNAL */){
        var _CX/* sNv8 */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
        _CY/* sNva */ = _CX/* sNv8 */,
        _CZ/* sNCx */ = function(_/* EXTERNAL */){
          var _D0/* sNvd */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
          _D1/* sNvf */ = _D0/* sNvd */,
          _D2/* sNvh */ = new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_D1/* sNvf */),
          _D3/* sNCv */ = function(_/* EXTERNAL */){
            var _D4/* sNvj */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
            _D5/* sNvl */ = _D4/* sNvj */,
            _D6/* sNCt */ = function(_/* EXTERNAL */){
              var _D7/* sNvo */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
              _D8/* sNvq */ = _D7/* sNvo */,
              _D9/* sNCr */ = function(_/* EXTERNAL */){
                var _Da/* sNvt */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                _Db/* sNvv */ = _Da/* sNvt */,
                _Dc/* sNCp */ = function(_/* EXTERNAL */){
                  var _Dd/* sNvy */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                  _De/* sNvA */ = _Dd/* sNvy */,
                  _Df/* sNvC */ = new T(function(){
                    return B(_wJ/* Core.Ease.$wforceTo */(_De/* sNvA */, _BL/* Motion.Bounce.lvl2 */));
                  }),
                  _Dg/* sNCn */ = function(_/* EXTERNAL */){
                    var _Dh/* sNvE */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                    _Di/* sNvG */ = _Dh/* sNvE */,
                    _Dj/* sNCl */ = function(_/* EXTERNAL */){
                      var _Dk/* sNvJ */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                      _Dl/* sNvL */ = _Dk/* sNvJ */,
                      _Dm/* sNvN */ = new T(function(){
                        return B(_wJ/* Core.Ease.$wforceTo */(_Dl/* sNvL */, _BB/* Motion.Bounce.lvl1 */));
                      }),
                      _Dn/* sNCj */ = function(_/* EXTERNAL */){
                        var _Do/* sNvP */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                        _Dp/* sNvR */ = _Do/* sNvP */,
                        _Dq/* sNvT */ = new T(function(){
                          return B(_wJ/* Core.Ease.$wforceTo */(_Dp/* sNvR */, _BB/* Motion.Bounce.lvl1 */));
                        }),
                        _Dr/* sNCh */ = function(_/* EXTERNAL */){
                          var _Ds/* sNvV */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                          _Dt/* sNvX */ = _Ds/* sNvV */,
                          _Du/* sNCf */ = function(_/* EXTERNAL */){
                            var _Dv/* sNw0 */ = nMV/* EXTERNAL */(_BH/* Motion.Bounce.lvl13 */),
                            _Dw/* sNw2 */ = _Dv/* sNw0 */;
                            return new T(function(){
                              var _Dx/* sNw5 */ = function(_Dy/* sNwa */){
                                return new F(function(){return _Dz/* sNw7 */(E(_Dy/* sNwa */).b);});
                              },
                              _DA/* sNw6 */ = function(_DB/* sNwe */){
                                return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_BO/* Motion.Bounce.lvl5 */, E(_DB/* sNwe */).b, _Dx/* sNw5 */);});
                              },
                              _Dz/* sNw7 */ = function(_DC/* sNwi */){
                                var _DD/* sNAX */ = function(_DE/* sNwj */){
                                  var _DF/* sNwk */ = new T(function(){
                                    var _DG/* sNAQ */ = function(_DH/* sNwl */){
                                      var _DI/* sNwm */ = new T(function(){
                                        var _DJ/* sNAJ */ = function(_DK/* sNwn */){
                                          var _DL/* sNwo */ = new T(function(){
                                            var _DM/* sNAC */ = function(_DN/* sNwp */){
                                              var _DO/* sNwq */ = new T(function(){
                                                var _DP/* sNAv */ = function(_DQ/* sNwr */){
                                                  var _DR/* sNws */ = new T(function(){
                                                    var _DS/* sNwt */ = new T(function(){
                                                      return E(E(_DQ/* sNwr */).a);
                                                    }),
                                                    _DT/* sNwx */ = new T(function(){
                                                      return B(_wJ/* Core.Ease.$wforceTo */(_CU/* sNv4 */, new T(function(){
                                                        return (E(E(_DE/* sNwj */).a)+E(_DS/* sNwt */))*0.7;
                                                      })));
                                                    }),
                                                    _DU/* sNAo */ = function(_DV/* sNwI */){
                                                      var _DW/* sNwJ */ = new T(function(){
                                                        var _DX/* sNwK */ = new T(function(){
                                                          return E(E(_DV/* sNwI */).a);
                                                        }),
                                                        _DY/* sNwO */ = new T(function(){
                                                          return B(_wJ/* Core.Ease.$wforceTo */(_CY/* sNva */, new T(function(){
                                                            return (E(E(_DH/* sNwl */).a)+E(_DX/* sNwK */))*0.7;
                                                          })));
                                                        }),
                                                        _DZ/* sNAh */ = function(_E0/* sNwZ */){
                                                          var _E1/* sNx0 */ = new T(function(){
                                                            var _E2/* sNx1 */ = new T(function(){
                                                              return E(E(_E0/* sNwZ */).a);
                                                            }),
                                                            _E3/* sNx5 */ = new T(function(){
                                                              return B(_wJ/* Core.Ease.$wforceTo */(_D1/* sNvf */, new T(function(){
                                                                return (E(E(_DK/* sNwn */).a)+E(_E2/* sNx1 */))*0.7;
                                                              })));
                                                            }),
                                                            _E4/* sNAa */ = function(_E5/* sNxg */){
                                                              var _E6/* sNxh */ = new T(function(){
                                                                var _E7/* sNxi */ = new T(function(){
                                                                  return E(E(_E5/* sNxg */).a);
                                                                }),
                                                                _E8/* sNxm */ = new T(function(){
                                                                  return B(_wJ/* Core.Ease.$wforceTo */(_D5/* sNvl */, new T(function(){
                                                                    return (E(E(_DN/* sNwp */).a)+E(_E7/* sNxi */))*0.7;
                                                                  })));
                                                                }),
                                                                _E9/* sNxx */ = function(_Ea/* sNxy */){
                                                                  return new F(function(){return A2(_E8/* sNxm */,E(_Ea/* sNxy */).b, _DA/* sNw6 */);});
                                                                },
                                                                _Eb/* sNxC */ = function(_Ec/* sNxD */){
                                                                  return new F(function(){return A2(_E3/* sNx5 */,E(_Ec/* sNxD */).b, _E9/* sNxx */);});
                                                                },
                                                                _Ed/* sNxH */ = function(_Ee/* sNxI */){
                                                                  return new F(function(){return A2(_DY/* sNwO */,E(_Ee/* sNxI */).b, _Eb/* sNxC */);});
                                                                },
                                                                _Ef/* sNxM */ = function(_Eg/* sNxN */){
                                                                  return new F(function(){return A2(_DT/* sNwx */,E(_Eg/* sNxN */).b, _Ed/* sNxH */);});
                                                                },
                                                                _Eh/* sNA3 */ = function(_Ei/* sNxR */){
                                                                  var _Ej/* sNxS */ = new T(function(){
                                                                    var _Ek/* sNxT */ = new T(function(){
                                                                      return E(E(_Ei/* sNxR */).a);
                                                                    }),
                                                                    _El/* sNxX */ = new T(function(){
                                                                      return B(_wJ/* Core.Ease.$wforceTo */(_Dl/* sNvL */, new T(function(){
                                                                        return E(_Ek/* sNxT */)*0.7;
                                                                      })));
                                                                    }),
                                                                    _Em/* sNy2 */ = new T(function(){
                                                                      return B(_wJ/* Core.Ease.$wforceTo */(_D8/* sNvq */, new T(function(){
                                                                        return (E(_DS/* sNwt */)+E(_Ek/* sNxT */))*0.7;
                                                                      })));
                                                                    }),
                                                                    _En/* sNzW */ = function(_Eo/* sNya */){
                                                                      var _Ep/* sNyb */ = new T(function(){
                                                                        var _Eq/* sNyc */ = new T(function(){
                                                                          return E(E(_Eo/* sNya */).a);
                                                                        }),
                                                                        _Er/* sNyg */ = new T(function(){
                                                                          return B(_wJ/* Core.Ease.$wforceTo */(_Dp/* sNvR */, new T(function(){
                                                                            return E(_Eq/* sNyc */)*0.7;
                                                                          })));
                                                                        }),
                                                                        _Es/* sNyl */ = new T(function(){
                                                                          return B(_wJ/* Core.Ease.$wforceTo */(_Db/* sNvv */, new T(function(){
                                                                            return (E(_DX/* sNwK */)+E(_Eq/* sNyc */))*0.7;
                                                                          })));
                                                                        }),
                                                                        _Et/* sNzP */ = function(_Eu/* sNyt */){
                                                                          var _Ev/* sNyu */ = new T(function(){
                                                                            var _Ew/* sNyv */ = new T(function(){
                                                                              return E(E(_Eu/* sNyt */).a);
                                                                            }),
                                                                            _Ex/* sNyz */ = new T(function(){
                                                                              return B(_wJ/* Core.Ease.$wforceTo */(_Dt/* sNvX */, new T(function(){
                                                                                return E(_Ew/* sNyv */)*0.7;
                                                                              })));
                                                                            }),
                                                                            _Ey/* sNyE */ = new T(function(){
                                                                              return B(_wJ/* Core.Ease.$wforceTo */(_De/* sNvA */, new T(function(){
                                                                                return (E(_E2/* sNx1 */)+E(_Ew/* sNyv */))*0.7;
                                                                              })));
                                                                            }),
                                                                            _Ez/* sNzI */ = function(_EA/* sNyM */){
                                                                              var _EB/* sNyN */ = new T(function(){
                                                                                var _EC/* sNyO */ = new T(function(){
                                                                                  return E(E(_EA/* sNyM */).a);
                                                                                }),
                                                                                _ED/* sNyS */ = new T(function(){
                                                                                  return B(_wJ/* Core.Ease.$wforceTo */(_Dw/* sNw2 */, new T(function(){
                                                                                    return E(_EC/* sNyO */)*0.7;
                                                                                  })));
                                                                                }),
                                                                                _EE/* sNyX */ = new T(function(){
                                                                                  return B(_wJ/* Core.Ease.$wforceTo */(_Di/* sNvG */, new T(function(){
                                                                                    return (E(_E7/* sNxi */)+E(_EC/* sNyO */))*0.7;
                                                                                  })));
                                                                                }),
                                                                                _EF/* sNz5 */ = function(_EG/* sNz6 */){
                                                                                  return new F(function(){return A2(_EE/* sNyX */,E(_EG/* sNz6 */).b, _Ef/* sNxM */);});
                                                                                },
                                                                                _EH/* sNza */ = function(_EI/* sNzb */){
                                                                                  return new F(function(){return A2(_Ey/* sNyE */,E(_EI/* sNzb */).b, _EF/* sNz5 */);});
                                                                                },
                                                                                _EJ/* sNzf */ = function(_EK/* sNzg */){
                                                                                  return new F(function(){return A2(_Es/* sNyl */,E(_EK/* sNzg */).b, _EH/* sNza */);});
                                                                                },
                                                                                _EL/* sNzk */ = function(_EM/* sNzl */){
                                                                                  return new F(function(){return A2(_Em/* sNy2 */,E(_EM/* sNzl */).b, _EJ/* sNzf */);});
                                                                                },
                                                                                _EN/* sNzp */ = function(_EO/* sNzq */){
                                                                                  return new F(function(){return A2(_ED/* sNyS */,E(_EO/* sNzq */).b, _EL/* sNzk */);});
                                                                                },
                                                                                _EP/* sNzu */ = function(_EQ/* sNzv */){
                                                                                  return new F(function(){return A2(_Ex/* sNyz */,E(_EQ/* sNzv */).b, _EN/* sNzp */);});
                                                                                };
                                                                                return B(A2(_El/* sNxX */,_DC/* sNwi */, function(_ER/* sNzz */){
                                                                                  return new F(function(){return A2(_Er/* sNyg */,E(_ER/* sNzz */).b, _EP/* sNzu */);});
                                                                                }));
                                                                              });
                                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Dw/* sNw2 */, _EA/* sNyM */, function(_ES/* sNzE */){
                                                                                return E(_EB/* sNyN */);
                                                                              })));
                                                                            };
                                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Dw/* sNw2 */, _Ez/* sNzI */)));
                                                                          });
                                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Dt/* sNvX */, _Eu/* sNyt */, function(_ET/* sNzL */){
                                                                            return E(_Ev/* sNyu */);
                                                                          })));
                                                                        };
                                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Dt/* sNvX */, _Et/* sNzP */)));
                                                                      });
                                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Dp/* sNvR */, _Eo/* sNya */, function(_EU/* sNzS */){
                                                                        return E(_Ep/* sNyb */);
                                                                      })));
                                                                    };
                                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Dp/* sNvR */, _En/* sNzW */)));
                                                                  });
                                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Dl/* sNvL */, _Ei/* sNxR */, function(_EV/* sNzZ */){
                                                                    return E(_Ej/* sNxS */);
                                                                  })));
                                                                };
                                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Dl/* sNvL */, _Eh/* sNA3 */)));
                                                              });
                                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Di/* sNvG */, _E5/* sNxg */, function(_EW/* sNA6 */){
                                                                return E(_E6/* sNxh */);
                                                              })));
                                                            };
                                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Di/* sNvG */, _E4/* sNAa */)));
                                                          });
                                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_De/* sNvA */, _E0/* sNwZ */, function(_EX/* sNAd */){
                                                            return E(_E1/* sNx0 */);
                                                          })));
                                                        };
                                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_De/* sNvA */, _DZ/* sNAh */)));
                                                      });
                                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_Db/* sNvv */, _DV/* sNwI */, function(_EY/* sNAk */){
                                                        return E(_DW/* sNwJ */);
                                                      })));
                                                    };
                                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_Db/* sNvv */, _DU/* sNAo */)));
                                                  });
                                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_D8/* sNvq */, _DQ/* sNwr */, function(_EZ/* sNAr */){
                                                    return E(_DR/* sNws */);
                                                  })));
                                                };
                                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_D8/* sNvq */, _DP/* sNAv */)));
                                              });
                                              return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_D5/* sNvl */, _DN/* sNwp */, function(_F0/* sNAy */){
                                                return E(_DO/* sNwq */);
                                              })));
                                            };
                                            return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_D5/* sNvl */, _DM/* sNAC */)));
                                          });
                                          return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_D1/* sNvf */, _DK/* sNwn */, function(_F1/* sNAF */){
                                            return E(_DL/* sNwo */);
                                          })));
                                        };
                                        return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_D1/* sNvf */, _DJ/* sNAJ */)));
                                      });
                                      return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_CY/* sNva */, _DH/* sNwl */, function(_F2/* sNAM */){
                                        return E(_DI/* sNwm */);
                                      })));
                                    };
                                    return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_CY/* sNva */, _DG/* sNAQ */)));
                                  });
                                  return new T1(0,B(_2K/* Haste.Concurrent.Monad.$wa1 */(_CU/* sNv4 */, _DE/* sNwj */, function(_F3/* sNAT */){
                                    return E(_DF/* sNwk */);
                                  })));
                                };
                                return new T1(0,B(_8B/* Haste.Concurrent.Monad.$wa2 */(_CU/* sNv4 */, _DD/* sNAX */)));
                              },
                              _F4/* sNB0 */ = new T(function(){
                                return B(_wJ/* Core.Ease.$wforceTo */(_Dw/* sNw2 */, _BN/* Motion.Bounce.lvl4 */));
                              }),
                              _F5/* sNB2 */ = function(_F6/* sNBc */){
                                return new F(function(){return _F7/* sNB9 */(E(_F6/* sNBc */).b);});
                              },
                              _F8/* sNB3 */ = function(_F9/* sNBg */){
                                return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_BA/* Motion.Bounce.lvl */, E(_F9/* sNBg */).b, _F5/* sNB2 */);});
                              },
                              _Fa/* sNB4 */ = function(_Fb/* sNBk */){
                                return new F(function(){return A2(_Dq/* sNvT */,E(_Fb/* sNBk */).b, _F8/* sNB3 */);});
                              },
                              _Fc/* sNB5 */ = function(_Fd/* sNBo */){
                                return new F(function(){return A2(_Dm/* sNvN */,E(_Fd/* sNBo */).b, _Fa/* sNB4 */);});
                              },
                              _Fe/* sNB6 */ = function(_Ff/* sNBs */){
                                return new F(function(){return A2(_Df/* sNvC */,E(_Ff/* sNBs */).b, _Fc/* sNB5 */);});
                              },
                              _Fg/* sNB7 */ = function(_Fh/* sNBw */){
                                return new T1(0,B(_Ba/* Core.World.Internal.$wa6 */(_CM/* sNuT */, E(_Fh/* sNBw */).b, _Fe/* sNB6 */)));
                              },
                              _Fi/* sNB8 */ = function(_Fj/* sNBC */){
                                return new T1(0,B(_Ba/* Core.World.Internal.$wa6 */(_CP/* sNuX */, E(_Fj/* sNBC */).b, _Fg/* sNB7 */)));
                              },
                              _F7/* sNB9 */ = function(_Fk/* sNBI */){
                                return new F(function(){return A2(_F4/* sNB0 */,_Fk/* sNBI */, _Fi/* sNB8 */);});
                              },
                              _Fl/* sNCb */ = function(_Fm/* sNC5 */, _Fn/* sNC6 */){
                                return new T1(1,new T2(1,new T(function(){
                                  return B(_F7/* sNB9 */(_Fm/* sNC5 */));
                                }),new T2(1,new T(function(){
                                  return B(_Dz/* sNw7 */(_Fm/* sNC5 */));
                                }),_6/* GHC.Types.[] */)));
                              },
                              _Fo/* sNC4 */ = new T(function(){
                                var _Fp/* sNC3 */ = new T(function(){
                                  var _Fq/* sNBZ */ = B(_rM/* Core.Shape.Internal.$wrect */(new T(function(){
                                    return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, _BT/* Motion.Bounce.lvl8 */, new T2(2,_CV/* sNv6 */,_BC/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, new T2(2,new T3(0,_Bv/* Motion.Bounce.dur */,_Bw/* Motion.Bounce.e */,_CL/* sNuR */),_2E/* GHC.Base.id */), new T2(2,_D2/* sNvh */,_BC/* Motion.Bounce.lvl10 */)));
                                  }), new T(function(){
                                    return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, _BR/* Motion.Bounce.lvl7 */, new T2(2,_CV/* sNv6 */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_CY/* sNva */),_2E/* GHC.Base.id */)));
                                  }), new T(function(){
                                    return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, _BP/* Motion.Bounce.lvl6 */, new T2(2,_D2/* sNvh */,_2E/* GHC.Base.id */))), new T2(2,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_D5/* sNvl */),_2E/* GHC.Base.id */)));
                                  })));
                                  return new T3(0,_Fq/* sNBZ */.a,_Fq/* sNBZ */.b,_Fq/* sNBZ */.c);
                                });
                                return B(_ro/* Core.Render.Internal.fill1 */(_CH/* sNuL */, _Fp/* sNC3 */));
                              });
                              return B(A1(_CJ/* sNuN */,new T2(0,new T2(0,_Fo/* sNC4 */,_Fl/* sNCb */),_CI/* sNuM */)));
                            });
                          };
                          return new T1(0,_Du/* sNCf */);
                        };
                        return new T1(0,_Dr/* sNCh */);
                      };
                      return new T1(0,_Dn/* sNCj */);
                    };
                    return new T1(0,_Dj/* sNCl */);
                  };
                  return new T1(0,_Dg/* sNCn */);
                };
                return new T1(0,_Dc/* sNCp */);
              };
              return new T1(0,_D9/* sNCr */);
            };
            return new T1(0,_D6/* sNCt */);
          };
          return new T1(0,_D3/* sNCv */);
        };
        return new T1(0,_CZ/* sNCx */);
      };
      return new T1(0,_CW/* sNCz */);
    };
    return new T1(0,_CS/* sNCB */);
  };
},
_Fr/* bounceMot1 */ = function(_Fs/* sNCE */, _Ft/* sNCF */, _Fu/* sNCG */){
  return new T1(0,B(_CG/* Motion.Bounce.$wa */(_Fs/* sNCE */, _Ft/* sNCF */, _Fu/* sNCG */)));
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
_FC/* $fAffineRender1 */ = function(_FD/* sFdS */, _FE/* sFdT */, _FF/* sFdU */, _FG/* sFdV */){
  var _FH/* sFeZ */ = new T(function(){
    var _FI/* sFeX */ = new T(function(){
      var _FJ/* sFeU */ = new T(function(){
        var _FK/* sFer */ = E(_FF/* sFdU */);
        switch(_FK/* sFer */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_FK/* sFer */.a);
            }));
            break;
          case 1:
            var _FL/* sFeD */ = function(_/* EXTERNAL */){
              var _FM/* sFez */ = B(A1(_FK/* sFer */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_FA/* GHC.Float.negateDouble */(_FM/* sFez */));
              });
            };
            return new T1(1,_FL/* sFeD */);
            break;
          case 2:
            return new T2(2,_FK/* sFer */.a,function(_FN/* sFeG */){
              return  -B(A1(_FK/* sFer */.b,_FN/* sFeG */));
            });
            break;
          default:
            var _FO/* sFeT */ = function(_FP/* sFeN */, _/* EXTERNAL */){
              var _FQ/* sFeP */ = B(A2(_FK/* sFer */.b,_FP/* sFeN */, _/* EXTERNAL */));
              return new T(function(){
                return B(_FA/* GHC.Float.negateDouble */(_FQ/* sFeP */));
              });
            };
            return new T2(3,_FK/* sFer */.a,_FO/* sFeT */);
        }
      }),
      _FR/* sFeq */ = new T(function(){
        var _FS/* sFdX */ = E(_FE/* sFdT */);
        switch(_FS/* sFdX */._){
          case 0:
            return new T1(0,new T(function(){
              return  -E(_FS/* sFdX */.a);
            }));
            break;
          case 1:
            var _FT/* sFe9 */ = function(_/* EXTERNAL */){
              var _FU/* sFe5 */ = B(A1(_FS/* sFdX */.a,_/* EXTERNAL */));
              return new T(function(){
                return B(_FA/* GHC.Float.negateDouble */(_FU/* sFe5 */));
              });
            };
            return new T1(1,_FT/* sFe9 */);
            break;
          case 2:
            return new T2(2,_FS/* sFdX */.a,function(_FV/* sFec */){
              return  -B(A1(_FS/* sFdX */.b,_FV/* sFec */));
            });
            break;
          default:
            var _FW/* sFep */ = function(_FX/* sFej */, _/* EXTERNAL */){
              var _FY/* sFel */ = B(A2(_FS/* sFdX */.b,_FX/* sFej */, _/* EXTERNAL */));
              return new T(function(){
                return B(_FA/* GHC.Float.negateDouble */(_FY/* sFel */));
              });
            };
            return new T2(3,_FS/* sFdX */.a,_FW/* sFep */);
        }
      });
      return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_FR/* sFeq */,_FJ/* sFeU */),_FG/* sFdV */,_7/* GHC.Tuple.() */)));
    });
    return B(_pg/* Control.Monad.Skeleton.bone */(new T3(7,_FD/* sFdS */,_FI/* sFeX */,_7/* GHC.Tuple.() */)));
  });
  return new F(function(){return _pg/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_FE/* sFdT */,_FF/* sFdU */),_FH/* sFeZ */,_7/* GHC.Tuple.() */));});
},
_FZ/* lvl */ = 0,
_G0/* lvl1 */ = 20,
_G1/* lvl2 */ = 0.9999999999999998,
_G2/* lvl3 */ = new T4(0,_FZ/* Motion.Grow.lvl */,_FZ/* Motion.Grow.lvl */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_G3/* lvl4 */ = new T2(0,_FZ/* Motion.Grow.lvl */,_G2/* Motion.Grow.lvl3 */),
_G4/* lvl5 */ = new T2(0,_G3/* Motion.Grow.lvl4 */,_6/* GHC.Types.[] */),
_G5/* $wa1 */ = function(_G6/* sOXb */, _G7/* sOXc */, _G8/* sOXd */){
  return function(_/* EXTERNAL */){
    var _G9/* sOXf */ = nMV/* EXTERNAL */(_G4/* Motion.Grow.lvl5 */);
    return new T(function(){
      var _Ga/* sOXi */ = function(_Gb/* sOXj */, _Gc/* sOXk */){
        return 1-B(A1(_Gb/* sOXj */,new T(function(){
          var _Gd/* sOXn */ = E(_Gc/* sOXk */)/0.3-_G6/* sOXb *//4*2.3333333333333335;
          if(1>_Gd/* sOXn */){
            if(0>_Gd/* sOXn */){
              return E(_G1/* Motion.Grow.lvl2 */);
            }else{
              var _Ge/* sOXw */ = 1-_Gd/* sOXn */;
              return _Ge/* sOXw */*_Ge/* sOXw */*(2.70158*_Ge/* sOXw */-1.70158);
            }
          }else{
            return E(_FZ/* Motion.Grow.lvl */);
          }
        })));
      },
      _Gf/* sOXJ */ = new T3(0,_G0/* Motion.Grow.lvl1 */,function(_Gg/* sOXF */, _Gh/* sOXG */){
        return new F(function(){return _Ga/* sOXi */(_Gg/* sOXF */, _Gh/* sOXG */);});
      },_G9/* sOXf */),
      _Gi/* sOXK */ = E(_G6/* sOXb */);
      if(_Gi/* sOXK */==4){
        return B(A1(_G8/* sOXd */,new T2(0,new T2(1,_Gf/* sOXJ */,_6/* GHC.Types.[] */),_G7/* sOXc */)));
      }else{
        return new T1(0,B(_G5/* Motion.Grow.$wa1 */(_Gi/* sOXK */+1|0, _G7/* sOXc */, function(_Gj/* sOXM */){
          var _Gk/* sOXN */ = E(_Gj/* sOXM */);
          return new F(function(){return A1(_G8/* sOXd */,new T2(0,new T2(1,_Gf/* sOXJ */,_Gk/* sOXN */.a),_Gk/* sOXN */.b));});
        })));
      }
    });
  };
},
_Gl/* $wcenterRect */ = function(_Gm/* stCR */, _Gn/* stCS */, _Go/* stCT */, _Gp/* stCU */){
  var _Gq/* stF0 */ = function(_Gr/* stDN */, _Gs/* stDO */, _Gt/* stDP */, _/* EXTERNAL */){
    var _Gu/* stEZ */ = function(_Gv/* stDR */, _Gw/* stDS */, _Gx/* stDT */, _/* EXTERNAL */){
      var _Gy/* stEY */ = function(_Gz/* stDV */){
        var _GA/* stDW */ = new T(function(){
          return E(_Gz/* stDV */)/2;
        }),
        _GB/* stEX */ = function(_GC/* stE0 */, _GD/* stE1 */, _GE/* stE2 */, _/* EXTERNAL */){
          var _GF/* stE4 */ = E(_Gr/* stDN */),
          _GG/* stE6 */ = E(_GA/* stDW */),
          _GH/* stE8 */ = _GF/* stE4 */+_GG/* stE6 */,
          _GI/* stEe */ = _GF/* stE4 */-_GG/* stE6 */,
          _GJ/* stEh */ = E(_Gv/* stDR */),
          _GK/* stEl */ = E(_GC/* stE0 */)/2,
          _GL/* stEp */ = _GJ/* stEh */+_GK/* stEl */,
          _GM/* stEs */ = _GJ/* stEh */-_GK/* stEl */,
          _GN/* stEv */ = E(_GD/* stE1 */),
          _GO/* stEz */ = E(_GE/* stE2 */),
          _GP/* stEC */ = __app4/* EXTERNAL */(E(_rK/* Core.Shape.Internal.bezier_f2 */), _GI/* stEe */, _GM/* stEs */, _GN/* stEv */, _GO/* stEz */),
          _GQ/* stEF */ = E(_rL/* Core.Shape.Internal.line_f1 */),
          _GR/* stEI */ = __app4/* EXTERNAL */(_GQ/* stEF */, _GH/* stE8 */, _GJ/* stEh */-_GK/* stEl */, _GN/* stEv */, _GO/* stEz */),
          _GS/* stEM */ = __app4/* EXTERNAL */(_GQ/* stEF */, _GH/* stE8 */, _GL/* stEp */, _GN/* stEv */, _GO/* stEz */),
          _GT/* stEQ */ = __app4/* EXTERNAL */(_GQ/* stEF */, _GF/* stE4 */-_GG/* stE6 */, _GL/* stEp */, _GN/* stEv */, _GO/* stEz */),
          _GU/* stEU */ = __app4/* EXTERNAL */(_GQ/* stEF */, _GI/* stEe */, _GM/* stEs */, _GN/* stEv */, _GO/* stEz */);
          return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
        };
        return function(_gd/* _fa_1 */, _ge/* _fa_2 */, _GV/* _fa_3 */){
          return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_Gp/* stCU */, _GB/* stEX */, _gd/* _fa_1 */, _ge/* _fa_2 */, _GV/* _fa_3 */);});
        };
      };
      return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_Go/* stCT */, _Gy/* stEY */, _Gw/* stDS */, _Gx/* stDT */, _/* EXTERNAL */);});
    };
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_Gn/* stCS */, _Gu/* stEZ */, _Gs/* stDO */, _Gt/* stDP */, _/* EXTERNAL */);});
  },
  _GW/* stDM */ = function(_GX/* stCV */, _/* EXTERNAL */){
    var _GY/* stCX */ = E(_GX/* stCV */),
    _GZ/* stDL */ = function(_H0/* stD0 */, _/* EXTERNAL */){
      var _H1/* stDK */ = function(_H2/* stD2 */, _/* EXTERNAL */){
        var _H3/* stDJ */ = function(_H4/* stD4 */, _/* EXTERNAL */){
          var _H5/* stDI */ = function(_H6/* stD6 */, _/* EXTERNAL */){
            return new T(function(){
              var _H7/* stDc */ = function(_H8/* stDd */){
                if(_H8/* stDd */>=E(_H4/* stD4 */)/2){
                  return false;
                }else{
                  var _H9/* stDn */ = E(_GY/* stCX */.b)-E(_H2/* stD2 */);
                  return (_H9/* stDn */==0) ? 0<E(_H6/* stD6 */)/2 : (_H9/* stDn */<=0) ?  -_H9/* stDn */<E(_H6/* stD6 */)/2 : _H9/* stDn */<E(_H6/* stD6 */)/2;
                }
              },
              _Ha/* stDD */ = E(_GY/* stCX */.a)-E(_H0/* stD0 */);
              if(!_Ha/* stDD */){
                return B(_H7/* stDc */(0));
              }else{
                if(_Ha/* stDD */<=0){
                  return B(_H7/* stDc */( -_Ha/* stDD */));
                }else{
                  return B(_H7/* stDc */(_Ha/* stDD */));
                }
              }
            });
          };
          return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_Gp/* stCU */, _H5/* stDI */, _/* EXTERNAL */);});
        };
        return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_Go/* stCT */, _H3/* stDJ */, _/* EXTERNAL */);});
      };
      return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_Gn/* stCS */, _H1/* stDK */, _/* EXTERNAL */);});
    };
    return new F(function(){return _rz/* Core.Shape.Internal.$fAffineShape3 */(_Gm/* stCR */, _GZ/* stDL */, _/* EXTERNAL */);});
  };
  return new T3(0,_GW/* stDM */,function(_rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */){
    return new F(function(){return _q9/* Core.Shape.Internal.$fAffineShape2 */(_Gm/* stCR */, _Gq/* stF0 */, _rg/* B3 */, _rh/* B2 */, _/* EXTERNAL */);});
  },_7/* GHC.Tuple.() */);
},
_Hb/* a3 */ = new T1(0,_/* EXTERNAL */),
_Hc/* a4 */ = new T1(0,_6/* GHC.Types.[] */),
_Hd/* a5 */ = new T2(0,E(_Hc/* Motion.Grow.a4 */),E(_Hb/* Motion.Grow.a3 */)),
_He/* a */ = function(_Hf/* sOX8 */, _Hg/* sOX9 */){
  return new F(function(){return A1(_Hg/* sOX9 */,new T2(0,_7/* GHC.Tuple.() */,_Hf/* sOX8 */));});
},
_Hh/* ds */ = 1,
_Hi/* go */ = function(_Hj/* sOXZ */){
  var _Hk/* sOY0 */ = E(_Hj/* sOXZ */);
  if(!_Hk/* sOY0 */._){
    return E(_He/* Motion.Grow.a */);
  }else{
    var _Hl/* sOY3 */ = new T(function(){
      var _Hm/* sOY4 */ = E(_Hk/* sOY0 */.a);
      return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Hm/* sOY4 */.a, _Hm/* sOY4 */.b, _Hm/* sOY4 */.c, _Hh/* Motion.Grow.ds */, _tT/* Core.Ease.easeTo1 */));
    }),
    _Hn/* sOY8 */ = new T(function(){
      return B(_Hi/* Motion.Grow.go */(_Hk/* sOY0 */.b));
    }),
    _Ho/* sOYi */ = function(_Hp/* sOY9 */){
      var _Hq/* sOYa */ = new T(function(){
        return B(A1(_Hl/* sOY3 */,_Hp/* sOY9 */));
      }),
      _Hr/* sOYh */ = function(_Hs/* sOYb */){
        return new F(function(){return A1(_Hq/* sOYa */,function(_Ht/* sOYc */){
          return new F(function(){return A2(_Hn/* sOY8 */,E(_Ht/* sOYc */).b, _Hs/* sOYb */);});
        });});
      };
      return E(_Hr/* sOYh */);
    };
    return E(_Ho/* sOYi */);
  }
},
_Hu/* go1 */ = function(_Hv/* sOYj */){
  var _Hw/* sOYk */ = E(_Hv/* sOYj */);
  if(!_Hw/* sOYk */._){
    return E(_He/* Motion.Grow.a */);
  }else{
    var _Hx/* sOYn */ = new T(function(){
      var _Hy/* sOYo */ = E(_Hw/* sOYk */.a),
      _Hz/* sOYD */ = function(_HA/* sOYs */){
        var _HB/* sOYt */ = new T(function(){
          return B(A1(_Hy/* sOYo */.b,_HA/* sOYs */));
        }),
        _HC/* sOYC */ = function(_HD/* sOYu */){
          return 1-B(A1(_HB/* sOYt */,new T(function(){
            return 1-E(_HD/* sOYu */);
          })));
        };
        return E(_HC/* sOYC */);
      };
      return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _Hy/* sOYo */.a, _Hz/* sOYD */, _Hy/* sOYo */.c, _FZ/* Motion.Grow.lvl */, _tT/* Core.Ease.easeTo1 */));
    }),
    _HE/* sOYE */ = new T(function(){
      return B(_Hu/* Motion.Grow.go1 */(_Hw/* sOYk */.b));
    }),
    _HF/* sOYO */ = function(_HG/* sOYF */){
      var _HH/* sOYG */ = new T(function(){
        return B(A1(_Hx/* sOYn */,_HG/* sOYF */));
      }),
      _HI/* sOYN */ = function(_HJ/* sOYH */){
        return new F(function(){return A1(_HH/* sOYG */,function(_HK/* sOYI */){
          return new F(function(){return A2(_HE/* sOYE */,E(_HK/* sOYI */).b, _HJ/* sOYH */);});
        });});
      };
      return E(_HI/* sOYN */);
    };
    return E(_HF/* sOYO */);
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
_HY/* morph */ = function(_HZ/* skYW */){
  return new T2(2,_HZ/* skYW */,_2E/* GHC.Base.id */);
},
_I0/* $wa */ = function(_I1/* sOYP */, _I2/* sOYQ */, _I3/* sOYR */){
  var _I4/* sOYS */ = function(_I5/* sOYT */, _I6/* sOYU */){
    var _I7/* sOYV */ = E(_I5/* sOYT */);
    if(!_I7/* sOYV */._){
      return E(_Hd/* Motion.Grow.a5 */);
    }else{
      var _I8/* sOYY */ = E(_I6/* sOYU */);
      if(!_I8/* sOYY */._){
        return E(_Hd/* Motion.Grow.a5 */);
      }else{
        var _I9/* sOYZ */ = _I8/* sOYY */.a,
        _Ia/* sOZ1 */ = new T(function(){
          return 4-E(_I7/* sOYV */.a);
        }),
        _Ib/* sOZk */ = new T(function(){
          var _Ic/* sOZj */ = new T(function(){
            var _Id/* sOZf */ = B(_Gl/* Core.Shape.Internal.$wcenterRect */(_HX/* Motion.Grow.lvl9 */, new T(function(){
              return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, B(_uj/* Core.Ease.opLift */(_vu/* GHC.Float.timesDouble */, new T1(0,_Ia/* sOZ1 */), _HS/* Motion.Grow.lvl10 */)), _HU/* Motion.Grow.lvl8 */));
            }), _HS/* Motion.Grow.lvl10 */, _HS/* Motion.Grow.lvl10 */));
            return new T3(0,_Id/* sOZf */.a,_Id/* sOZf */.b,_Id/* sOZf */.c);
          });
          return B(_ro/* Core.Render.Internal.fill1 */(_I1/* sOYP */, _Ic/* sOZj */));
        }),
        _Ie/* sOZl */ = B(_FC/* Core.Render.Internal.$fAffineRender1 */(new T2(0,new T(function(){
          return B(_HY/* Core.Ease.morph */(_I9/* sOYZ */));
        }),new T(function(){
          return B(_HY/* Core.Ease.morph */(_I9/* sOYZ */));
        })), _HX/* Motion.Grow.lvl9 */, new T(function(){
          return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, B(_uj/* Core.Ease.opLift */(_vu/* GHC.Float.timesDouble */, new T1(0,_Ia/* sOZ1 */), _HS/* Motion.Grow.lvl10 */)), _HS/* Motion.Grow.lvl10 */));
        }), _Ib/* sOZk */)),
        _If/* sOZo */ = new T(function(){
          return B(_I4/* sOYS */(_I7/* sOYV */.b, _I8/* sOYY */.b));
        }),
        _Ig/* sOZz */ = function(_Ih/* sOZp */){
          var _Ii/* sOZq */ = E(_If/* sOZo */);
          return new T2(0,E(_Ii/* sOZq */.a),E(new T2(2,_Ii/* sOZq */.b,new T1(1,function(_Ij/* sOZt */){
            return new T2(0,E(new T1(0,new T2(1,_Ih/* sOZp */,_Ij/* sOZt */))),E(_Hb/* Motion.Grow.a3 */));
          }))));
        };
        return new T2(0,E(_Ie/* sOZl */.a),E(new T2(2,_Ie/* sOZl */.b,new T1(1,_Ig/* sOZz */))));
      }
    }
  },
  _Ik/* sP0b */ = function(_Il/* sOZC */){
    var _Im/* sOZD */ = E(_Il/* sOZC */),
    _In/* sOZE */ = _Im/* sOZD */.a,
    _Io/* sOZG */ = new T(function(){
      return B(_Hu/* Motion.Grow.go1 */(_In/* sOZE */));
    }),
    _Ip/* sOZH */ = new T(function(){
      return B(_Hi/* Motion.Grow.go */(_In/* sOZE */));
    }),
    _Iq/* sOZI */ = function(_Ir/* sOZJ */){
      var _Is/* sOZK */ = new T(function(){
        return B(A1(_Ip/* sOZH */,_Ir/* sOZJ */));
      }),
      _It/* sP06 */ = function(_Iu/* sOZL */){
        var _Iv/* sOZM */ = function(_Iw/* sOZN */){
          return new F(function(){return A2(_Iq/* sOZI */,E(_Iw/* sOZN */).b, _Iu/* sOZL */);});
        },
        _Ix/* sOZR */ = function(_Iy/* sOZS */){
          return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_HT/* Motion.Grow.lvl11 */, E(_Iy/* sOZS */).b, _Iv/* sOZM */);});
        },
        _Iz/* sOZW */ = function(_IA/* sOZX */){
          return new F(function(){return A2(_Io/* sOZG */,E(_IA/* sOZX */).b, _Ix/* sOZR */);});
        };
        return new F(function(){return A1(_Is/* sOZK */,function(_IB/* sP01 */){
          return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_HT/* Motion.Grow.lvl11 */, E(_IB/* sP01 */).b, _Iz/* sOZW */);});
        });});
      };
      return E(_It/* sP06 */);
    },
    _IC/* sP08 */ = new T(function(){
      return B(_p8/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
        return B(_I4/* sOYS */(_HQ/* Core.Util.iforM1 */, _In/* sOZE */));
      })));
    });
    return new F(function(){return A1(_I3/* sOYR */,new T2(0,new T2(0,_IC/* sP08 */,_Iq/* sOZI */),_Im/* sOZD */.b));});
  };
  return new F(function(){return _G5/* Motion.Grow.$wa1 */(0, _I2/* sOYQ */, _Ik/* sP0b */);});
},
_ID/* growMot1 */ = function(_IE/* sP0c */, _IF/* sP0d */, _IG/* sP0e */){
  return new T1(0,B(_I0/* Motion.Grow.$wa */(_IE/* sP0c */, _IF/* sP0d */, _IG/* sP0e */)));
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
_IO/* speedMot1 */ = function(_IP/* sRjo */, _IQ/* sRjp */){
  return new F(function(){return A1(_IQ/* sRjp */,new T2(0,_7/* GHC.Tuple.() */,_IP/* sRjo */));});
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
_XY/* speedMot */ = function(_XZ/* sRjs */){
  var _Y0/* sRjt */ = new T(function(){
    var _Y1/* sRkl */ = new T(function(){
      var _Y2/* sRju */ = E(_XI/* Motion.Speed.speedMot15 */),
      _Y3/* sRjv */ = _Y2/* sRju */.a,
      _Y4/* sRjw */ = _Y2/* sRju */.b,
      _Y5/* sRki */ = function(_Y6/* sRjx */){
        var _Y7/* sRjy */ = new T(function(){
          var _Y8/* sRjB */ = Math.log/* EXTERNAL */(E(_Y6/* sRjx */));
          return Math.sqrt/* EXTERNAL */( -(_Y8/* sRjB */+_Y8/* sRjB */));
        }),
        _Y9/* sRkf */ = function(_Ya/* sRjF */){
          var _Yb/* sRjG */ = new T(function(){
            var _Yc/* sRjH */ = E(_Y7/* sRjy */),
            _Yd/* sRjJ */ = E(_Ya/* sRjF */);
            return _Yc/* sRjH */*Math.sin/* EXTERNAL */(6.283185307179586*_Yd/* sRjJ */)+_Yc/* sRjH */*Math.sin/* EXTERNAL */(6.283185307179586*_Yd/* sRjJ */);
          }),
          _Ye/* sRkc */ = function(_Yf/* sRjT */){
            var _Yg/* sRka */ = new T(function(){
              var _Yh/* sRk8 */ = new T(function(){
                var _Yi/* sRk6 */ = new T(function(){
                  var _Yj/* sRk5 */ = new T(function(){
                    var _Yk/* sRk0 */ = new T(function(){
                      return B(_uj/* Core.Ease.opLift */(_BU/* GHC.Float.plusDouble */, _XP/* Motion.Speed.speedMot4 */, new T1(0,new T(function(){
                        return 4/(1-E(_Yf/* sRjT */));
                      }))));
                    }),
                    _Yl/* sRk1 */ = B(_Gl/* Core.Shape.Internal.$wcenterRect */(new T1(0,_Yb/* sRjG */), _Yk/* sRk0 */, _XK/* Motion.Speed.speedMot2 */, _XK/* Motion.Speed.speedMot2 */));
                    return new T3(0,_Yl/* sRk1 */.a,_Yl/* sRk1 */.b,_Yl/* sRk1 */.c);
                  });
                  return B(_ro/* Core.Render.Internal.fill1 */(_XZ/* sRjs */, _Yj/* sRk5 */));
                });
                return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,_XS/* Motion.Speed.speedMot6 */,_Yi/* sRk6 */,_7/* GHC.Tuple.() */)));
              });
              return B(_pg/* Control.Monad.Skeleton.bone */(new T3(6,_XX/* Motion.Speed.speedMot9 */,_Yh/* sRk8 */,_7/* GHC.Tuple.() */)));
            });
            return new F(function(){return _pg/* Control.Monad.Skeleton.bone */(new T3(5,_IT/* Motion.Speed.speedMot12 */,_Yg/* sRka */,_7/* GHC.Tuple.() */));});
          };
          return new T2(0,E(_Y3/* sRjv */),E(new T2(2,_Y4/* sRjw */,new T1(1,_Ye/* sRkc */))));
        };
        return new T2(0,E(_Y3/* sRjv */),E(new T2(2,_Y4/* sRjw */,new T1(1,_Y9/* sRkf */))));
      };
      return new T2(0,E(_Y3/* sRjv */),E(new T2(2,_Y4/* sRjw */,new T1(1,_Y5/* sRki */))));
    });
    return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,_XN/* Motion.Speed.speedMot20 */,_Y1/* sRkl */,_7/* GHC.Tuple.() */)));
  });
  return function(_Ym/* sRko */, _Yn/* sRkp */){
    return new F(function(){return A1(_Yn/* sRkp */,new T2(0,new T2(0,_Y0/* sRjt */,_IO/* Motion.Speed.speedMot1 */),_Ym/* sRko */));});
  };
},
_Yo/* lvl36 */ = new T(function(){
  return B(_AB/* Motion.Main.$wconsView */(_IM/* Motion.Main.lvl34 */, _XY/* Motion.Speed.speedMot */, _IN/* Motion.Main.lvl35 */));
}),
_Yp/* $sreplicateM2 */ = function(_Yq/* s81j */, _Yr/* s81k */){
  var _Ys/* s81l */ = E(_Yq/* s81j */);
  if(!_Ys/* s81l */._){
    return function(_Yt/* s81n */){
      return new F(function(){return A1(_Yt/* s81n */,new T2(0,_6/* GHC.Types.[] */,_Yr/* s81k */));});
    };
  }else{
    var _Yu/* s81C */ = function(_Yv/* s81r */){
      var _Yw/* s81s */ = new T(function(){
        return B(A1(_Ys/* s81l */.a,_Yv/* s81r */));
      }),
      _Yx/* s81B */ = function(_Yy/* s81t */){
        var _Yz/* s81A */ = function(_YA/* s81u */){
          var _YB/* s81z */ = new T(function(){
            var _YC/* s81v */ = E(_YA/* s81u */);
            return new T2(0,function(_YD/* B1 */){
              return new T2(1,_YC/* s81v */.a,_YD/* B1 */);
            },_YC/* s81v */.b);
          });
          return new F(function(){return A1(_Yy/* s81t */,_YB/* s81z */);});
        };
        return new F(function(){return A1(_Yw/* s81s */,_Yz/* s81A */);});
      };
      return E(_Yx/* s81B */);
    };
    return new F(function(){return _55/* Core.World.Internal.$fApplicativeWorld3 */(_Yu/* s81C */, function(_YD/* B1 */){
      return new F(function(){return _Yp/* Motion.Change.$sreplicateM2 */(_Ys/* s81l */.b, _YD/* B1 */);});
    }, _Yr/* s81k */);});
  }
},
_YE/* $swhen1 */ = new T(function(){
  return B(_oH/* Control.Monad.Skeleton.$w$cpure */(_/* EXTERNAL */, _7/* GHC.Tuple.() */));
}),
_YF/* $fNumInt_$c* */ = function(_YG/* s6GP */, _YH/* s6GQ */){
  return imul/* EXTERNAL */(E(_YG/* s6GP */), E(_YH/* s6GQ */))|0;
},
_YI/* $fNumInt_$c+ */ = function(_YJ/* s6H3 */, _YK/* s6H4 */){
  return E(_YJ/* s6H3 */)+E(_YK/* s6H4 */)|0;
},
_YL/* $fNumInt_$c- */ = function(_YM/* s6GW */, _YN/* s6GX */){
  return E(_YM/* s6GW */)-E(_YN/* s6GX */)|0;
},
_YO/* $fNumInt_$cabs */ = function(_YP/* s6Hg */){
  var _YQ/* s6Hh */ = E(_YP/* s6Hg */);
  return (_YQ/* s6Hh */<0) ?  -_YQ/* s6Hh */ : E(_YQ/* s6Hh */);
},
_YR/* $fNumInt_$cfromInteger */ = function(_YS/* s6GJ */){
  return new F(function(){return _US/* GHC.Integer.Type.integerToInt */(_YS/* s6GJ */);});
},
_YT/* $fNumInt_$cnegate */ = function(_YU/* s6GL */){
  return  -E(_YU/* s6GL */);
},
_YV/* $fNumInt1 */ = -1,
_YW/* $fNumInt2 */ = 0,
_YX/* $fNumInt3 */ = 1,
_YY/* $fNumInt_$csignum */ = function(_YZ/* s6Ha */){
  var _Z0/* s6Hb */ = E(_YZ/* s6Ha */);
  return (_Z0/* s6Hb */>=0) ? (E(_Z0/* s6Hb */)==0) ? E(_YW/* GHC.Num.$fNumInt2 */) : E(_YX/* GHC.Num.$fNumInt3 */) : E(_YV/* GHC.Num.$fNumInt1 */);
},
_Z1/* $fNumInt */ = {_:0,a:_YI/* GHC.Num.$fNumInt_$c+ */,b:_YL/* GHC.Num.$fNumInt_$c- */,c:_YF/* GHC.Num.$fNumInt_$c* */,d:_YT/* GHC.Num.$fNumInt_$cnegate */,e:_YO/* GHC.Num.$fNumInt_$cabs */,f:_YY/* GHC.Num.$fNumInt_$csignum */,g:_YR/* GHC.Num.$fNumInt_$cfromInteger */},
_Z2/* $fRandomBool2 */ = function(_Z3/* sftN */){
  var _Z4/* sftO */ = B(_Td/* System.Random.$w$srandomIvalInteger */(_Z1/* GHC.Num.$fNumInt */, _SW/* System.Random.getStdRandom4 */, _SH/* System.Random.$fRandomBool3 */, _Z3/* sftN */));
  return new T2(0,E(_Z4/* sftO */.b),new T(function(){
    if(!E(_Z4/* sftO */.a)){
      return false;
    }else{
      return true;
    }
  }));
},
_Z5/* a10 */ = function(_Z6/* s82q */, _Z7/* s82r */, _Z8/* s82s */){
  var _Z9/* s82t */ = E(_Z6/* s82q */);
  if(!_Z9/* s82t */._){
    return new F(function(){return A1(_Z8/* s82s */,new T2(0,_7/* GHC.Tuple.() */,_Z7/* s82r */));});
  }else{
    var _Za/* s83c */ = function(_/* EXTERNAL */){
      var _Zb/* s82y */ = E(_Xw/* System.Random.theStdGen */),
      _Zc/* s82A */ = mMV/* EXTERNAL */(_Zb/* s82y */, _Z2/* System.Random.$fRandomBool2 */);
      return new T(function(){
        var _Zd/* s83a */ = function(_Ze/* s82I */){
          var _Zf/* s82M */ = function(_Zg/* s82N */, _Zh/* s82O */, _Zi/* s82P */){
            var _Zj/* s82Q */ = E(_Zg/* s82N */);
            if(!_Zj/* s82Q */._){
              return new F(function(){return A1(_Zi/* s82P */,new T2(0,_7/* GHC.Tuple.() */,_Zh/* s82O */));});
            }else{
              var _Zk/* s839 */ = function(_/* EXTERNAL */){
                var _Zl/* s82V */ = mMV/* EXTERNAL */(_Zb/* s82y */, _Z2/* System.Random.$fRandomBool2 */);
                return new T(function(){
                  return B(A(_wJ/* Core.Ease.$wforceTo */,[E(_Zj/* s82Q */.a).c, E(_Zl/* s82V */), _Zh/* s82O */, function(_Zm/* s833 */){
                    return new F(function(){return _Zf/* s82M */(_Zj/* s82Q */.b, E(_Zm/* s833 */).b, _Zi/* s82P */);});
                  }]));
                });
              };
              return new T1(0,_Zk/* s839 */);
            }
          };
          return new F(function(){return _Zf/* s82M */(_Z9/* s82t */.b, E(_Ze/* s82I */).b, _Z8/* s82s */);});
        };
        return B(A(_wJ/* Core.Ease.$wforceTo */,[E(_Z9/* s82t */.a).c, E(_Zc/* s82A */), _Z7/* s82r */, _Zd/* s83a */]));
      });
    };
    return new T1(0,_Za/* s83c */);
  }
},
_Zn/* a */ = new T1(0,_/* EXTERNAL */),
_Zo/* a1 */ = new T1(0,_7/* GHC.Tuple.() */),
_Zp/* a2 */ = new T2(0,E(_Zo/* Motion.Change.a1 */),E(_Zn/* Motion.Change.a */)),
_Zq/* lvl */ = new T4(0,_aw/* GHC.Types.True */,_aw/* GHC.Types.True */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_Zr/* lvl1 */ = new T2(0,_aw/* GHC.Types.True */,_Zq/* Motion.Change.lvl */),
_Zs/* lvl2 */ = new T2(0,_Zr/* Motion.Change.lvl1 */,_6/* GHC.Types.[] */),
_Zt/* lvl3 */ = function(_Zu/* s81E */, _Zv/* s81F */){
  var _Zw/* s81O */ = function(_/* EXTERNAL */){
    var _Zx/* s81H */ = nMV/* EXTERNAL */(_Zs/* Motion.Change.lvl2 */);
    return new T(function(){
      return B(A1(_Zv/* s81F */,new T2(0,new T3(0,_wI/* Core.Ease.forceTo_b1 */,_tX/* Core.Ease.easeIn */,_Zx/* s81H */),_Zu/* s81E */)));
    });
  };
  return new T1(0,_Zw/* s81O */);
},
_Zy/* lvl4 */ = new T2(1,_Zt/* Motion.Change.lvl3 */,_6/* GHC.Types.[] */),
_Zz/* $wxs */ = function(_ZA/* s81P */){
  var _ZB/* s81Q */ = E(_ZA/* s81P */);
  return (_ZB/* s81Q */==1) ? E(_Zy/* Motion.Change.lvl4 */) : new T2(1,_Zt/* Motion.Change.lvl3 */,new T(function(){
    return B(_Zz/* Motion.Change.$wxs */(_ZB/* s81Q */-1|0));
  }));
},
_ZC/* a7 */ = new T(function(){
  return B(_Zz/* Motion.Change.$wxs */(10));
}),
_ZD/* dur */ = 10,
_ZE/* e */ = function(_ZF/* s81T */, _ZG/* s81U */){
  return 1-B(A1(_ZF/* s81T */,new T(function(){
    return Math.pow/* EXTERNAL */(2,  -((1-(1-E(_ZG/* s81U */)))*10));
  })));
},
_ZH/* $fRealDouble1 */ = new T1(0,1),
_ZI/* encodeDoubleInteger */ = function(_ZJ/* s1LC */, _ZK/* s1LD */){
  var _ZL/* s1LE */ = E(_ZJ/* s1LC */);
  return (_ZL/* s1LE */._==0) ? _ZL/* s1LE */.a*Math.pow/* EXTERNAL */(2, _ZK/* s1LD */) : I_toNumber/* EXTERNAL */(_ZL/* s1LE */.a)*Math.pow/* EXTERNAL */(2, _ZK/* s1LD */);
},
_ZM/* rationalToDouble5 */ = new T1(0,0),
_ZN/* $w$j1 */ = function(_ZO/* s18QG */, _ZP/* s18QH */, _ZQ/* s18QI */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_ZQ/* s18QI */, _ZM/* GHC.Float.rationalToDouble5 */))){
    var _ZR/* s18QK */ = B(_VB/* GHC.Integer.Type.quotRemInteger */(_ZP/* s18QH */, _ZQ/* s18QI */)),
    _ZS/* s18QL */ = _ZR/* s18QK */.a;
    switch(B(_Wg/* GHC.Integer.Type.compareInteger */(B(_Jy/* GHC.Integer.Type.shiftLInteger */(_ZR/* s18QK */.b, 1)), _ZQ/* s18QI */))){
      case 0:
        return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(_ZS/* s18QL */, _ZO/* s18QG */);});
        break;
      case 1:
        if(!(B(_US/* GHC.Integer.Type.integerToInt */(_ZS/* s18QL */))&1)){
          return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(_ZS/* s18QL */, _ZO/* s18QG */);});
        }else{
          return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_ZS/* s18QL */, _ZH/* GHC.Float.$fRealDouble1 */)), _ZO/* s18QG */);});
        }
        break;
      default:
        return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_ZS/* s18QL */, _ZH/* GHC.Float.$fRealDouble1 */)), _ZO/* s18QG */);});
    }
  }else{
    return E(_OU/* GHC.Real.divZeroError */);
  }
},
_ZT/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_ZU/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_ZV/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_ZW/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_ZT/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_ZU/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_ZV/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_ZX/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_ZW/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */),
_ZY/* $fExceptionPatternMatchFail1 */ = function(_ZZ/* s4nDQ */){
  return E(_ZX/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_100/* $fExceptionPatternMatchFail_$cfromException */ = function(_101/* s4nE1 */){
  var _102/* s4nE2 */ = E(_101/* s4nE1 */);
  return new F(function(){return _S/* Data.Typeable.cast */(B(_Q/* GHC.Exception.$p1Exception */(_102/* s4nE2 */.a)), _ZY/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _102/* s4nE2 */.b);});
},
_103/* $fExceptionPatternMatchFail_$cshow */ = function(_104/* s4nDT */){
  return E(E(_104/* s4nDT */).a);
},
_105/* $fExceptionPatternMatchFail_$ctoException */ = function(_106/* B1 */){
  return new T2(0,_107/* Control.Exception.Base.$fExceptionPatternMatchFail */,_106/* B1 */);
},
_108/* $fShowPatternMatchFail1 */ = function(_109/* s4nzz */, _10a/* s4nzA */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_109/* s4nzz */).a, _10a/* s4nzA */);});
},
_10b/* $fShowPatternMatchFail_$cshowList */ = function(_10c/* s4nDR */, _10d/* s4nDS */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_108/* Control.Exception.Base.$fShowPatternMatchFail1 */, _10c/* s4nDR */, _10d/* s4nDS */);});
},
_10e/* $fShowPatternMatchFail_$cshowsPrec */ = function(_10f/* s4nDW */, _10g/* s4nDX */, _10h/* s4nDY */){
  return new F(function(){return _2/* GHC.Base.++ */(E(_10g/* s4nDX */).a, _10h/* s4nDY */);});
},
_10i/* $fShowPatternMatchFail */ = new T3(0,_10e/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_103/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_10b/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_107/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_ZY/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_10i/* Control.Exception.Base.$fShowPatternMatchFail */,_105/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_100/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_103/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_10j/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_10k/* lvl */ = function(_10l/* s2S2g */, _10m/* s2S2h */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_10m/* s2S2h */, _10l/* s2S2g */));
  }));});
},
_10n/* throw1 */ = function(_10o/* B2 */, _OR/* B1 */){
  return new F(function(){return _10k/* GHC.Exception.lvl */(_10o/* B2 */, _OR/* B1 */);});
},
_10p/* $wspan */ = function(_10q/* s9wA */, _10r/* s9wB */){
  var _10s/* s9wC */ = E(_10r/* s9wB */);
  if(!_10s/* s9wC */._){
    return new T2(0,_6/* GHC.Types.[] */,_6/* GHC.Types.[] */);
  }else{
    var _10t/* s9wD */ = _10s/* s9wC */.a;
    if(!B(A1(_10q/* s9wA */,_10t/* s9wD */))){
      return new T2(0,_6/* GHC.Types.[] */,_10s/* s9wC */);
    }else{
      var _10u/* s9wG */ = new T(function(){
        var _10v/* s9wH */ = B(_10p/* GHC.List.$wspan */(_10q/* s9wA */, _10s/* s9wC */.b));
        return new T2(0,_10v/* s9wH */.a,_10v/* s9wH */.b);
      });
      return new T2(0,new T2(1,_10t/* s9wD */,new T(function(){
        return E(E(_10u/* s9wG */).a);
      })),new T(function(){
        return E(E(_10u/* s9wG */).b);
      }));
    }
  }
},
_10w/* untangle1 */ = 32,
_10x/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_10y/* untangle3 */ = function(_10z/* s3JKg */){
  return (E(_10z/* s3JKg */)==124) ? false : true;
},
_10A/* untangle */ = function(_10B/* s3JL9 */, _10C/* s3JLa */){
  var _10D/* s3JLc */ = B(_10p/* GHC.List.$wspan */(_10y/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_10B/* s3JL9 */)))),
  _10E/* s3JLd */ = _10D/* s3JLc */.a,
  _10F/* s3JLf */ = function(_10G/* s3JLg */, _10H/* s3JLh */){
    var _10I/* s3JLk */ = new T(function(){
      var _10J/* s3JLj */ = new T(function(){
        return B(_2/* GHC.Base.++ */(_10C/* s3JLa */, new T(function(){
          return B(_2/* GHC.Base.++ */(_10H/* s3JLh */, _10x/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _10J/* s3JLj */));
    },1);
    return new F(function(){return _2/* GHC.Base.++ */(_10G/* s3JLg */, _10I/* s3JLk */);});
  },
  _10K/* s3JLl */ = E(_10D/* s3JLc */.b);
  if(!_10K/* s3JLl */._){
    return new F(function(){return _10F/* s3JLf */(_10E/* s3JLd */, _6/* GHC.Types.[] */);});
  }else{
    if(E(_10K/* s3JLl */.a)==124){
      return new F(function(){return _10F/* s3JLf */(_10E/* s3JLd */, new T2(1,_10w/* GHC.IO.Exception.untangle1 */,_10K/* s3JLl */.b));});
    }else{
      return new F(function(){return _10F/* s3JLf */(_10E/* s3JLd */, _6/* GHC.Types.[] */);});
    }
  }
},
_10L/* patError */ = function(_10M/* s4nFx */){
  return new F(function(){return _10n/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_10A/* GHC.IO.Exception.untangle */(_10M/* s4nFx */, _10j/* Control.Exception.Base.lvl3 */));
  })), _107/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_10N/* log2I */ = function(_10O/* s1Ju */){
  var _10P/* s1Jv */ = function(_10Q/* s1Jw */, _10R/* s1Jx */){
    while(1){
      if(!B(_KW/* GHC.Integer.Type.ltInteger */(_10Q/* s1Jw */, _10O/* s1Ju */))){
        if(!B(_Kq/* GHC.Integer.Type.gtInteger */(_10Q/* s1Jw */, _10O/* s1Ju */))){
          if(!B(_QT/* GHC.Integer.Type.eqInteger */(_10Q/* s1Jw */, _10O/* s1Ju */))){
            return new F(function(){return _10L/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});
          }else{
            return E(_10R/* s1Jx */);
          }
        }else{
          return _10R/* s1Jx */-1|0;
        }
      }else{
        var _10S/*  s1Jw */ = B(_Jy/* GHC.Integer.Type.shiftLInteger */(_10Q/* s1Jw */, 1)),
        _10T/*  s1Jx */ = _10R/* s1Jx */+1|0;
        _10Q/* s1Jw */ = _10S/*  s1Jw */;
        _10R/* s1Jx */ = _10T/*  s1Jx */;
        continue;
      }
    }
  };
  return new F(function(){return _10P/* s1Jv */(_JF/* GHC.Integer.Type.log2I1 */, 0);});
},
_10U/* integerLog2# */ = function(_10V/* s1JD */){
  var _10W/* s1JE */ = E(_10V/* s1JD */);
  if(!_10W/* s1JE */._){
    var _10X/* s1JG */ = _10W/* s1JE */.a>>>0;
    if(!_10X/* s1JG */){
      return -1;
    }else{
      var _10Y/* s1JH */ = function(_10Z/* s1JI */, _110/* s1JJ */){
        while(1){
          if(_10Z/* s1JI */>=_10X/* s1JG */){
            if(_10Z/* s1JI */<=_10X/* s1JG */){
              if(_10Z/* s1JI */!=_10X/* s1JG */){
                return new F(function(){return _10L/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_110/* s1JJ */);
              }
            }else{
              return _110/* s1JJ */-1|0;
            }
          }else{
            var _111/*  s1JI */ = imul/* EXTERNAL */(_10Z/* s1JI */, 2)>>>0,
            _112/*  s1JJ */ = _110/* s1JJ */+1|0;
            _10Z/* s1JI */ = _111/*  s1JI */;
            _110/* s1JJ */ = _112/*  s1JJ */;
            continue;
          }
        }
      };
      return new F(function(){return _10Y/* s1JH */(1, 0);});
    }
  }else{
    return new F(function(){return _10N/* GHC.Integer.Type.log2I */(_10W/* s1JE */);});
  }
},
_113/* integerLog2IsPowerOf2# */ = function(_114/* s1JT */){
  var _115/* s1JU */ = E(_114/* s1JT */);
  if(!_115/* s1JU */._){
    var _116/* s1JW */ = _115/* s1JU */.a>>>0;
    if(!_116/* s1JW */){
      return new T2(0,-1,0);
    }else{
      var _117/* s1JX */ = function(_118/* s1JY */, _119/* s1JZ */){
        while(1){
          if(_118/* s1JY */>=_116/* s1JW */){
            if(_118/* s1JY */<=_116/* s1JW */){
              if(_118/* s1JY */!=_116/* s1JW */){
                return new F(function(){return _10L/* Control.Exception.Base.patError */("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_119/* s1JZ */);
              }
            }else{
              return _119/* s1JZ */-1|0;
            }
          }else{
            var _11a/*  s1JY */ = imul/* EXTERNAL */(_118/* s1JY */, 2)>>>0,
            _11b/*  s1JZ */ = _119/* s1JZ */+1|0;
            _118/* s1JY */ = _11a/*  s1JY */;
            _119/* s1JZ */ = _11b/*  s1JZ */;
            continue;
          }
        }
      };
      return new T2(0,B(_117/* s1JX */(1, 0)),(_116/* s1JW */&_116/* s1JW */-1>>>0)>>>0&4294967295);
    }
  }else{
    var _11c/* s1Kc */ = _115/* s1JU */.a;
    return new T2(0,B(_10U/* GHC.Integer.Type.integerLog2# */(_115/* s1JU */)),I_compareInt/* EXTERNAL */(I_and/* EXTERNAL */(_11c/* s1Kc */, I_sub/* EXTERNAL */(_11c/* s1Kc */, I_fromInt/* EXTERNAL */(1))), 0));
  }
},
_11d/* andInteger */ = function(_11e/* s1Lf */, _11f/* s1Lg */){
  while(1){
    var _11g/* s1Lh */ = E(_11e/* s1Lf */);
    if(!_11g/* s1Lh */._){
      var _11h/* s1Li */ = _11g/* s1Lh */.a,
      _11i/* s1Lj */ = E(_11f/* s1Lg */);
      if(!_11i/* s1Lj */._){
        return new T1(0,(_11h/* s1Li */>>>0&_11i/* s1Lj */.a>>>0)>>>0&4294967295);
      }else{
        _11e/* s1Lf */ = new T1(1,I_fromInt/* EXTERNAL */(_11h/* s1Li */));
        _11f/* s1Lg */ = _11i/* s1Lj */;
        continue;
      }
    }else{
      var _11j/* s1Lu */ = E(_11f/* s1Lg */);
      if(!_11j/* s1Lu */._){
        _11e/* s1Lf */ = _11g/* s1Lh */;
        _11f/* s1Lg */ = new T1(1,I_fromInt/* EXTERNAL */(_11j/* s1Lu */.a));
        continue;
      }else{
        return new T1(1,I_and/* EXTERNAL */(_11g/* s1Lh */.a, _11j/* s1Lu */.a));
      }
    }
  }
},
_11k/* roundingMode#1 */ = new T1(0,2),
_11l/* roundingMode# */ = function(_11m/* s1Pt */, _11n/* s1Pu */){
  var _11o/* s1Pv */ = E(_11m/* s1Pt */);
  if(!_11o/* s1Pv */._){
    var _11p/* s1Px */ = (_11o/* s1Pv */.a>>>0&(2<<_11n/* s1Pu */>>>0)-1>>>0)>>>0,
    _11q/* s1PB */ = 1<<_11n/* s1Pu */>>>0;
    return (_11q/* s1PB */<=_11p/* s1Px */) ? (_11q/* s1PB */>=_11p/* s1Px */) ? 1 : 2 : 0;
  }else{
    var _11r/* s1PH */ = B(_11d/* GHC.Integer.Type.andInteger */(_11o/* s1Pv */, B(_Lm/* GHC.Integer.Type.minusInteger */(B(_Jy/* GHC.Integer.Type.shiftLInteger */(_11k/* GHC.Integer.Type.roundingMode#1 */, _11n/* s1Pu */)), _JF/* GHC.Integer.Type.log2I1 */)))),
    _11s/* s1PK */ = B(_Jy/* GHC.Integer.Type.shiftLInteger */(_JF/* GHC.Integer.Type.log2I1 */, _11n/* s1Pu */));
    return (!B(_Kq/* GHC.Integer.Type.gtInteger */(_11s/* s1PK */, _11r/* s1PH */))) ? (!B(_KW/* GHC.Integer.Type.ltInteger */(_11s/* s1PK */, _11r/* s1PH */))) ? 1 : 2 : 0;
  }
},
_11t/* shiftRInteger */ = function(_11u/* s1Ja */, _11v/* s1Jb */){
  while(1){
    var _11w/* s1Jc */ = E(_11u/* s1Ja */);
    if(!_11w/* s1Jc */._){
      _11u/* s1Ja */ = new T1(1,I_fromInt/* EXTERNAL */(_11w/* s1Jc */.a));
      continue;
    }else{
      return new T1(1,I_shiftRight/* EXTERNAL */(_11w/* s1Jc */.a, _11v/* s1Jb */));
    }
  }
},
_11x/* $w$sfromRat'' */ = function(_11y/* s18QU */, _11z/* s18QV */, _11A/* s18QW */, _11B/* s18QX */){
  var _11C/* s18QY */ = B(_113/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_11B/* s18QX */)),
  _11D/* s18QZ */ = _11C/* s18QY */.a;
  if(!E(_11C/* s18QY */.b)){
    var _11E/* s18Rp */ = B(_10U/* GHC.Integer.Type.integerLog2# */(_11A/* s18QW */));
    if(_11E/* s18Rp */<((_11D/* s18QZ */+_11y/* s18QU */|0)-1|0)){
      var _11F/* s18Ru */ = _11D/* s18QZ */+(_11y/* s18QU */-_11z/* s18QV */|0)|0;
      if(_11F/* s18Ru */>0){
        if(_11F/* s18Ru */>_11E/* s18Rp */){
          if(_11F/* s18Ru */<=(_11E/* s18Rp */+1|0)){
            if(!E(B(_113/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_11A/* s18QW */)).b)){
              return 0;
            }else{
              return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(_ZH/* GHC.Float.$fRealDouble1 */, _11y/* s18QU */-_11z/* s18QV */|0);});
            }
          }else{
            return 0;
          }
        }else{
          var _11G/* s18RI */ = B(_11t/* GHC.Integer.Type.shiftRInteger */(_11A/* s18QW */, _11F/* s18Ru */));
          switch(B(_11l/* GHC.Integer.Type.roundingMode# */(_11A/* s18QW */, _11F/* s18Ru */-1|0))){
            case 0:
              return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(_11G/* s18RI */, _11y/* s18QU */-_11z/* s18QV */|0);});
              break;
            case 1:
              if(!(B(_US/* GHC.Integer.Type.integerToInt */(_11G/* s18RI */))&1)){
                return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(_11G/* s18RI */, _11y/* s18QU */-_11z/* s18QV */|0);});
              }else{
                return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_11G/* s18RI */, _ZH/* GHC.Float.$fRealDouble1 */)), _11y/* s18QU */-_11z/* s18QV */|0);});
              }
              break;
            default:
              return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_11G/* s18RI */, _ZH/* GHC.Float.$fRealDouble1 */)), _11y/* s18QU */-_11z/* s18QV */|0);});
          }
        }
      }else{
        return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(_11A/* s18QW */, (_11y/* s18QU */-_11z/* s18QV */|0)-_11F/* s18Ru */|0);});
      }
    }else{
      if(_11E/* s18Rp */>=_11z/* s18QV */){
        var _11H/* s18RX */ = B(_11t/* GHC.Integer.Type.shiftRInteger */(_11A/* s18QW */, (_11E/* s18Rp */+1|0)-_11z/* s18QV */|0));
        switch(B(_11l/* GHC.Integer.Type.roundingMode# */(_11A/* s18QW */, _11E/* s18Rp */-_11z/* s18QV */|0))){
          case 0:
            return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(_11H/* s18RX */, ((_11E/* s18Rp */-_11D/* s18QZ */|0)+1|0)-_11z/* s18QV */|0);});
            break;
          case 2:
            return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_11H/* s18RX */, _ZH/* GHC.Float.$fRealDouble1 */)), ((_11E/* s18Rp */-_11D/* s18QZ */|0)+1|0)-_11z/* s18QV */|0);});
            break;
          default:
            if(!(B(_US/* GHC.Integer.Type.integerToInt */(_11H/* s18RX */))&1)){
              return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(_11H/* s18RX */, ((_11E/* s18Rp */-_11D/* s18QZ */|0)+1|0)-_11z/* s18QV */|0);});
            }else{
              return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(B(_JH/* GHC.Integer.Type.plusInteger */(_11H/* s18RX */, _ZH/* GHC.Float.$fRealDouble1 */)), ((_11E/* s18Rp */-_11D/* s18QZ */|0)+1|0)-_11z/* s18QV */|0);});
            }
        }
      }else{
        return new F(function(){return _ZI/* GHC.Integer.Type.encodeDoubleInteger */(_11A/* s18QW */,  -_11D/* s18QZ */);});
      }
    }
  }else{
    var _11I/* s18R3 */ = B(_10U/* GHC.Integer.Type.integerLog2# */(_11A/* s18QW */))-_11D/* s18QZ */|0,
    _11J/* s18R4 */ = function(_11K/* s18R5 */){
      var _11L/* s18R6 */ = function(_11M/* s18R7 */, _11N/* s18R8 */){
        if(!B(_W2/* GHC.Integer.Type.leInteger */(B(_Jy/* GHC.Integer.Type.shiftLInteger */(_11N/* s18R8 */, _11z/* s18QV */)), _11M/* s18R7 */))){
          return new F(function(){return _ZN/* GHC.Float.$w$j1 */(_11K/* s18R5 */-_11z/* s18QV */|0, _11M/* s18R7 */, _11N/* s18R8 */);});
        }else{
          return new F(function(){return _ZN/* GHC.Float.$w$j1 */((_11K/* s18R5 */-_11z/* s18QV */|0)+1|0, _11M/* s18R7 */, B(_Jy/* GHC.Integer.Type.shiftLInteger */(_11N/* s18R8 */, 1)));});
        }
      };
      if(_11K/* s18R5 */>=_11z/* s18QV */){
        if(_11K/* s18R5 */!=_11z/* s18QV */){
          return new F(function(){return _11L/* s18R6 */(_11A/* s18QW */, new T(function(){
            return B(_Jy/* GHC.Integer.Type.shiftLInteger */(_11B/* s18QX */, _11K/* s18R5 */-_11z/* s18QV */|0));
          }));});
        }else{
          return new F(function(){return _11L/* s18R6 */(_11A/* s18QW */, _11B/* s18QX */);});
        }
      }else{
        return new F(function(){return _11L/* s18R6 */(new T(function(){
          return B(_Jy/* GHC.Integer.Type.shiftLInteger */(_11A/* s18QW */, _11z/* s18QV */-_11K/* s18R5 */|0));
        }), _11B/* s18QX */);});
      }
    };
    if(_11y/* s18QU */>_11I/* s18R3 */){
      return new F(function(){return _11J/* s18R4 */(_11y/* s18QU */);});
    }else{
      return new F(function(){return _11J/* s18R4 */(_11I/* s18R3 */);});
    }
  }
},
_11O/* rationalToDouble1 */ = new T(function(){
  return 0/0;
}),
_11P/* rationalToDouble2 */ = new T(function(){
  return -1/0;
}),
_11Q/* rationalToDouble3 */ = new T(function(){
  return 1/0;
}),
_11R/* rationalToDouble4 */ = 0,
_11S/* rationalToDouble */ = function(_11T/* s197E */, _11U/* s197F */){
  if(!B(_QT/* GHC.Integer.Type.eqInteger */(_11U/* s197F */, _ZM/* GHC.Float.rationalToDouble5 */))){
    if(!B(_QT/* GHC.Integer.Type.eqInteger */(_11T/* s197E */, _ZM/* GHC.Float.rationalToDouble5 */))){
      if(!B(_KW/* GHC.Integer.Type.ltInteger */(_11T/* s197E */, _ZM/* GHC.Float.rationalToDouble5 */))){
        return new F(function(){return _11x/* GHC.Float.$w$sfromRat'' */(-1021, 53, _11T/* s197E */, _11U/* s197F */);});
      }else{
        return  -B(_11x/* GHC.Float.$w$sfromRat'' */(-1021, 53, B(_JR/* GHC.Integer.Type.negateInteger */(_11T/* s197E */)), _11U/* s197F */));
      }
    }else{
      return E(_11R/* GHC.Float.rationalToDouble4 */);
    }
  }else{
    return (!B(_QT/* GHC.Integer.Type.eqInteger */(_11T/* s197E */, _ZM/* GHC.Float.rationalToDouble5 */))) ? (!B(_KW/* GHC.Integer.Type.ltInteger */(_11T/* s197E */, _ZM/* GHC.Float.rationalToDouble5 */))) ? E(_11Q/* GHC.Float.rationalToDouble3 */) : E(_11P/* GHC.Float.rationalToDouble2 */) : E(_11O/* GHC.Float.rationalToDouble1 */);
  }
},
_11V/* $fFractionalDouble_$cfromRational */ = function(_11W/* s197P */){
  var _11X/* s197Q */ = E(_11W/* s197P */);
  return new F(function(){return _11S/* GHC.Float.rationalToDouble */(_11X/* s197Q */.a, _11X/* s197Q */.b);});
},
_11Y/* $fFractionalDouble_$crecip */ = function(_11Z/* s191m */){
  return 1/E(_11Z/* s191m */);
},
_120/* $fNumDouble_$cabs */ = function(_121/* s190N */){
  var _122/* s190O */ = E(_121/* s190N */),
  _123/* s190Q */ = E(_122/* s190O */);
  return (_123/* s190Q */==0) ? E(_11R/* GHC.Float.rationalToDouble4 */) : (_123/* s190Q */<=0) ?  -_123/* s190Q */ : E(_122/* s190O */);
},
_124/* $fNumDouble_$cfromInteger */ = function(_125/* s190E */){
  return new F(function(){return _Sv/* GHC.Integer.Type.doubleFromInteger */(_125/* s190E */);});
},
_126/* $fNumDouble1 */ = 1,
_127/* $fNumDouble2 */ = -1,
_128/* $fNumDouble_$csignum */ = function(_129/* s190G */){
  var _12a/* s190H */ = E(_129/* s190G */);
  return (_12a/* s190H */<=0) ? (_12a/* s190H */>=0) ? E(_12a/* s190H */) : E(_127/* GHC.Float.$fNumDouble2 */) : E(_126/* GHC.Float.$fNumDouble1 */);
},
_12b/* minusDouble */ = function(_12c/* s18yR */, _12d/* s18yS */){
  return E(_12c/* s18yR */)-E(_12d/* s18yS */);
},
_12e/* $fNumDouble */ = {_:0,a:_BU/* GHC.Float.plusDouble */,b:_12b/* GHC.Float.minusDouble */,c:_vu/* GHC.Float.timesDouble */,d:_FA/* GHC.Float.negateDouble */,e:_120/* GHC.Float.$fNumDouble_$cabs */,f:_128/* GHC.Float.$fNumDouble_$csignum */,g:_124/* GHC.Float.$fNumDouble_$cfromInteger */},
_12f/* $fFractionalDouble */ = new T4(0,_12e/* GHC.Float.$fNumDouble */,_in/* GHC.Float.divideDouble */,_11Y/* GHC.Float.$fFractionalDouble_$crecip */,_11V/* GHC.Float.$fFractionalDouble_$cfromRational */),
_12g/* $fEqDouble_$c/= */ = function(_12h/* scFX */, _12i/* scFY */){
  return (E(_12h/* scFX */)!=E(_12i/* scFY */)) ? true : false;
},
_12j/* $fEqDouble_$c== */ = function(_12k/* scFQ */, _12l/* scFR */){
  return E(_12k/* scFQ */)==E(_12l/* scFR */);
},
_12m/* $fEqDouble */ = new T2(0,_12j/* GHC.Classes.$fEqDouble_$c== */,_12g/* GHC.Classes.$fEqDouble_$c/= */),
_12n/* $fOrdDouble_$c< */ = function(_12o/* scIa */, _12p/* scIb */){
  return E(_12o/* scIa */)<E(_12p/* scIb */);
},
_12q/* $fOrdDouble_$c<= */ = function(_12r/* scI3 */, _12s/* scI4 */){
  return E(_12r/* scI3 */)<=E(_12s/* scI4 */);
},
_12t/* $fOrdDouble_$c> */ = function(_12u/* scHW */, _12v/* scHX */){
  return E(_12u/* scHW */)>E(_12v/* scHX */);
},
_12w/* $fOrdDouble_$c>= */ = function(_12x/* scHP */, _12y/* scHQ */){
  return E(_12x/* scHP */)>=E(_12y/* scHQ */);
},
_12z/* $fOrdDouble_$ccompare */ = function(_12A/* scIh */, _12B/* scIi */){
  var _12C/* scIj */ = E(_12A/* scIh */),
  _12D/* scIl */ = E(_12B/* scIi */);
  return (_12C/* scIj */>=_12D/* scIl */) ? (_12C/* scIj */!=_12D/* scIl */) ? 2 : 1 : 0;
},
_12E/* $fOrdDouble_$cmax */ = function(_12F/* scIz */, _12G/* scIA */){
  var _12H/* scIB */ = E(_12F/* scIz */),
  _12I/* scID */ = E(_12G/* scIA */);
  return (_12H/* scIB */>_12I/* scID */) ? E(_12H/* scIB */) : E(_12I/* scID */);
},
_12J/* $fOrdDouble_$cmin */ = function(_12K/* scIr */, _12L/* scIs */){
  var _12M/* scIt */ = E(_12K/* scIr */),
  _12N/* scIv */ = E(_12L/* scIs */);
  return (_12M/* scIt */>_12N/* scIv */) ? E(_12N/* scIv */) : E(_12M/* scIt */);
},
_12O/* $fOrdDouble */ = {_:0,a:_12m/* GHC.Classes.$fEqDouble */,b:_12z/* GHC.Classes.$fOrdDouble_$ccompare */,c:_12n/* GHC.Classes.$fOrdDouble_$c< */,d:_12q/* GHC.Classes.$fOrdDouble_$c<= */,e:_12t/* GHC.Classes.$fOrdDouble_$c> */,f:_12w/* GHC.Classes.$fOrdDouble_$c>= */,g:_12E/* GHC.Classes.$fOrdDouble_$cmax */,h:_12J/* GHC.Classes.$fOrdDouble_$cmin */},
_12P/* lvl8 */ = -1,
_12Q/* $p1Fractional */ = function(_12R/* svdN */){
  return E(E(_12R/* svdN */).a);
},
_12S/* + */ = function(_12T/* s6Fy */){
  return E(E(_12T/* s6Fy */).a);
},
_12U/* $wnumericEnumFrom */ = function(_12V/* svLB */, _12W/* svLC */){
  var _12X/* svLD */ = E(_12W/* svLC */),
  _12Y/* svLK */ = new T(function(){
    var _12Z/* svLE */ = B(_12Q/* GHC.Real.$p1Fractional */(_12V/* svLB */)),
    _130/* svLH */ = B(_12U/* GHC.Real.$wnumericEnumFrom */(_12V/* svLB */, B(A3(_12S/* GHC.Num.+ */,_12Z/* svLE */, _12X/* svLD */, new T(function(){
      return B(A2(_Ko/* GHC.Num.fromInteger */,_12Z/* svLE */, _Kj/* GHC.Real.$fEnumRatio1 */));
    })))));
    return new T2(1,_130/* svLH */.a,_130/* svLH */.b);
  });
  return new T2(0,_12X/* svLD */,_12Y/* svLK */);
},
_131/* / */ = function(_132/* svdT */){
  return E(E(_132/* svdT */).b);
},
_133/* <= */ = function(_134/* scCl */){
  return E(E(_134/* scCl */).d);
},
_135/* takeWhile */ = function(_136/* s9yw */, _137/* s9yx */){
  var _138/* s9yy */ = E(_137/* s9yx */);
  if(!_138/* s9yy */._){
    return __Z/* EXTERNAL */;
  }else{
    var _139/* s9yz */ = _138/* s9yy */.a;
    return (!B(A1(_136/* s9yw */,_139/* s9yz */))) ? __Z/* EXTERNAL */ : new T2(1,_139/* s9yz */,new T(function(){
      return B(_135/* GHC.List.takeWhile */(_136/* s9yw */, _138/* s9yy */.b));
    }));
  }
},
_13a/* numericEnumFromTo */ = function(_13b/* svMm */, _13c/* svMn */, _13d/* svMo */, _13e/* svMp */){
  var _13f/* svMq */ = B(_12U/* GHC.Real.$wnumericEnumFrom */(_13c/* svMn */, _13d/* svMo */)),
  _13g/* svMt */ = new T(function(){
    var _13h/* svMu */ = B(_12Q/* GHC.Real.$p1Fractional */(_13c/* svMn */)),
    _13i/* svMx */ = new T(function(){
      return B(A3(_131/* GHC.Real./ */,_13c/* svMn */, new T(function(){
        return B(A2(_Ko/* GHC.Num.fromInteger */,_13h/* svMu */, _Kj/* GHC.Real.$fEnumRatio1 */));
      }), new T(function(){
        return B(A2(_Ko/* GHC.Num.fromInteger */,_13h/* svMu */, _RU/* GHC.Real.even2 */));
      })));
    });
    return B(A3(_12S/* GHC.Num.+ */,_13h/* svMu */, _13e/* svMp */, _13i/* svMx */));
  });
  return new F(function(){return _135/* GHC.List.takeWhile */(function(_13j/* svMy */){
    return new F(function(){return A3(_133/* GHC.Classes.<= */,_13b/* svMm */, _13j/* svMy */, _13g/* svMt */);});
  }, new T2(1,_13f/* svMq */.a,_13f/* svMq */.b));});
},
_13k/* x */ = 1,
_13l/* lvl9 */ = new T(function(){
  return B(_13a/* GHC.Real.numericEnumFromTo */(_12O/* GHC.Classes.$fOrdDouble */, _12f/* GHC.Float.$fFractionalDouble */, _12P/* Motion.Change.lvl8 */, _13k/* Motion.Change.x */));
}),
_13m/* go */ = function(_13n/* s826 */){
  var _13o/* s827 */ = E(_13n/* s826 */);
  if(!_13o/* s827 */._){
    return __Z/* EXTERNAL */;
  }else{
    var _13p/* s82a */ = new T(function(){
      return E(_13o/* s827 */.a)*100;
    }),
    _13q/* s82e */ = new T(function(){
      return B(_13m/* Motion.Change.go */(_13o/* s827 */.b));
    }),
    _13r/* s82f */ = function(_13s/* s82g */){
      var _13t/* s82h */ = E(_13s/* s82g */);
      return (_13t/* s82h */._==0) ? E(_13q/* s82e */) : new T2(1,new T2(0,_13p/* s82a */,new T(function(){
        return E(_13t/* s82h */.a)*100;
      })),new T(function(){
        return B(_13r/* s82f */(_13t/* s82h */.b));
      }));
    };
    return new F(function(){return _13r/* s82f */(_13l/* Motion.Change.lvl9 */);});
  }
},
_13u/* lvl10 */ = new T(function(){
  return B(_13m/* Motion.Change.go */(_13l/* Motion.Change.lvl9 */));
}),
_13v/* lvl11 */ = 1.5,
_13w/* lvl12 */ = 15,
_13x/* lvl13 */ = 50,
_13y/* lvl14 */ = 100,
_13z/* lvl15 */ = new T4(0,_13k/* Motion.Change.x */,_13k/* Motion.Change.x */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_13A/* lvl16 */ = new T2(0,_13k/* Motion.Change.x */,_13z/* Motion.Change.lvl15 */),
_13B/* lvl17 */ = new T2(0,_13A/* Motion.Change.lvl16 */,_6/* GHC.Types.[] */),
_13C/* a8 */ = 100,
_13D/* lvl5 */ = new T1(0,_13C/* Motion.Change.a8 */),
_13E/* lvl6 */ = new T2(0,_13D/* Motion.Change.lvl5 */,_13D/* Motion.Change.lvl5 */),
_13F/* a9 */ = 3,
_13G/* lvl7 */ = new T1(0,_13F/* Motion.Change.a9 */),
_13H/* valueIO1 */ = function(_13I/* sl3L */, _/* EXTERNAL */){
  var _13J/* sl3N */ = E(_13I/* sl3L */);
  switch(_13J/* sl3N */._){
    case 0:
      return new T1(1,_13J/* sl3N */.a);
    case 1:
      var _13K/* sl3R */ = B(A1(_13J/* sl3N */.a,_/* EXTERNAL */));
      return new T1(1,_13K/* sl3R */);
    case 2:
      var _13L/* sl43 */ = rMV/* EXTERNAL */(E(E(_13J/* sl3N */.a).c)),
      _13M/* sl46 */ = E(_13L/* sl43 */);
      if(!_13M/* sl46 */._){
        var _13N/* sl4a */ = new T(function(){
          return B(A1(_13J/* sl3N */.b,new T(function(){
            return B(_fB/* Data.Tuple.fst */(_13M/* sl46 */.a));
          })));
        });
        return new T1(1,_13N/* sl4a */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
      break;
    default:
      var _13O/* sl4l */ = rMV/* EXTERNAL */(E(E(_13J/* sl3N */.a).c)),
      _13P/* sl4o */ = E(_13O/* sl4l */);
      if(!_13P/* sl4o */._){
        var _13Q/* sl4u */ = B(A2(_13J/* sl3N */.b,E(_13P/* sl4o */.a).a, _/* EXTERNAL */));
        return new T1(1,_13Q/* sl4u */);
      }else{
        return _2o/* GHC.Base.Nothing */;
      }
  }
},
_13R/* changeMot1 */ = function(_13S/* s83d */, _13T/* s83e */){
  var _13U/* s83f */ = new T(function(){
    return B(_Yp/* Motion.Change.$sreplicateM2 */(_ZC/* Motion.Change.a7 */, _13T/* s83e */));
  }),
  _13V/* s83g */ = function(_13W/* s83h */, _13X/* s83i */){
    var _13Y/* s83j */ = E(_13W/* s83h */);
    if(!_13Y/* s83j */._){
      return E(_Zp/* Motion.Change.a2 */);
    }else{
      var _13Z/* s83m */ = E(_13X/* s83i */);
      if(!_13Z/* s83m */._){
        return E(_Zp/* Motion.Change.a2 */);
      }else{
        var _140/* s83p */ = E(_13Z/* s83m */.a),
        _141/* s83s */ = new T(function(){
          return B(_HY/* Core.Ease.morph */(_13Y/* s83j */.a));
        }),
        _142/* s83v */ = B(_pg/* Control.Monad.Skeleton.bone */(new T1(1,function(_/* EXTERNAL */){
          return new F(function(){return _13H/* Core.Ease.valueIO1 */(_141/* s83s */, _/* EXTERNAL */);});
        }))),
        _143/* s83y */ = new T(function(){
          return B(_13V/* s83g */(_13Y/* s83j */.b, _13Z/* s83m */.b));
        }),
        _144/* s83z */ = new T(function(){
          return B(_ro/* Core.Render.Internal.fill1 */(_13S/* s83d */, new T(function(){
            var _145/* s83C */ = B(_Gl/* Core.Shape.Internal.$wcenterRect */(new T1(0,_140/* s83p */.a), new T1(0,_140/* s83p */.b), _13D/* Motion.Change.lvl5 */, _13D/* Motion.Change.lvl5 */));
            return new T3(0,_145/* s83C */.a,_145/* s83C */.b,_145/* s83C */.c);
          })));
        });
        return new T2(0,E(_142/* s83v */.a),E(new T2(2,new T2(2,_142/* s83v */.b,new T1(1,function(_146/* s83H */){
          var _147/* s83I */ = E(_146/* s83H */);
          return (_147/* s83I */._==0) ? E(_YE/* Motion.Change.$swhen1 */) : (!E(_147/* s83I */.a)) ? E(_YE/* Motion.Change.$swhen1 */) : E(_144/* s83z */);
        })),new T1(1,function(_148/* s83O */){
          return E(_143/* s83y */);
        }))));
      }
    }
  },
  _149/* s85x */ = function(_14a/* s83S */){
    var _14b/* s85w */ = function(_14c/* s83T */){
      var _14d/* s83U */ = E(_14c/* s83T */),
      _14e/* s83V */ = _14d/* s83U */.a,
      _14f/* s85v */ = function(_/* EXTERNAL */){
        var _14g/* s83Y */ = nMV/* EXTERNAL */(_13B/* Motion.Change.lvl17 */);
        return new T(function(){
          var _14h/* s842 */ = new T(function(){
            return B(_iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _ZD/* Motion.Change.dur */, _ZE/* Motion.Change.e */, _14g/* s83Y */, _13k/* Motion.Change.x */, _tT/* Core.Ease.easeTo1 */));
          }),
          _14i/* s843 */ = new T(function(){
            return B(_wJ/* Core.Ease.$wforceTo */(_14g/* s83Y */, _13v/* Motion.Change.lvl11 */));
          }),
          _14j/* s844 */ = function(_14k/* s845 */, _14l/* s846 */){
            var _14m/* s847 */ = function(_14n/* s848 */){
              return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_13w/* Motion.Change.lvl12 */, E(_14n/* s848 */).b, _14l/* s846 */);});
            },
            _14o/* s84c */ = function(_14p/* s84d */){
              return new F(function(){return A2(_14h/* s842 */,E(_14p/* s84d */).b, _14m/* s847 */);});
            };
            return new F(function(){return _Z5/* Motion.Change.a10 */(_14e/* s83V */, _14k/* s845 */, function(_14q/* s84h */){
              return new F(function(){return A2(_14i/* s843 */,E(_14q/* s84h */).b, _14o/* s84c */);});
            });});
          },
          _14r/* s84m */ = new T(function(){
            var _14s/* s84o */ = function(_14t/* s84p */){
              var _14u/* s84q */ = E(_14t/* s84p */);
              return (_14u/* s84q */==1) ? E(new T2(1,_14j/* s844 */,_6/* GHC.Types.[] */)) : new T2(1,_14j/* s844 */,new T(function(){
                return B(_14s/* s84o */(_14u/* s84q */-1|0));
              }));
            };
            return B(_14s/* s84o */(4));
          }),
          _14v/* s84t */ = function(_14w/* s84u */){
            var _14x/* s84v */ = new T(function(){
              return B(_Yp/* Motion.Change.$sreplicateM2 */(_14r/* s84m */, _14w/* s84u */));
            }),
            _14y/* s85g */ = function(_14z/* s84w */){
              var _14A/* s84x */ = function(_14B/* s84y */){
                return new F(function(){return A2(_14v/* s84t */,E(_14B/* s84y */).b, _14z/* s84w */);});
              },
              _14C/* s84C */ = function(_14D/* s84D */){
                return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_13y/* Motion.Change.lvl14 */, E(_14D/* s84D */).b, _14A/* s84x */);});
              },
              _14E/* s84H */ = function(_14F/* s84I */){
                return new F(function(){return A2(_14h/* s842 */,E(_14F/* s84I */).b, _14C/* s84C */);});
              },
              _14G/* s84M */ = function(_14H/* s84N */){
                return new F(function(){return A2(_14i/* s843 */,E(_14H/* s84N */).b, _14E/* s84H */);});
              },
              _14I/* s84R */ = function(_14J/* s84S */){
                return new F(function(){return _Z5/* Motion.Change.a10 */(_14e/* s83V */, E(_14J/* s84S */).b, _14G/* s84M */);});
              },
              _14K/* s84W */ = function(_14L/* s84X */){
                return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_13x/* Motion.Change.lvl13 */, E(_14L/* s84X */).b, _14I/* s84R */);});
              },
              _14M/* s851 */ = function(_14N/* s852 */){
                return new F(function(){return A2(_14h/* s842 */,E(_14N/* s852 */).b, _14K/* s84W */);});
              },
              _14O/* s856 */ = function(_14P/* s857 */){
                return new F(function(){return A2(_14i/* s843 */,E(_14P/* s857 */).b, _14M/* s851 */);});
              };
              return new F(function(){return A1(_14x/* s84v */,function(_14Q/* s85b */){
                return new F(function(){return _Z5/* Motion.Change.a10 */(_14e/* s83V */, E(_14Q/* s85b */).b, _14O/* s856 */);});
              });});
            };
            return E(_14y/* s85g */);
          },
          _14R/* s85r */ = new T(function(){
            var _14S/* s85p */ = new T(function(){
              var _14T/* s85h */ = new T3(0,_ZD/* Motion.Change.dur */,_ZE/* Motion.Change.e */,_14g/* s83Y */);
              return B(_pg/* Control.Monad.Skeleton.bone */(new T3(7,new T2(0,new T(function(){
                return B(_uj/* Core.Ease.opLift */(_in/* GHC.Float.divideDouble */, new T2(2,_14T/* s85h */,_2E/* GHC.Base.id */), _13G/* Motion.Change.lvl7 */));
              }),new T(function(){
                return B(_uj/* Core.Ease.opLift */(_in/* GHC.Float.divideDouble */, new T2(2,_14T/* s85h */,_2E/* GHC.Base.id */), _13G/* Motion.Change.lvl7 */));
              })),new T(function(){
                return B(_13V/* s83g */(_14e/* s83V */, _13u/* Motion.Change.lvl10 */));
              }),_7/* GHC.Tuple.() */)));
            });
            return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,_13E/* Motion.Change.lvl6 */,_14S/* s85p */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_14a/* s83S */,new T2(0,new T2(0,_14R/* s85r */,_14v/* s84t */),_14d/* s83U */.b)));
        });
      };
      return new T1(0,_14f/* s85v */);
    };
    return new F(function(){return A1(_13U/* s83f */,_14b/* s85w */);});
  };
  return E(_149/* s85x */);
},
_14U/* lvl37 */ = 0.1,
_14V/* lvl38 */ = new T1(0,_14U/* Motion.Main.lvl37 */),
_14W/* lvl39 */ = new T4(0,_14V/* Motion.Main.lvl38 */,_II/* Motion.Main.lvl30 */,_II/* Motion.Main.lvl30 */,_u4/* Motion.Main.lvl9 */),
_14X/* lvl40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Change"));
}),
_14Y/* lvl41 */ = new T(function(){
  return B(_AB/* Motion.Main.$wconsView */(_14W/* Motion.Main.lvl39 */, _13R/* Motion.Change.changeMot1 */, _14X/* Motion.Main.lvl40 */));
}),
_14Z/* lvl42 */ = 0.5,
_150/* lvl43 */ = new T1(0,_14Z/* Motion.Main.lvl42 */),
_151/* lvl44 */ = new T4(0,_u4/* Motion.Main.lvl9 */,_150/* Motion.Main.lvl43 */,_sA/* Motion.Main.lvl4 */,_u4/* Motion.Main.lvl9 */),
_152/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Trot"));
}),
_153/* cubic */ = function(_154/* slb1 */, _155/* slb2 */){
  var _156/* slb3 */ = B(A1(_154/* slb1 */,_155/* slb2 */));
  return _156/* slb3 */*_156/* slb3 */*_156/* slb3 */;
},
_157/* dur */ = 40,
_158/* $we */ = function(_159/* s5dv */, _15a/* s5dw */){
  if(_15a/* s5dw */>=0.5){
    var _15b/* s5dz */ = 2-(_15a/* s5dw */+_15a/* s5dw */);
    return 1-B(A1(_159/* s5dv */,_15b/* s5dz */*_15b/* s5dz */*(3-_15b/* s5dz */)/2))/2;
  }else{
    var _15c/* s5dJ */ = _15a/* s5dw */+_15a/* s5dw */;
    return B(A1(_159/* s5dv */,_15c/* s5dJ */*_15c/* s5dJ */*(3-_15c/* s5dJ */)/2))/2;
  }
},
_15d/* e */ = function(_15e/* s5dR */, _15f/* s5dS */){
  return new F(function(){return _158/* Motion.Trot.$we */(_15e/* s5dR */, E(_15f/* s5dS */));});
},
_15g/* x */ = 0,
_15h/* lvl */ = new T1(0,_15g/* Motion.Trot.x */),
_15i/* lvl10 */ = -100,
_15j/* lvl11 */ = new T1(0,_15i/* Motion.Trot.lvl10 */),
_15k/* lvl12 */ = -200,
_15l/* lvl13 */ = new T1(0,_15k/* Motion.Trot.lvl12 */),
_15m/* lvl14 */ = new T2(0,_15j/* Motion.Trot.lvl11 */,_15l/* Motion.Trot.lvl13 */),
_15n/* lvl15 */ = new T4(0,_15g/* Motion.Trot.x */,_15g/* Motion.Trot.x */,_iq/* Core.Ease.ease2 */,_av/* GHC.Types.False */),
_15o/* lvl16 */ = new T2(0,_15g/* Motion.Trot.x */,_15n/* Motion.Trot.lvl15 */),
_15p/* lvl17 */ = new T2(0,_15o/* Motion.Trot.lvl16 */,_6/* GHC.Types.[] */),
_15q/* a3 */ = 25,
_15r/* lvl3 */ = new T1(0,_15q/* Motion.Trot.a3 */),
_15s/* a4 */ = 125,
_15t/* lvl4 */ = new T1(0,_15s/* Motion.Trot.a4 */),
_15u/* a5 */ = 75,
_15v/* lvl5 */ = new T1(0,_15u/* Motion.Trot.a5 */),
_15w/* lvl6 */ = new T(function(){
  var _15x/* s5dW */ = B(_rM/* Core.Shape.Internal.$wrect */(_15r/* Motion.Trot.lvl3 */, _15t/* Motion.Trot.lvl4 */, _15v/* Motion.Trot.lvl5 */, _15v/* Motion.Trot.lvl5 */));
  return new T3(0,_15x/* s5dW */.a,_15x/* s5dW */.b,_15x/* s5dW */.c);
}),
_15y/* lvl7 */ = 1.5707963267948966,
_15z/* lvl8 */ = -75,
_15A/* a1 */ = 100,
_15B/* lvl1 */ = new T1(0,_15A/* Motion.Trot.a1 */),
_15C/* a2 */ = 200,
_15D/* lvl2 */ = new T1(0,_15C/* Motion.Trot.a2 */),
_15E/* lvl9 */ = new T2(0,_15B/* Motion.Trot.lvl1 */,_15D/* Motion.Trot.lvl2 */),
_15F/* trotMot */ = function(_15G/* s5e0 */){
  var _15H/* s5e1 */ = new T(function(){
    return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,_15m/* Motion.Trot.lvl14 */,new T(function(){
      return B(_ro/* Core.Render.Internal.fill1 */(_15G/* s5e0 */, _15w/* Motion.Trot.lvl6 */));
    }),_7/* GHC.Tuple.() */)));
  }),
  _15I/* s5fa */ = function(_15J/* s5e4 */, _15K/* s5e5 */){
    var _15L/* s5f9 */ = function(_/* EXTERNAL */){
      var _15M/* s5e7 */ = nMV/* EXTERNAL */(_15p/* Motion.Trot.lvl17 */),
      _15N/* s5e9 */ = _15M/* s5e7 */,
      _15O/* s5eb */ = new T(function(){
        return B(_wJ/* Core.Ease.$wforceTo */(_15N/* s5e9 */, _15g/* Motion.Trot.x */));
      }),
      _15P/* s5ec */ = function(_15Q/* s5ed */){
        return new F(function(){return _iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _157/* Motion.Trot.dur */, _153/* Core.Ease.cubic */, _15N/* s5e9 */, _15y/* Motion.Trot.lvl7 */, function(_15R/* s5ee */){
          return E(_15Q/* s5ed */);
        });});
      },
      _15S/* s5f7 */ = function(_/* EXTERNAL */){
        var _15T/* s5eh */ = nMV/* EXTERNAL */(_15p/* Motion.Trot.lvl17 */),
        _15U/* s5ej */ = _15T/* s5eh */;
        return new T(function(){
          var _15V/* s5el */ = new T(function(){
            return B(_wJ/* Core.Ease.$wforceTo */(_15U/* s5ej */, _15g/* Motion.Trot.x */));
          }),
          _15W/* s5em */ = function(_15X/* s5en */){
            return new F(function(){return _iB/* Core.Ease.$weaseHandle */(_id/* Core.Ease.$fMorphDouble_$clerp */, _157/* Motion.Trot.dur */, _15d/* Motion.Trot.e */, _15U/* s5ej */, _15z/* Motion.Trot.lvl8 */, function(_15Y/* s5eo */){
              return E(_15X/* s5en */);
            });});
          },
          _15Z/* s5eq */ = function(_160/* s5er */){
            var _161/* s5es */ = new T(function(){
              return B(A1(_15O/* s5eb */,_160/* s5er */));
            }),
            _162/* s5eS */ = function(_163/* s5et */){
              var _164/* s5eu */ = function(_165/* s5ev */){
                return new F(function(){return A2(_15Z/* s5eq */,E(_165/* s5ev */).b, _163/* s5et */);});
              },
              _166/* s5ez */ = function(_167/* s5eA */){
                return new T1(0,B(_Ba/* Core.World.Internal.$wa6 */(_15W/* s5em */, E(_167/* s5eA */).b, _164/* s5eu */)));
              },
              _168/* s5eG */ = function(_169/* s5eH */){
                return new T1(0,B(_Ba/* Core.World.Internal.$wa6 */(_15P/* s5ec */, E(_169/* s5eH */).b, _166/* s5ez */)));
              };
              return new F(function(){return A1(_161/* s5es */,function(_16a/* s5eN */){
                return new F(function(){return A2(_15V/* s5el */,E(_16a/* s5eN */).b, _168/* s5eG */);});
              });});
            };
            return E(_162/* s5eS */);
          },
          _16b/* s5f3 */ = new T(function(){
            var _16c/* s5f1 */ = new T(function(){
              return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,_15E/* Motion.Trot.lvl9 */,new T(function(){
                return B(_pg/* Control.Monad.Skeleton.bone */(new T3(6,new T2(2,new T3(0,_157/* Motion.Trot.dur */,_153/* Core.Ease.cubic */,_15N/* s5e9 */),_2E/* GHC.Base.id */),_15H/* s5e1 */,_7/* GHC.Tuple.() */)));
              }),_7/* GHC.Tuple.() */)));
            });
            return B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,new T2(2,new T3(0,_157/* Motion.Trot.dur */,_15d/* Motion.Trot.e */,_15U/* s5ej */),_2E/* GHC.Base.id */),_15h/* Motion.Trot.lvl */),_16c/* s5f1 */,_7/* GHC.Tuple.() */)));
          });
          return B(A1(_15K/* s5e5 */,new T2(0,new T2(0,_16b/* s5f3 */,_15Z/* s5eq */),_15J/* s5e4 */)));
        });
      };
      return new T1(0,_15S/* s5f7 */);
    };
    return new T1(0,_15L/* s5f9 */);
  };
  return E(_15I/* s5fa */);
},
_16d/* lvl46 */ = new T(function(){
  return B(_AB/* Motion.Main.$wconsView */(_151/* Motion.Main.lvl44 */, _15F/* Motion.Trot.trotMot */, _152/* Motion.Main.lvl45 */));
}),
_16e/* lvl47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("height"));
}),
_16f/* lvl48 */ = 1,
_16g/* lvl49 */ = new T1(1,_6/* GHC.Types.[] */),
_16h/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.scale(x,y);})");
}),
_16i/* f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,rad){ctx.rotate(rad);})");
}),
_16j/* f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,x,y){ctx.translate(x,y);})");
}),
_16k/* f4 */ = new T(function(){
  return eval/* EXTERNAL */("(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})");
}),
_16l/* render2 */ = function(_16m/*  sFRJ */, _16n/*  sFRK */, _/* EXTERNAL */){
  while(1){
    var _16o/*  render2 */ = B((function(_16p/* sFRJ */, _16q/* sFRK */, _/* EXTERNAL */){
      var _16r/* sFRM */ = B(_fo/* Control.Monad.Skeleton.debone */(_16p/* sFRJ */));
      if(!_16r/* sFRM */._){
        return _16r/* sFRM */.a;
      }else{
        var _16s/* sFRP */ = _16r/* sFRM */.b,
        _16t/* sFRQ */ = E(_16r/* sFRM */.a);
        switch(_16t/* sFRQ */._){
          case 0:
            var _16u/* sFRT */ = B(A2(_16t/* sFRQ */.a,_16q/* sFRK */, _/* EXTERNAL */)),
            _16v/*   sFRK */ = _16q/* sFRK */;
            _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16t/* sFRQ */.b));
            _16n/*  sFRK */ = _16v/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 1:
            var _16w/* sFRY */ = B(A1(_16t/* sFRQ */.a,_/* EXTERNAL */)),
            _16v/*   sFRK */ = _16q/* sFRK */;
            _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16w/* sFRY */));
            _16n/*  sFRK */ = _16v/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 2:
            var _16v/*   sFRK */ = _16q/* sFRK */;
            _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16t/* sFRQ */.b));
            _16n/*  sFRK */ = _16v/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 3:
            var _16x/* sFS8 */ = B(_16l/* Core.Render.Internal.render2 */(_16t/* sFRQ */.b, _16t/* sFRQ */.a, _/* EXTERNAL */)),
            _16v/*   sFRK */ = _16q/* sFRK */;
            _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16t/* sFRQ */.c));
            _16n/*  sFRK */ = _16v/*   sFRK */;
            return __continue/* EXTERNAL */;
          case 4:
            var _16y/* sFSj */ = _16t/* sFRQ */.h,
            _16z/* sFSk */ = function(_16A/* sFSl */, _/* EXTERNAL */){
              var _16B/* sFTp */ = function(_16C/* sFSn */, _/* EXTERNAL */){
                var _16D/* sFTo */ = function(_16E/* sFSp */, _/* EXTERNAL */){
                  var _16F/* sFTn */ = function(_16G/* sFSr */, _/* EXTERNAL */){
                    var _16H/* sFTm */ = function(_16I/* sFSt */, _/* EXTERNAL */){
                      return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_16t/* sFRQ */.f, function(_16J/* sFSv */, _/* EXTERNAL */){
                        var _16K/* sFSx */ = E(_16q/* sFRK */),
                        _16L/* sFSC */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _16K/* sFSx */),
                        _16M/* sFT9 */ = __apply/* EXTERNAL */(E(_16k/* Core.Render.Internal.f4 */), new T2(1,E(_16J/* sFSv */),new T2(1,E(_16I/* sFSt */),new T2(1,E(_16G/* sFSr */),new T2(1,E(_16E/* sFSp */),new T2(1,E(_16C/* sFSn */),new T2(1,E(_16A/* sFSl */),new T2(1,_16K/* sFSx */,_6/* GHC.Types.[] */)))))))),
                        _16N/* sFTc */ = B(_16l/* Core.Render.Internal.render2 */(_16t/* sFRQ */.g, _16K/* sFSx */, _/* EXTERNAL */)),
                        _16O/* sFTi */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), _16K/* sFSx */);
                        return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
                      }, _/* EXTERNAL */);});
                    };
                    return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_16t/* sFRQ */.e, _16H/* sFTm */, _/* EXTERNAL */);});
                  };
                  return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_16t/* sFRQ */.d, _16F/* sFTn */, _/* EXTERNAL */);});
                };
                return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_16t/* sFRQ */.c, _16D/* sFTo */, _/* EXTERNAL */);});
              };
              return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_16t/* sFRQ */.b, _16B/* sFTp */, _/* EXTERNAL */);});
            },
            _16P/* sFTq */ = E(_16t/* sFRQ */.a);
            switch(_16P/* sFTq */._){
              case 0:
                var _16Q/* sFTs */ = B(_16z/* sFSk */(_16P/* sFTq */.a, _/* EXTERNAL */)),
                _16v/*   sFRK */ = _16q/* sFRK */;
                _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16y/* sFSj */));
                _16n/*  sFRK */ = _16v/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _16R/* sFTx */ = B(A1(_16P/* sFTq */.a,_/* EXTERNAL */)),
                _16S/* sFTA */ = B(_16z/* sFSk */(_16R/* sFTx */, _/* EXTERNAL */)),
                _16v/*   sFRK */ = _16q/* sFRK */;
                _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16y/* sFSj */));
                _16n/*  sFRK */ = _16v/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _16T/* sFTM */ = rMV/* EXTERNAL */(E(E(_16P/* sFTq */.a).c)),
                _16U/* sFTP */ = E(_16T/* sFTM */);
                if(!_16U/* sFTP */._){
                  var _16V/* sFTT */ = new T(function(){
                    return B(A1(_16P/* sFTq */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_16U/* sFTP */.a));
                    })));
                  },1),
                  _16W/* sFTU */ = B(_16z/* sFSk */(_16V/* sFTT */, _/* EXTERNAL */)),
                  _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16y/* sFSj */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16y/* sFSj */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _16X/* sFU8 */ = rMV/* EXTERNAL */(E(E(_16P/* sFTq */.a).c)),
                _16Y/* sFUb */ = E(_16X/* sFU8 */);
                if(!_16Y/* sFUb */._){
                  var _16Z/* sFUh */ = B(A2(_16P/* sFTq */.b,E(_16Y/* sFUb */.a).a, _/* EXTERNAL */)),
                  _170/* sFUk */ = B(_16z/* sFSk */(_16Z/* sFUh */, _/* EXTERNAL */)),
                  _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16y/* sFSj */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16y/* sFSj */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 5:
            var _171/* sFUs */ = _16t/* sFRQ */.c,
            _172/* sFUt */ = E(_16t/* sFRQ */.a),
            _173/* sFUw */ = function(_174/* sFUx */, _/* EXTERNAL */){
              return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_172/* sFUt */.b, function(_175/* sFUz */, _/* EXTERNAL */){
                var _176/* sFUB */ = E(_16q/* sFRK */),
                _177/* sFUG */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _176/* sFUB */),
                _178/* sFUU */ = __app3/* EXTERNAL */(E(_16j/* Core.Render.Internal.f3 */), _176/* sFUB */, E(_174/* sFUx */), E(_175/* sFUz */)),
                _179/* sFUX */ = B(_16l/* Core.Render.Internal.render2 */(_16t/* sFRQ */.b, _176/* sFUB */, _/* EXTERNAL */)),
                _17a/* sFV3 */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), _176/* sFUB */);
                return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _17b/* sFV7 */ = E(_172/* sFUt */.a);
            switch(_17b/* sFV7 */._){
              case 0:
                var _17c/* sFV9 */ = B(_173/* sFUw */(_17b/* sFV7 */.a, _/* EXTERNAL */)),
                _16v/*   sFRK */ = _16q/* sFRK */;
                _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_171/* sFUs */));
                _16n/*  sFRK */ = _16v/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _17d/* sFVe */ = B(A1(_17b/* sFV7 */.a,_/* EXTERNAL */)),
                _17e/* sFVh */ = B(_173/* sFUw */(_17d/* sFVe */, _/* EXTERNAL */)),
                _16v/*   sFRK */ = _16q/* sFRK */;
                _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_171/* sFUs */));
                _16n/*  sFRK */ = _16v/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _17f/* sFVt */ = rMV/* EXTERNAL */(E(E(_17b/* sFV7 */.a).c)),
                _17g/* sFVw */ = E(_17f/* sFVt */);
                if(!_17g/* sFVw */._){
                  var _17h/* sFVA */ = new T(function(){
                    return B(A1(_17b/* sFV7 */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_17g/* sFVw */.a));
                    })));
                  },1),
                  _17i/* sFVB */ = B(_173/* sFUw */(_17h/* sFVA */, _/* EXTERNAL */)),
                  _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_171/* sFUs */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_171/* sFUs */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _17j/* sFVP */ = rMV/* EXTERNAL */(E(E(_17b/* sFV7 */.a).c)),
                _17k/* sFVS */ = E(_17j/* sFVP */);
                if(!_17k/* sFVS */._){
                  var _17l/* sFVY */ = B(A2(_17b/* sFV7 */.b,E(_17k/* sFVS */.a).a, _/* EXTERNAL */)),
                  _17m/* sFW1 */ = B(_173/* sFUw */(_17l/* sFVY */, _/* EXTERNAL */)),
                  _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_171/* sFUs */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_171/* sFUs */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 6:
            var _17n/* sFW9 */ = _16t/* sFRQ */.c,
            _17o/* sFWa */ = function(_17p/* sFWb */, _/* EXTERNAL */){
              var _17q/* sFWd */ = E(_16q/* sFRK */),
              _17r/* sFWi */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _17q/* sFWd */),
              _17s/* sFWs */ = __app2/* EXTERNAL */(E(_16i/* Core.Render.Internal.f2 */), _17q/* sFWd */, E(_17p/* sFWb */)),
              _17t/* sFWv */ = B(_16l/* Core.Render.Internal.render2 */(_16t/* sFRQ */.b, _17q/* sFWd */, _/* EXTERNAL */)),
              _17u/* sFWB */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), _17q/* sFWd */);
              return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
            },
            _17v/* sFWE */ = E(_16t/* sFRQ */.a);
            switch(_17v/* sFWE */._){
              case 0:
                var _17w/* sFWG */ = B(_17o/* sFWa */(_17v/* sFWE */.a, _/* EXTERNAL */)),
                _16v/*   sFRK */ = _16q/* sFRK */;
                _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17n/* sFW9 */));
                _16n/*  sFRK */ = _16v/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _17x/* sFWL */ = B(A1(_17v/* sFWE */.a,_/* EXTERNAL */)),
                _17y/* sFWO */ = B(_17o/* sFWa */(_17x/* sFWL */, _/* EXTERNAL */)),
                _16v/*   sFRK */ = _16q/* sFRK */;
                _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17n/* sFW9 */));
                _16n/*  sFRK */ = _16v/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _17z/* sFX0 */ = rMV/* EXTERNAL */(E(E(_17v/* sFWE */.a).c)),
                _17A/* sFX3 */ = E(_17z/* sFX0 */);
                if(!_17A/* sFX3 */._){
                  var _17B/* sFX7 */ = new T(function(){
                    return B(A1(_17v/* sFWE */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_17A/* sFX3 */.a));
                    })));
                  },1),
                  _17C/* sFX8 */ = B(_17o/* sFWa */(_17B/* sFX7 */, _/* EXTERNAL */)),
                  _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17n/* sFW9 */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17n/* sFW9 */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _17D/* sFXm */ = rMV/* EXTERNAL */(E(E(_17v/* sFWE */.a).c)),
                _17E/* sFXp */ = E(_17D/* sFXm */);
                if(!_17E/* sFXp */._){
                  var _17F/* sFXv */ = B(A2(_17v/* sFWE */.b,E(_17E/* sFXp */.a).a, _/* EXTERNAL */)),
                  _17G/* sFXy */ = B(_17o/* sFWa */(_17F/* sFXv */, _/* EXTERNAL */)),
                  _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17n/* sFW9 */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17n/* sFW9 */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          case 7:
            var _17H/* sFXG */ = _16t/* sFRQ */.c,
            _17I/* sFXH */ = E(_16t/* sFRQ */.a),
            _17J/* sFXK */ = function(_17K/* sFXL */, _/* EXTERNAL */){
              return new F(function(){return _ps/* Core.Render.Internal.getImage2 */(_17I/* sFXH */.b, function(_17L/* sFXN */, _/* EXTERNAL */){
                var _17M/* sFXP */ = E(_16q/* sFRK */),
                _17N/* sFXU */ = __app1/* EXTERNAL */(E(_pr/* Core.Render.Internal.clip_f4 */), _17M/* sFXP */),
                _17O/* sFY8 */ = __app3/* EXTERNAL */(E(_16h/* Core.Render.Internal.f1 */), _17M/* sFXP */, E(_17K/* sFXL */), E(_17L/* sFXN */)),
                _17P/* sFYb */ = B(_16l/* Core.Render.Internal.render2 */(_16t/* sFRQ */.b, _17M/* sFXP */, _/* EXTERNAL */)),
                _17Q/* sFYh */ = __app1/* EXTERNAL */(E(_ph/* Core.Render.Internal.clip_f1 */), _17M/* sFXP */);
                return new F(function(){return _jl/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
              }, _/* EXTERNAL */);});
            },
            _17R/* sFYl */ = E(_17I/* sFXH */.a);
            switch(_17R/* sFYl */._){
              case 0:
                var _17S/* sFYn */ = B(_17J/* sFXK */(_17R/* sFYl */.a, _/* EXTERNAL */)),
                _16v/*   sFRK */ = _16q/* sFRK */;
                _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17H/* sFXG */));
                _16n/*  sFRK */ = _16v/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 1:
                var _17T/* sFYs */ = B(A1(_17R/* sFYl */.a,_/* EXTERNAL */)),
                _17U/* sFYv */ = B(_17J/* sFXK */(_17T/* sFYs */, _/* EXTERNAL */)),
                _16v/*   sFRK */ = _16q/* sFRK */;
                _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17H/* sFXG */));
                _16n/*  sFRK */ = _16v/*   sFRK */;
                return __continue/* EXTERNAL */;
              case 2:
                var _17V/* sFYH */ = rMV/* EXTERNAL */(E(E(_17R/* sFYl */.a).c)),
                _17W/* sFYK */ = E(_17V/* sFYH */);
                if(!_17W/* sFYK */._){
                  var _17X/* sFYO */ = new T(function(){
                    return B(A1(_17R/* sFYl */.b,new T(function(){
                      return B(_fB/* Data.Tuple.fst */(_17W/* sFYK */.a));
                    })));
                  },1),
                  _17Y/* sFYP */ = B(_17J/* sFXK */(_17X/* sFYO */, _/* EXTERNAL */)),
                  _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17H/* sFXG */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17H/* sFXG */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
                break;
              default:
                var _17Z/* sFZ3 */ = rMV/* EXTERNAL */(E(E(_17R/* sFYl */.a).c)),
                _180/* sFZ6 */ = E(_17Z/* sFZ3 */);
                if(!_180/* sFZ6 */._){
                  var _181/* sFZc */ = B(A2(_17R/* sFYl */.b,E(_180/* sFZ6 */.a).a, _/* EXTERNAL */)),
                  _182/* sFZf */ = B(_17J/* sFXK */(_181/* sFZc */, _/* EXTERNAL */)),
                  _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17H/* sFXG */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }else{
                  var _16v/*   sFRK */ = _16q/* sFRK */;
                  _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_17H/* sFXG */));
                  _16n/*  sFRK */ = _16v/*   sFRK */;
                  return __continue/* EXTERNAL */;
                }
            }
            break;
          default:
            var _183/* sFZo */ = B(_16l/* Core.Render.Internal.render2 */(_16t/* sFRQ */.a, _16q/* sFRK */, _/* EXTERNAL */)),
            _16v/*   sFRK */ = _16q/* sFRK */;
            _16m/*  sFRJ */ = B(A1(_16s/* sFRP */,_16t/* sFRQ */.c));
            _16n/*  sFRK */ = _16v/*   sFRK */;
            return __continue/* EXTERNAL */;
        }
      }
    })(_16m/*  sFRJ */, _16n/*  sFRK */, _/* EXTERNAL */));
    if(_16o/*  render2 */!=__continue/* EXTERNAL */){
      return _16o/*  render2 */;
    }
  }
},
_184/* a12 */ = new T1(0,_/* EXTERNAL */),
_185/* a13 */ = new T1(0,_6/* GHC.Types.[] */),
_186/* a14 */ = new T2(0,E(_185/* Motion.Main.a13 */),E(_184/* Motion.Main.a12 */)),
_187/* pad */ = 40,
_188/* lvl1 */ = new T1(0,_187/* Motion.Main.pad */),
_189/* rendering1 */ = function(_18a/* sWcL */){
  return E(E(_18a/* sWcL */).b);
},
_18b/* renderContents_go */ = function(_18c/* s7zC */, _18d/* s7zD */){
  var _18e/* s7zE */ = E(_18c/* s7zC */);
  if(!_18e/* s7zE */._){
    return E(_186/* Motion.Main.a14 */);
  }else{
    var _18f/* s7zH */ = E(_18d/* s7zD */);
    if(!_18f/* s7zH */._){
      return E(_186/* Motion.Main.a14 */);
    }else{
      var _18g/* s7zU */ = B(_pg/* Control.Monad.Skeleton.bone */(new T3(5,new T2(0,_188/* Motion.Main.lvl1 */,new T1(0,new T(function(){
        return 40+240*E(_18e/* s7zE */.a);
      }))),new T(function(){
        return B(_189/* Core.View.rendering1 */(_18f/* s7zH */.a));
      }),_7/* GHC.Tuple.() */))),
      _18h/* s7zX */ = new T(function(){
        return B(_18b/* Motion.Main.renderContents_go */(_18e/* s7zE */.b, _18f/* s7zH */.b));
      }),
      _18i/* s7A8 */ = function(_18j/* s7zY */){
        var _18k/* s7zZ */ = E(_18h/* s7zX */);
        return new T2(0,E(_18k/* s7zZ */.a),E(new T2(2,_18k/* s7zZ */.b,new T1(1,function(_18l/* s7A2 */){
          return new T2(0,E(new T1(0,new T2(1,_18j/* s7zY */,_18l/* s7A2 */))),E(_184/* Motion.Main.a12 */));
        }))));
      };
      return new T2(0,E(_18g/* s7zU */.a),E(new T2(2,_18g/* s7zU */.b,new T1(1,_18i/* s7A8 */))));
    }
  }
},
_18m/* renderContents1 */ = function(_18n/* s7Ab */){
  return new F(function(){return _p8/* Control.Monad.Skeleton.$fFunctorSkeleton_$c<$ */(_7/* GHC.Tuple.() */, new T(function(){
    return B(_18b/* Motion.Main.renderContents_go */(_HQ/* Core.Util.iforM1 */, _18n/* s7Ab */));
  }));});
},
_18o/* launch1 */ = function(_18p/* s7Bx */, _18q/* s7By */){
  var _18r/* s7Bz */ = function(_18s/* s7BA */, _/* EXTERNAL */){
    var _18t/* s7BC */ = E(_18p/* s7Bx */),
    _18u/* s7BI */ = __app1/* EXTERNAL */(E(_ib/* Haste.Graphics.Canvas.buffer_f1 */), _18t/* s7BC */.b);
    return new F(function(){return _16l/* Core.Render.Internal.render2 */(B(_18m/* Motion.Main.renderContents1 */(_18s/* s7BA */)), _18t/* s7BC */.a, _/* EXTERNAL */);});
  },
  _18v/* s7BN */ = new T(function(){
    return B(A1(_Fz/* Motion.Main.lvl28 */,_18q/* s7By */));
  }),
  _18w/* s7DA */ = function(_18x/* s7BO */){
    var _18y/* s7Dz */ = function(_18z/* s7BP */){
      var _18A/* s7BQ */ = E(_18z/* s7BP */),
      _18B/* s7Dy */ = function(_18C/* s7BT */){
        var _18D/* s7BU */ = E(_18C/* s7BT */),
        _18E/* s7Dx */ = function(_18F/* s7BX */){
          var _18G/* s7BY */ = E(_18F/* s7BX */),
          _18H/* s7Dw */ = function(_18I/* s7C1 */){
            var _18J/* s7C2 */ = E(_18I/* s7C1 */),
            _18K/* s7Dv */ = function(_18L/* s7C5 */){
              var _18M/* s7C6 */ = E(_18L/* s7C5 */),
              _18N/* s7Cd */ = new T2(1,_18A/* s7BQ */.a,new T2(1,_18D/* s7BU */.a,new T2(1,_18G/* s7BY */.a,new T2(1,_18J/* s7C2 */.a,new T2(1,_18M/* s7C6 */.a,_6/* GHC.Types.[] */))))),
              _18O/* s7Du */ = function(_/* EXTERNAL */){
                var _18P/* s7Cs */ = jsShow/* EXTERNAL */(40+B(_eT/* GHC.List.$wlenAcc */(_18N/* s7Cd */, 0))*240),
                _18Q/* s7CE */ = __app3/* EXTERNAL */(E(_ic/* Haste.DOM.Core.jsSet_f1 */), E(_18p/* s7Bx */).b, toJSStr/* EXTERNAL */(E(_16e/* Motion.Main.lvl47 */)), toJSStr/* EXTERNAL */(fromJSStr/* EXTERNAL */(_18P/* s7Cs */))),
                _18R/* s7Ds */ = function(_/* EXTERNAL */){
                  var _18S/* s7CJ */ = nMV/* EXTERNAL */(new T2(0,_18N/* s7Cd */,_6/* GHC.Types.[] */));
                  return new T(function(){
                    var _18T/* s7CN */ = new T(function(){
                      return B(_9I/* Core.Util.$wwithMVar */(_8l/* Core.World.Internal.$fMonadConcWorld */, _18S/* s7CJ */, _eY/* Motion.Main.a22 */));
                    }),
                    _18U/* s7CP */ = function(_18V/* s7CV */){
                      return new F(function(){return _18W/* s7CS */(E(_18V/* s7CV */).b);});
                    },
                    _18X/* s7CQ */ = function(_18Y/* s7CZ */){
                      return new F(function(){return _BY/* Core.World.Internal.sleep1 */(_16f/* Motion.Main.lvl48 */, E(_18Y/* s7CZ */).b, _18U/* s7CP */);});
                    },
                    _18Z/* s7CR */ = function(_190/* s7D3 */){
                      var _191/* s7D4 */ = E(_190/* s7D3 */);
                      return new F(function(){return A(_fU/* Core.Render.Internal.applyTransform_world */,[B(_18m/* Motion.Main.renderContents1 */(_191/* s7D4 */.a)), _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f2/* Core.Render.Internal.applyTransform1 */, _f3/* Core.Render.Internal.applyTransform2 */, _f2/* Core.Render.Internal.applyTransform1 */, _191/* s7D4 */.b, _18X/* s7CQ */]);});
                    },
                    _18W/* s7CS */ = function(_192/* s7D8 */){
                      return new F(function(){return A2(_18T/* s7CN */,_192/* s7D8 */, _18Z/* s7CR */);});
                    },
                    _193/* s7Do */ = function(_194/* s7D9 */){
                      var _195/* s7Dc */ = E(_194/* s7D9 */).b,
                      _196/* s7Dn */ = function(_/* EXTERNAL */){
                        var _197/* s7De */ = nMV/* EXTERNAL */(_16g/* Motion.Main.lvl49 */);
                        return new T1(1,new T2(1,new T(function(){
                          return B(A1(_18x/* s7BO */,new T2(0,_7/* GHC.Tuple.() */,_195/* s7Dc */)));
                        }),new T2(1,new T(function(){
                          return B(_18W/* s7CS */(_195/* s7Dc */));
                        }),_6/* GHC.Types.[] */)));
                      };
                      return new T1(0,_196/* s7Dn */);
                    };
                    return new T1(0,B(_e8/* Core.Front.Internal.$wa */(_18S/* s7CJ */, _18r/* s7Bz */, _18M/* s7C6 */.b, _193/* s7Do */)));
                  });
                };
                return new T1(0,_18R/* s7Ds */);
              };
              return new T1(0,_18O/* s7Du */);
            };
            return new F(function(){return A2(_16d/* Motion.Main.lvl46 */,_18J/* s7C2 */.b, _18K/* s7Dv */);});
          };
          return new F(function(){return A2(_14Y/* Motion.Main.lvl41 */,_18G/* s7BY */.b, _18H/* s7Dw */);});
        };
        return new F(function(){return A2(_Yo/* Motion.Main.lvl36 */,_18D/* s7BU */.b, _18E/* s7Dx */);});
      };
      return new F(function(){return A2(_IL/* Motion.Main.lvl33 */,_18A/* s7BQ */.b, _18B/* s7Dy */);});
    };
    return new F(function(){return A1(_18v/* s7BN */,_18y/* s7Dz */);});
  };
  return E(_18w/* s7DA */);
},
_198/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Canvas not found!"));
}),
_199/* main2 */ = new T(function(){
  return B(err/* EXTERNAL */(_198/* Main.lvl */));
}),
_19a/* main3 */ = "canvas",
_19b/* start_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(Util.onload)");
}),
_19c/* main1 */ = function(_/* EXTERNAL */){
  var _19d/* s11fh */ = __app1/* EXTERNAL */(E(_19b/* Core.Front.Internal.start_f1 */), E(_48/* Haste.Prim.Any.jsNull */)),
  _19e/* s11fk */ = B(A3(_e1/* Haste.DOM.JSString.elemById */,_2G/* Control.Monad.IO.Class.$fMonadIOIO */, _19a/* Main.main3 */, _/* EXTERNAL */)),
  _19f/* s11fn */ = E(_19e/* s11fk */);
  if(!_19f/* s11fn */._){
    return E(_199/* Main.main2 */);
  }else{
    var _19g/* s11fq */ = E(_19f/* s11fn */.a),
    _19h/* s11fv */ = __app1/* EXTERNAL */(E(_1/* Haste.Graphics.Canvas.$fFromAnyCanvas_f2 */), _19g/* s11fq */);
    if(!_19h/* s11fv */){
      return E(_199/* Main.main2 */);
    }else{
      var _19i/* s11fD */ = __app1/* EXTERNAL */(E(_0/* Haste.Graphics.Canvas.$fFromAnyCanvas_f1 */), _19g/* s11fq */),
      _19j/* s11fF */ = _19i/* s11fD */,
      _19k/* s11fK */ = new T(function(){
        return new T1(0,B(_d7/* Core.World.Internal.$wa5 */(function(_19l/* B1 */){
          return new F(function(){return _18o/* Motion.Main.launch1 */(new T2(0,_19j/* s11fF */,_19g/* s11fq */), _19l/* B1 */);});
        }, _2I/* Haste.Concurrent.Monad.forkIO1 */)));
      });
      return new F(function(){return _e/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(_19k/* s11fK */, _6/* GHC.Types.[] */, _/* EXTERNAL */);});
    }
  }
},
_19m/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _19c/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_19m, [0]));};window.onload = hasteMain;