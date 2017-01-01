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

var _0=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_2=function(_3,_4){var _5=E(_3);return (_5._==0)?E(_4):new T2(1,_5.a,new T(function(){return B(_2(_5.b,_4));}));},_6=__Z,_7=0,_8=function(_9,_){while(1){var _a=E(_9);if(!_a._){return _7;}else{var _b=_a.b,_c=E(_a.a);switch(_c._){case 0:var _d=B(A1(_c.a,_));_9=B(_2(_b,new T2(1,_d,_6)));continue;case 1:_9=B(_2(_b,_c.a));continue;default:_9=_b;continue;}}}},_e=function(_f,_g,_){var _h=E(_f);switch(_h._){case 0:var _i=B(A1(_h.a,_));return new F(function(){return _8(B(_2(_g,new T2(1,_i,_6))),_);});break;case 1:return new F(function(){return _8(B(_2(_g,_h.a)),_);});break;default:return new F(function(){return _8(_g,_);});}},_j=function(_k,_l,_){var _m=B(A1(_k,_)),_n=B(A1(_l,_));return _m;},_o=function(_p,_q,_){var _r=B(A1(_p,_)),_s=B(A1(_q,_));return new T(function(){return B(A1(_r,_s));});},_t=function(_u,_v,_){var _w=B(A1(_v,_));return _u;},_x=function(_y,_z,_){var _A=B(A1(_z,_));return new T(function(){return B(A1(_y,_A));});},_B=new T2(0,_x,_t),_C=function(_D,_){return _D;},_E=function(_F,_G,_){var _H=B(A1(_F,_));return new F(function(){return A1(_G,_);});},_I=new T5(0,_B,_C,_o,_E,_j),_J=new T(function(){return B(unCStr("base"));}),_K=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_L=new T(function(){return B(unCStr("IOException"));}),_M=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_J,_K,_L),_N=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_M,_6,_6),_O=function(_P){return E(_N);},_Q=function(_R){return E(E(_R).a);},_S=function(_T,_U,_V){var _W=B(A1(_T,_)),_X=B(A1(_U,_)),_Y=hs_eqWord64(_W.a,_X.a);if(!_Y){return __Z;}else{var _Z=hs_eqWord64(_W.b,_X.b);return (!_Z)?__Z:new T1(1,_V);}},_10=function(_11){var _12=E(_11);return new F(function(){return _S(B(_Q(_12.a)),_O,_12.b);});},_13=new T(function(){return B(unCStr(": "));}),_14=new T(function(){return B(unCStr(")"));}),_15=new T(function(){return B(unCStr(" ("));}),_16=new T(function(){return B(unCStr("interrupted"));}),_17=new T(function(){return B(unCStr("system error"));}),_18=new T(function(){return B(unCStr("unsatisified constraints"));}),_19=new T(function(){return B(unCStr("user error"));}),_1a=new T(function(){return B(unCStr("permission denied"));}),_1b=new T(function(){return B(unCStr("illegal operation"));}),_1c=new T(function(){return B(unCStr("end of file"));}),_1d=new T(function(){return B(unCStr("resource exhausted"));}),_1e=new T(function(){return B(unCStr("resource busy"));}),_1f=new T(function(){return B(unCStr("does not exist"));}),_1g=new T(function(){return B(unCStr("already exists"));}),_1h=new T(function(){return B(unCStr("resource vanished"));}),_1i=new T(function(){return B(unCStr("timeout"));}),_1j=new T(function(){return B(unCStr("unsupported operation"));}),_1k=new T(function(){return B(unCStr("hardware fault"));}),_1l=new T(function(){return B(unCStr("inappropriate type"));}),_1m=new T(function(){return B(unCStr("invalid argument"));}),_1n=new T(function(){return B(unCStr("failed"));}),_1o=new T(function(){return B(unCStr("protocol error"));}),_1p=function(_1q,_1r){switch(E(_1q)){case 0:return new F(function(){return _2(_1g,_1r);});break;case 1:return new F(function(){return _2(_1f,_1r);});break;case 2:return new F(function(){return _2(_1e,_1r);});break;case 3:return new F(function(){return _2(_1d,_1r);});break;case 4:return new F(function(){return _2(_1c,_1r);});break;case 5:return new F(function(){return _2(_1b,_1r);});break;case 6:return new F(function(){return _2(_1a,_1r);});break;case 7:return new F(function(){return _2(_19,_1r);});break;case 8:return new F(function(){return _2(_18,_1r);});break;case 9:return new F(function(){return _2(_17,_1r);});break;case 10:return new F(function(){return _2(_1o,_1r);});break;case 11:return new F(function(){return _2(_1n,_1r);});break;case 12:return new F(function(){return _2(_1m,_1r);});break;case 13:return new F(function(){return _2(_1l,_1r);});break;case 14:return new F(function(){return _2(_1k,_1r);});break;case 15:return new F(function(){return _2(_1j,_1r);});break;case 16:return new F(function(){return _2(_1i,_1r);});break;case 17:return new F(function(){return _2(_1h,_1r);});break;default:return new F(function(){return _2(_16,_1r);});}},_1s=new T(function(){return B(unCStr("}"));}),_1t=new T(function(){return B(unCStr("{handle: "));}),_1u=function(_1v,_1w,_1x,_1y,_1z,_1A){var _1B=new T(function(){var _1C=new T(function(){var _1D=new T(function(){var _1E=E(_1y);if(!_1E._){return E(_1A);}else{var _1F=new T(function(){return B(_2(_1E,new T(function(){return B(_2(_14,_1A));},1)));},1);return B(_2(_15,_1F));}},1);return B(_1p(_1w,_1D));}),_1G=E(_1x);if(!_1G._){return E(_1C);}else{return B(_2(_1G,new T(function(){return B(_2(_13,_1C));},1)));}}),_1H=E(_1z);if(!_1H._){var _1I=E(_1v);if(!_1I._){return E(_1B);}else{var _1J=E(_1I.a);if(!_1J._){var _1K=new T(function(){var _1L=new T(function(){return B(_2(_1s,new T(function(){return B(_2(_13,_1B));},1)));},1);return B(_2(_1J.a,_1L));},1);return new F(function(){return _2(_1t,_1K);});}else{var _1M=new T(function(){var _1N=new T(function(){return B(_2(_1s,new T(function(){return B(_2(_13,_1B));},1)));},1);return B(_2(_1J.a,_1N));},1);return new F(function(){return _2(_1t,_1M);});}}}else{return new F(function(){return _2(_1H.a,new T(function(){return B(_2(_13,_1B));},1));});}},_1O=function(_1P){var _1Q=E(_1P);return new F(function(){return _1u(_1Q.a,_1Q.b,_1Q.c,_1Q.d,_1Q.f,_6);});},_1R=function(_1S){return new T2(0,_1T,_1S);},_1U=function(_1V,_1W,_1X){var _1Y=E(_1W);return new F(function(){return _1u(_1Y.a,_1Y.b,_1Y.c,_1Y.d,_1Y.f,_1X);});},_1Z=function(_20,_21){var _22=E(_20);return new F(function(){return _1u(_22.a,_22.b,_22.c,_22.d,_22.f,_21);});},_23=44,_24=93,_25=91,_26=function(_27,_28,_29){var _2a=E(_28);if(!_2a._){return new F(function(){return unAppCStr("[]",_29);});}else{var _2b=new T(function(){var _2c=new T(function(){var _2d=function(_2e){var _2f=E(_2e);if(!_2f._){return E(new T2(1,_24,_29));}else{var _2g=new T(function(){return B(A2(_27,_2f.a,new T(function(){return B(_2d(_2f.b));})));});return new T2(1,_23,_2g);}};return B(_2d(_2a.b));});return B(A2(_27,_2a.a,_2c));});return new T2(1,_25,_2b);}},_2h=function(_2i,_2j){return new F(function(){return _26(_1Z,_2i,_2j);});},_2k=new T3(0,_1U,_1O,_2h),_1T=new T(function(){return new T5(0,_O,_2k,_1R,_10,_1O);}),_2l=new T(function(){return E(_1T);}),_2m=function(_2n){return E(E(_2n).c);},_2o=__Z,_2p=7,_2q=function(_2r){return new T6(0,_2o,_2p,_6,_2r,_2o,_2o);},_2s=function(_2t,_){var _2u=new T(function(){return B(A2(_2m,_2l,new T(function(){return B(A1(_2q,_2t));})));});return new F(function(){return die(_2u);});},_2v=function(_2w,_){return new F(function(){return _2s(_2w,_);});},_2x=function(_2y){return new F(function(){return A1(_2v,_2y);});},_2z=function(_2A,_2B,_){var _2C=B(A1(_2A,_));return new F(function(){return A2(_2B,_2C,_);});},_2D=new T5(0,_I,_2z,_E,_C,_2x),_2E=function(_2F){return E(_2F);},_2G=new T2(0,_2D,_2E),_2H=new T0(2),_2I=function(_2J){return new T0(2);},_2K=function(_2L,_2M,_2N){return function(_){var _2O=E(_2L),_2P=rMV(_2O),_2Q=E(_2P);if(!_2Q._){var _2R=new T(function(){var _2S=new T(function(){return B(A1(_2N,_7));});return B(_2(_2Q.b,new T2(1,new T2(0,_2M,function(_2T){return E(_2S);}),_6)));}),_=wMV(_2O,new T2(0,_2Q.a,_2R));return _2H;}else{var _2U=E(_2Q.a);if(!_2U._){var _=wMV(_2O,new T2(0,_2M,_6));return new T(function(){return B(A1(_2N,_7));});}else{var _=wMV(_2O,new T1(1,_2U.b));return new T1(1,new T2(1,new T(function(){return B(A1(_2N,_7));}),new T2(1,new T(function(){return B(A2(_2U.a,_2M,_2I));}),_6)));}}};},_2V=function(_2W){return E(E(_2W).b);},_2X=function(_2Y,_2Z,_30){var _31=new T(function(){return new T1(0,B(_2K(_2Z,_30,_2I)));}),_32=function(_33){return new T1(1,new T2(1,new T(function(){return B(A1(_33,_7));}),new T2(1,_31,_6)));};return new F(function(){return A2(_2V,_2Y,_32);});},_34="deltaZ",_35="deltaY",_36="deltaX",_37=function(_38,_39){var _3a=jsShowI(_38);return new F(function(){return _2(fromJSStr(_3a),_39);});},_3b=41,_3c=40,_3d=function(_3e,_3f,_3g){if(_3f>=0){return new F(function(){return _37(_3f,_3g);});}else{if(_3e<=6){return new F(function(){return _37(_3f,_3g);});}else{return new T2(1,_3c,new T(function(){var _3h=jsShowI(_3f);return B(_2(fromJSStr(_3h),new T2(1,_3b,_3g)));}));}}},_3i=new T(function(){return B(unCStr(")"));}),_3j=new T(function(){return B(_3d(0,2,_3i));}),_3k=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_3j));}),_3l=function(_3m){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_3d(0,_3m,_3k));}))));});},_3n=function(_3o,_){return new T(function(){var _3p=Number(E(_3o)),_3q=jsTrunc(_3p);if(_3q<0){return B(_3l(_3q));}else{if(_3q>2){return B(_3l(_3q));}else{return _3q;}}});},_3r=0,_3s=new T3(0,_3r,_3r,_3r),_3t="button",_3u=new T(function(){return eval("jsGetMouseCoords");}),_3v=function(_3w,_){var _3x=E(_3w);if(!_3x._){return _6;}else{var _3y=B(_3v(_3x.b,_));return new T2(1,new T(function(){var _3z=Number(E(_3x.a));return jsTrunc(_3z);}),_3y);}},_3A=function(_3B,_){var _3C=__arr2lst(0,_3B);return new F(function(){return _3v(_3C,_);});},_3D=function(_3E,_){return new F(function(){return _3A(E(_3E),_);});},_3F=function(_3G,_){return new T(function(){var _3H=Number(E(_3G));return jsTrunc(_3H);});},_3I=new T2(0,_3F,_3D),_3J=function(_3K,_){var _3L=E(_3K);if(!_3L._){return _6;}else{var _3M=B(_3J(_3L.b,_));return new T2(1,_3L.a,_3M);}},_3N=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_3O=new T6(0,_2o,_2p,_6,_3N,_2o,_2o),_3P=new T(function(){return B(_1R(_3O));}),_3Q=function(_){return new F(function(){return die(_3P);});},_3R=function(_3S){return E(E(_3S).a);},_3T=function(_3U,_3V,_3W,_){var _3X=__arr2lst(0,_3W),_3Y=B(_3J(_3X,_)),_3Z=E(_3Y);if(!_3Z._){return new F(function(){return _3Q(_);});}else{var _40=E(_3Z.b);if(!_40._){return new F(function(){return _3Q(_);});}else{if(!E(_40.b)._){var _41=B(A3(_3R,_3U,_3Z.a,_)),_42=B(A3(_3R,_3V,_40.a,_));return new T2(0,_41,_42);}else{return new F(function(){return _3Q(_);});}}}},_43=function(_){return new F(function(){return __jsNull();});},_44=function(_45){var _46=B(A1(_45,_));return E(_46);},_47=new T(function(){return B(_44(_43));}),_48=new T(function(){return E(_47);}),_49=function(_4a,_4b,_){if(E(_4a)==7){var _4c=__app1(E(_3u),_4b),_4d=B(_3T(_3I,_3I,_4c,_)),_4e=__get(_4b,E(_36)),_4f=__get(_4b,E(_35)),_4g=__get(_4b,E(_34));return new T(function(){return new T3(0,E(_4d),E(_2o),E(new T3(0,_4e,_4f,_4g)));});}else{var _4h=__app1(E(_3u),_4b),_4i=B(_3T(_3I,_3I,_4h,_)),_4j=__get(_4b,E(_3t)),_4k=__eq(_4j,E(_48));if(!E(_4k)){var _4l=B(_3n(_4j,_));return new T(function(){return new T3(0,E(_4i),E(new T1(1,_4l)),E(_3s));});}else{return new T(function(){return new T3(0,E(_4i),E(_2o),E(_3s));});}}},_4m=function(_4n,_4o,_){return new F(function(){return _49(_4n,E(_4o),_);});},_4p="mouseout",_4q="mouseover",_4r="mousemove",_4s="mouseup",_4t="mousedown",_4u="dblclick",_4v="click",_4w="wheel",_4x=function(_4y){switch(E(_4y)){case 0:return E(_4v);case 1:return E(_4u);case 2:return E(_4t);case 3:return E(_4s);case 4:return E(_4r);case 5:return E(_4q);case 6:return E(_4p);default:return E(_4w);}},_4z=new T2(0,_4x,_4m),_4A=function(_4B,_){return new T1(1,_4B);},_4C=new T2(0,_2E,_4A),_4D=function(_4E){var _4F=E(_4E);return new T0(2);},_4G=function(_4H,_4I,_4J){return new T1(1,new T2(1,new T(function(){return B(A1(_4J,new T2(0,_7,_4I)));}),new T2(1,new T(function(){return B(A2(_4H,_4I,_4D));}),_6)));},_4K=function(_4L,_4M,_4N){var _4O=new T(function(){return B(A1(_4L,_4N));}),_4P=function(_4Q){var _4R=function(_4S){var _4T=E(_4S);return new F(function(){return A2(_4M,_4T.b,function(_4U){return new F(function(){return A1(_4Q,new T2(0,_4T.a,E(_4U).b));});});});};return new F(function(){return A1(_4O,_4R);});};return E(_4P);},_4V=function(_4W,_4X,_4Y){var _4Z=new T(function(){return B(A1(_4W,_4Y));}),_50=function(_51){var _52=function(_53){return new F(function(){return A1(_51,E(_53));});};return new F(function(){return A1(_4Z,function(_54){return new F(function(){return A2(_4X,E(_54).b,_52);});});});};return E(_50);},_55=function(_56,_57,_58){var _59=new T(function(){return B(A1(_56,_58));}),_5a=function(_5b){var _5c=function(_5d){var _5e=E(_5d),_5f=function(_5g){var _5h=E(_5g);return new F(function(){return A1(_5b,new T2(0,new T(function(){return B(A1(_5e.a,_5h.a));}),_5h.b));});};return new F(function(){return A2(_57,_5e.b,_5f);});};return new F(function(){return A1(_59,_5c);});};return E(_5a);},_5i=function(_5j,_5k,_5l){var _5m=new T(function(){return B(A1(_5k,_5l));}),_5n=function(_5o){var _5p=function(_5q){return new F(function(){return A1(_5o,new T(function(){return new T2(0,_5j,E(_5q).b);}));});};return new F(function(){return A1(_5m,_5p);});};return E(_5n);},_5r=function(_5s,_5t,_5u){var _5v=new T(function(){return B(A1(_5t,_5u));}),_5w=function(_5x){var _5y=function(_5z){var _5A=new T(function(){var _5B=E(_5z);return new T2(0,new T(function(){return B(A1(_5s,_5B.a));}),_5B.b);});return new F(function(){return A1(_5x,_5A);});};return new F(function(){return A1(_5v,_5y);});};return E(_5w);},_5C=new T2(0,_5r,_5i),_5D=function(_5E,_5F,_5G){return new F(function(){return A1(_5G,new T2(0,_5E,_5F));});},_5H=new T5(0,_5C,_5D,_55,_4V,_4K),_5I=function(_5J,_5K){return new F(function(){return err(_5J);});},_5L=function(_5M,_5N,_5O){return new F(function(){return A1(_5M,function(_5P){return new F(function(){return A2(_5N,_5P,_5O);});});});},_5Q=function(_5R,_5S,_5T){var _5U=function(_5V){var _5W=new T(function(){return B(A1(_5T,_5V));});return new F(function(){return A1(_5S,function(_5X){return E(_5W);});});};return new F(function(){return A1(_5R,_5U);});},_5Y=function(_5Z,_60,_61){var _62=new T(function(){return B(A1(_60,function(_63){return new F(function(){return A1(_61,_63);});}));});return new F(function(){return A1(_5Z,function(_64){return E(_62);});});},_65=function(_66,_67,_68){var _69=function(_6a){var _6b=function(_6c){return new F(function(){return A1(_68,new T(function(){return B(A1(_6a,_6c));}));});};return new F(function(){return A1(_67,_6b);});};return new F(function(){return A1(_66,_69);});},_6d=function(_6e,_6f){return new F(function(){return A1(_6f,_6e);});},_6g=function(_6h,_6i,_6j){var _6k=new T(function(){return B(A1(_6j,_6h));});return new F(function(){return A1(_6i,function(_6l){return E(_6k);});});},_6m=function(_6n,_6o,_6p){var _6q=function(_6r){return new F(function(){return A1(_6p,new T(function(){return B(A1(_6n,_6r));}));});};return new F(function(){return A1(_6o,_6q);});},_6s=new T2(0,_6m,_6g),_6t=new T5(0,_6s,_6d,_65,_5Y,_5Q),_6u=function(_6v){return E(E(_6v).b);},_6w=function(_6x,_6y){return new F(function(){return A3(_6u,_6z,_6x,function(_6A){return E(_6y);});});},_6B=function(_6C){return new F(function(){return err(_6C);});},_6z=new T(function(){return new T5(0,_6t,_5L,_6w,_6d,_6B);}),_6D=function(_6E,_6F,_6G,_6H,_6I){return new F(function(){return A3(_6u,_6F,new T(function(){return B(A1(_6G,_6I));}),function(_6J){var _6K=E(_6J);return new F(function(){return A2(_6H,_6K.a,_6K.b);});});});},_6L=function(_6M){return E(E(_6M).e);},_6N=function(_6O,_6P,_6Q){var _6R=new T(function(){return B(A2(_6L,_6P,_6Q));});return function(_6S){return E(_6R);};},_6T=function(_6U){return E(E(_6U).d);},_6V=function(_6W,_6X){return new T5(0,_6W,function(_6Y,_6Z,_70){return new F(function(){return _6D(_6W,_6X,_6Y,_6Z,_70);});},function(_6Z,_70){return new F(function(){return _71(_6W,_6X,_6Z,_70);});},function(_72,_73){return new F(function(){return A2(_6T,_6X,new T2(0,_72,_73));});},function(_70){return new F(function(){return _6N(_6W,_6X,_70);});});},_71=function(_74,_75,_76,_77){return new F(function(){return A3(_6u,B(_6V(_74,_75)),_76,function(_78){return E(_77);});});},_79=function(_7a,_7b,_7c){var _7d=new T(function(){return B(A1(_7b,_7c));}),_7e=function(_7f){var _7g=function(_7h){return new F(function(){return A1(_7f,new T(function(){return new T2(0,_7a,E(_7h).b);}));});};return new F(function(){return A1(_7d,_7g);});};return E(_7e);},_7i=function(_7j,_7k,_7l){var _7m=new T(function(){return B(A1(_7k,_7l));}),_7n=function(_7o){var _7p=function(_7q){var _7r=new T(function(){var _7s=E(_7q);return new T2(0,new T(function(){return B(A1(_7j,_7s.a));}),_7s.b);});return new F(function(){return A1(_7o,_7r);});};return new F(function(){return A1(_7m,_7p);});};return E(_7n);},_7t=new T2(0,_7i,_79),_7u=function(_7v,_7w,_7x){var _7y=new T(function(){return B(A1(_7v,_7x));}),_7z=function(_7A){var _7B=function(_7C){var _7D=E(_7C),_7E=function(_7F){var _7G=E(_7F);return new F(function(){return A1(_7A,new T2(0,new T(function(){return B(A1(_7D.a,_7G.a));}),_7G.b));});};return new F(function(){return A2(_7w,_7D.b,_7E);});};return new F(function(){return A1(_7y,_7B);});};return E(_7z);},_7H=function(_7I,_7J,_7K){var _7L=new T(function(){return B(A1(_7I,_7K));}),_7M=function(_7N){var _7O=function(_7P){return new F(function(){return A1(_7N,E(_7P));});};return new F(function(){return A1(_7L,function(_7Q){return new F(function(){return A2(_7J,E(_7Q).b,_7O);});});});};return E(_7M);},_7R=function(_7S,_7T,_7U){var _7V=new T(function(){return B(A1(_7S,_7U));}),_7W=function(_7X){var _7Y=function(_7Z){var _80=E(_7Z);return new F(function(){return A2(_7T,_80.b,function(_81){return new F(function(){return A1(_7X,new T2(0,_80.a,E(_81).b));});});});};return new F(function(){return A1(_7V,_7Y);});};return E(_7W);},_82=new T5(0,_7t,_5D,_7u,_7H,_7R),_83=function(_84,_85){return new F(function(){return _71(_82,_6z,_84,_85);});},_86=function(_87,_88,_89){var _8a=new T(function(){return B(A1(_87,_89));}),_8b=function(_8c){return new F(function(){return A1(_8a,function(_8d){var _8e=E(_8d);return new F(function(){return A3(_88,_8e.a,_8e.b,_8c);});});});};return E(_8b);},_8f=new T5(0,_5H,_86,_83,_5D,_5I),_8g=function(_8h,_8i,_8j){return new F(function(){return A1(_8h,function(_8k){return new F(function(){return A1(_8j,new T2(0,_8k,_8i));});});});},_8l=new T3(0,_8f,_8g,_4G),_8m=function(_8n,_8o,_8p){var _8q=function(_8r,_){return new F(function(){return _e(new T(function(){return B(A3(_8n,_8r,_8o,_4D));}),_6,_);});};return new F(function(){return A1(_8p,new T2(0,_8q,_8o));});},_8s=function(_8t,_8u,_8v){var _8w=function(_){var _8x=B(A1(_8t,_));return new T(function(){return B(A1(_8v,new T2(0,_8x,_8u)));});};return new T1(0,_8w);},_8y=new T2(0,_8f,_8s),_8z=new T2(0,_8y,_8m),_8A=new T1(1,_6),_8B=function(_8C,_8D){return function(_){var _8E=E(_8C),_8F=rMV(_8E),_8G=E(_8F);if(!_8G._){var _8H=_8G.a,_8I=E(_8G.b);if(!_8I._){var _=wMV(_8E,_8A);return new T(function(){return B(A1(_8D,_8H));});}else{var _8J=E(_8I.a),_=wMV(_8E,new T2(0,_8J.a,_8I.b));return new T1(1,new T2(1,new T(function(){return B(A1(_8D,_8H));}),new T2(1,new T(function(){return B(A1(_8J.b,_2I));}),_6)));}}else{var _8K=new T(function(){var _8L=function(_8M){var _8N=new T(function(){return B(A1(_8D,_8M));});return function(_8O){return E(_8N);};};return B(_2(_8G.a,new T2(1,_8L,_6)));}),_=wMV(_8E,new T1(1,_8K));return _2H;}};},_8P=new T2(0,_2G,_C),_8Q=function(_8R){return E(E(_8R).a);},_8S=function(_8T){return E(E(_8T).a);},_8U=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_8V=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_8W=function(_8X){return E(E(_8X).b);},_8Y=function(_8Z){return E(E(_8Z).b);},_90=function(_91,_92,_93){var _94=B(_8Q(_91)),_95=new T(function(){return B(_8W(_94));}),_96=function(_97){var _98=function(_){var _99=E(_92);if(!_99._){var _9a=B(A1(_97,_7)),_9b=__createJSFunc(0,function(_){var _9c=B(A1(_9a,_));return _48;}),_9d=__app2(E(_8V),_99.a,_9b);return new T(function(){var _9e=Number(_9d),_9f=jsTrunc(_9e);return new T2(0,_9f,E(_99));});}else{var _9g=B(A1(_97,_7)),_9h=__createJSFunc(0,function(_){var _9i=B(A1(_9g,_));return _48;}),_9j=__app2(E(_8U),_99.a,_9h);return new T(function(){var _9k=Number(_9j),_9l=jsTrunc(_9k);return new T2(0,_9l,E(_99));});}};return new F(function(){return A1(_95,_98);});},_9m=new T(function(){return B(A2(_8Y,_91,function(_9n){return E(_93);}));});return new F(function(){return A3(_6u,B(_8S(_94)),_9m,_96);});},_9o=new T1(1,_6),_9p=function(_9q,_9r){return function(_){var _9s=nMV(_9o),_9t=_9s,_9u=function(_){var _9v=function(_){return new F(function(){return _e(new T(function(){return new T1(0,B(_2K(_9t,_7,_2I)));}),_6,_);});},_9w=B(A(_90,[_8P,new T(function(){return new T1(0,E(_9q));}),_9v,_]));return new T(function(){return new T1(0,B(_8B(_9t,_9r)));});};return new T1(0,_9u);};},_9x=function(_9y){return E(E(_9y).a);},_9z=function(_9A){return E(E(_9A).c);},_9B=function(_9C,_9D,_9E){return new T1(0,B(_2K(_9C,_9D,_9E)));},_9F=function(_9G,_9H){return new T1(0,B(_8B(_9G,_9H)));},_9I=function(_9J,_9K,_9L){var _9M=new T(function(){return B(_2V(_9J));}),_9N=B(_9x(_9J)),_9O=function(_9P,_9Q){var _9R=new T(function(){return B(A1(_9M,function(_9S){return new F(function(){return _9B(_9K,_9Q,_9S);});}));});return new F(function(){return A3(_9z,_9N,_9R,new T(function(){return B(A2(_6T,_9N,_9P));}));});},_9T=function(_9U){var _9V=E(_9U);return new F(function(){return _9O(_9V.a,_9V.b);});},_9W=function(_9X){return new F(function(){return A3(_6u,_9N,new T(function(){return B(A1(_9L,_9X));}),_9T);});},_9Y=new T(function(){return B(A2(_2V,_9J,function(_9S){return new F(function(){return _9F(_9K,_9S);});}));});return new F(function(){return A3(_6u,_9N,_9Y,_9W);});},_9Z=function(_a0,_a1,_a2){return new F(function(){return A1(_a2,new T2(0,new T2(0,new T(function(){return E(E(_a0).a);}),_a0),_a1));});},_a3=16,_a4=function(_a5,_a6,_a7){var _a8=E(_a5);if(!_a8._){return new F(function(){return A1(_a7,new T2(0,_6,_a6));});}else{var _a9=function(_aa){var _ab=E(_aa);return new F(function(){return _a4(_a8.b,_ab.b,function(_ac){var _ad=E(_ac);return new F(function(){return A1(_a7,new T2(0,new T2(1,_ab.a,_ad.a),_ad.b));});});});};return new F(function(){return A2(E(_a8.a).a,_a6,_a9);});}},_ae=function(_af,_ag,_ah){var _ai=E(_af);if(!_ai._){return new F(function(){return A1(_ah,new T2(0,_6,_ag));});}else{var _aj=E(_ai.a),_ak=function(_al){var _am=E(_al),_an=function(_ao){var _ap=E(_ao),_aq=_ap.a;return new F(function(){return A1(_ah,new T2(0,new T(function(){if(!E(_am.a)){return E(_aq);}else{return new T2(1,_aj,_aq);}}),_ap.b));});};return new F(function(){return _ae(_ai.b,_am.b,_an);});};return new F(function(){return A2(_aj.b,_ag,_ak);});}},_ar=function(_as,_at,_au){return new F(function(){return A1(_au,new T2(0,new T2(0,new T(function(){return E(_as).b;}),_as),_at));});},_av=false,_aw=true,_ax=function(_ay,_az,_aA){return new F(function(){return A1(_aA,new T2(0,new T2(0,new T(function(){var _aB=E(E(_ay).c);if(!_aB._){return __Z;}else{return new T1(1,_aB.b);}}),_ay),_az));});},_aC=__Z,_aD=function(_aE,_aF,_aG,_aH){var _aI=E(_aH);switch(_aI._){case 0:return new T3(2,_aF,_aG,_aC);case 1:return new T3(2,_aF,_aG,_aI.a);default:var _aJ=_aI.a,_aK=_aI.b,_aL=_aI.c;return new T1(1,new T(function(){if(!B(A2(_aE,_aF,_aJ))){return B(_aD(_aE,_aJ,new T3(0,_aF,_aG,_aK),_aL));}else{return B(_aD(_aE,_aF,new T3(0,_aJ,_aK,_aG),_aL));}}));}},_aM=function(_aN,_aO){var _aP=E(_aO);switch(_aP._){case 0:return __Z;case 1:var _aQ=B(_aM(_aN,_aP.a));if(!_aQ._){return __Z;}else{var _aR=E(_aQ.b);return new T3(1,_aQ.a,_aR.c,new T3(2,_aR.a,_aR.b,_aQ.c));}break;default:var _aS=_aP.a,_aT=_aP.b,_aU=_aP.c,_aV=B(_aM(_aN,_aU));if(!_aV._){return new T3(1,_aS,_aT,new T1(1,_aU));}else{var _aW=_aV.a,_aX=_aV.c;if(!B(A2(_aN,_aS,_aW))){var _aY=E(_aV.b),_aZ=_aY.a,_b0=_aY.b;return new T3(1,_aW,_aY.c,new T1(1,new T(function(){if(!B(A2(_aN,_aS,_aZ))){return B(_aD(_aN,_aZ,new T3(0,_aS,_aT,_b0),_aX));}else{return B(_aD(_aN,_aS,new T3(0,_aZ,_b0,_aT),_aX));}})));}else{return new T3(1,_aS,_aT,new T1(1,_aU));}}}},_b1=function(_b2){var _b3=new T(function(){var _b4=E(_b2),_b5=E(_b4.c);if(!_b5._){var _b6=__Z;}else{var _b7=B(_aM(function(_b8,_b9){var _ba=E(E(_b8).a),_bb=E(E(_b9).a);return (_ba>=_bb)?_ba==_bb:true;},_b5.c));if(!_b7._){var _bc=__Z;}else{var _bc=new T3(1,_b5.a-1|0,_b7.a,E(_b7.c));}var _b6=_bc;}return new T4(0,E(_b4.a),_b4.b,E(_b6),E(_b4.d));});return function(_bd,_be){return new F(function(){return A1(_be,new T2(0,new T2(0,_7,_b3),_bd));});};},_bf=function(_bg,_bh,_bi){return new F(function(){return A1(_bi,new T2(0,new T2(0,_7,new T(function(){var _bj=E(_bg);return new T4(0,E(_bj.a),_bj.b+1|0,E(_bj.c),E(_bj.d));})),_bh));});},_bk=function(_bl,_bm){return new T1(0,B(_bn(_bl)));},_bo=function(_bp){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_bp));}))));});},_bq=new T(function(){return B(_bo("w_saRG ((), MVar WorldState) -> Action"));}),_br=function(_bs){return new F(function(){return _bk(E(_bs).b,_bq);});},_bt=function(_bu){var _bv=E(_bu).b;return new F(function(){return A(_9I,[_8l,_bv,_bf,_bv,_br]);});},_bw=function(_bx,_by){var _bz=new T(function(){return B(A2(_6T,_bx,_7));}),_bA=new T(function(){return B(_bw(_bx,_by));});return new F(function(){return A3(_6u,_bx,_by,function(_bB){return (!E(_bB))?E(_bz):E(_bA);});});},_bC=function(_bD){var _bE=E(_bD),_bF=function(_bG,_bH){var _bI=function(_bJ){return new F(function(){return A1(_bH,new T2(0,_aw,E(_bJ).b));});},_bK=function(_bL){var _bM=E(_bL),_bN=_bM.b,_bO=E(_bM.a);if(!_bO._){return new F(function(){return A1(_bH,new T2(0,_av,_bN));});}else{var _bP=E(_bO.a);if(E(_bP.a)<=E(_bE.a)){var _bQ=new T(function(){return B(A(_9I,[_8l,_bN,_b1,_bN,_bI]));});return new T1(0,B(_2K(_bP.b,_7,function(_bR){return E(_bQ);})));}else{return new F(function(){return A1(_bH,new T2(0,_av,_bN));});}}};return new F(function(){return A(_9I,[_8l,_bG,_ax,_bG,_bK]);});};return new F(function(){return A(_bw,[_8f,_bF,_bE.b,_bt]);});},_bS=function(_bT){var _bU=E(_bT).b;return new F(function(){return A(_9I,[_8l,_bU,_ar,_bU,_bC]);});},_bV=function(_bW){var _bX=E(_bW),_bY=_bX.b,_bZ=function(_c0,_c1,_c2){return new F(function(){return A1(_c2,new T2(0,new T2(0,_7,new T(function(){var _c3=E(_c0);return new T4(0,E(_bX.a),_c3.b,E(_c3.c),E(_c3.d));})),_c1));});};return new F(function(){return A(_9I,[_8l,_bY,_bZ,_bY,_bS]);});},_c4=function(_c5){var _c6=E(_c5),_c7=_c6.a;return new F(function(){return _a4(_c7,_c6.b,function(_c8){return new F(function(){return _ae(_c7,E(_c8).b,_bV);});});});},_bn=function(_c9){var _ca=new T(function(){return B(A(_9I,[_8l,_c9,_9Z,_c9,_c4]));});return new F(function(){return _9p(_a3,function(_cb){return E(_ca);});});},_cc=2,_cd=4,_ce=3,_cf=function(_cg,_ch,_ci){return new F(function(){return A1(_ci,new T2(0,new T2(0,new T(function(){return E(E(E(_cg).d).b);}),_cg),_ch));});},_cj=new T(function(){return eval("document");}),_ck=new T1(0,_av),_cl=new T1(0,_aw),_cm=new T1(1,_6),_cn=__Z,_co=new T0(2),_cp=0,_cq=new T2(0,_cp,_co),_cr=new T4(0,E(_6),0,E(_cn),E(_cq)),_cs=new T2(0,_cr,_6),_ct=function(_cu){return E(E(_cu).a);},_cv=function(_cw){return E(E(_cw).b);},_cx=function(_cy){return E(E(_cy).a);},_cz=function(_){return new F(function(){return nMV(_2o);});},_cA=new T(function(){return B(_44(_cz));}),_cB=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_cC=function(_cD,_cE,_cF,_cG,_cH,_cI){var _cJ=B(_8Q(_cD)),_cK=B(_8S(_cJ)),_cL=new T(function(){return B(_8W(_cJ));}),_cM=new T(function(){return B(_6T(_cK));}),_cN=new T(function(){return B(A2(_ct,_cE,_cG));}),_cO=new T(function(){return B(A2(_cx,_cF,_cH));}),_cP=function(_cQ){return new F(function(){return A1(_cM,new T3(0,_cO,_cN,_cQ));});},_cR=function(_cS){var _cT=new T(function(){var _cU=new T(function(){var _cV=__createJSFunc(2,function(_cW,_){var _cX=B(A2(E(_cS),_cW,_));return _48;}),_cY=_cV;return function(_){return new F(function(){return __app3(E(_cB),E(_cN),E(_cO),_cY);});};});return B(A1(_cL,_cU));});return new F(function(){return A3(_6u,_cK,_cT,_cP);});},_cZ=new T(function(){var _d0=new T(function(){return B(_8W(_cJ));}),_d1=function(_d2){var _d3=new T(function(){return B(A1(_d0,function(_){var _=wMV(E(_cA),new T1(1,_d2));return new F(function(){return A(_cv,[_cF,_cH,_d2,_]);});}));});return new F(function(){return A3(_6u,_cK,_d3,_cI);});};return B(A2(_8Y,_cD,_d1));});return new F(function(){return A3(_6u,_cK,_cZ,_cR);});},_d4=function(_d5,_d6){return new F(function(){return A1(_d6,new T2(0,_7,_d5));});},_d7=function(_d8,_d9){return function(_){var _da=nMV(_cs),_db=_da,_dc=function(_dd){return new F(function(){return A1(_d9,E(_dd).a);});},_de=function(_df){return new F(function(){return A2(_d8,E(_df).b,_dc);});},_dg=function(_){var _dh=nMV(_cm),_di=_dh,_dj=new T(function(){var _dk=function(_dl){return new F(function(){return _dm(E(_dl).b);});},_dm=function(_dn){var _do=function(_dp){var _dq=function(_dr){var _ds=E(_dr),_dt=_ds.b,_du=E(_dp),_dv=function(_dw,_dx,_dy){var _dz=function(_dA,_dB){while(1){var _dC=B((function(_dD,_dE){var _dF=E(_dE);switch(_dF._){case 0:_dA=new T(function(){return B(_dz(_dD,_dF.d));});_dB=_dF.c;return __continue;case 1:var _dG=new T(function(){return B(_2X(_8l,_dF.b,_dw));}),_dH=function(_dI){var _dJ=new T(function(){return B(A1(_dG,_dI));}),_dK=function(_dL){return new F(function(){return A1(_dJ,function(_dM){return new F(function(){return A2(_dD,E(_dM).b,_dL);});});});};return E(_dK);};return E(_dH);default:return E(_dD);}})(_dA,_dB));if(_dC!=__continue){return _dC;}}},_dN=E(_ds.a);if(!_dN._){var _dO=_dN.c,_dP=_dN.d;if(_dN.b>=0){return new F(function(){return A(_dz,[new T(function(){return B(_dz(_d4,_dP));}),_dO,_dx,_dy]);});}else{return new F(function(){return A(_dz,[new T(function(){return B(_dz(_d4,_dO));}),_dP,_dx,_dy]);});}}else{return new F(function(){return A(_dz,[_d4,_dN,_dx,_dy]);});}};switch(E(_du.a)){case 2:return new F(function(){return _dv(_cl,_dt,_dk);});break;case 3:return new F(function(){return _dv(_ck,_dt,_dk);});break;case 4:var _dQ=new T(function(){return E(E(_du.b).a);});return new F(function(){return _dv(new T1(1,new T2(0,new T(function(){return E(E(_dQ).a);}),new T(function(){return E(E(_dQ).b);}))),_dt,_dk);});break;default:return new F(function(){return _dm(_dt);});}};return new F(function(){return A(_9I,[_8l,_dn,_cf,_dn,_dq]);});};return new T1(0,B(_8B(_di,_do)));};return B(_dm(_db));}),_dR=new T(function(){var _dS=new T(function(){return B(_cC(_8z,_4C,_4z,_cj,_cd,function(_dT){return new F(function(){return _2X(_8l,_di,new T2(0,_cd,_dT));});}));}),_dU=new T(function(){return B(_cC(_8z,_4C,_4z,_cj,_ce,function(_dV){return new F(function(){return _2X(_8l,_di,new T2(0,_ce,_dV));});}));}),_dW=function(_dX){return new F(function(){return A2(_dU,E(_dX).b,_de);});};return B(A(_cC,[_8z,_4C,_4z,_cj,_cc,function(_dY){return new F(function(){return _2X(_8l,_di,new T2(0,_cc,_dY));});},_db,function(_dZ){return new F(function(){return A2(_dS,E(_dZ).b,_dW);});}]));});return new T1(1,new T2(1,_dR,new T2(1,_dj,_6)));};return new T1(1,new T2(1,new T1(0,_dg),new T2(1,new T(function(){return new T1(0,B(_bn(_db)));}),_6)));};},_e0=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_e1=function(_e2,_e3){var _e4=function(_){var _e5=__app1(E(_e0),E(_e3)),_e6=__eq(_e5,E(_48));return (E(_e6)==0)?new T1(1,_e5):_2o;};return new F(function(){return A2(_8W,_e2,_e4);});},_e7=new T(function(){return eval("window.requestAnimationFrame");}),_e8=function(_e9,_ea,_eb,_ec){return function(_){var _ed=E(_e9),_ee=rMV(_ed),_ef=E(_ee);if(!_ef._){var _eg=B(A2(_ea,_ef.a,_)),_eh=function(_ei,_){var _ej=function(_){var _ek=rMV(_ed),_el=function(_,_em){var _en=function(_){var _eo=__createJSFunc(2,function(_ep,_){var _eq=B(_er(_,_));return _48;}),_es=__app1(E(_e7),_eo);return _7;},_et=E(_em);if(!_et._){return new F(function(){return _en(_);});}else{var _eu=B(A2(_ea,_et.a,_));return new F(function(){return _en(_);});}},_ev=E(_ek);if(!_ev._){return new F(function(){return _el(_,new T1(1,_ev.a));});}else{return new F(function(){return _el(_,_2o);});}},_er=function(_ew,_){return new F(function(){return _ej(_);});},_ex=B(_er(_,_));return _48;},_ey=__createJSFunc(2,E(_eh)),_ez=__app1(E(_e7),_ey);return new T(function(){return B(A1(_ec,new T2(0,_7,_eb)));});}else{var _eA=function(_eB,_){var _eC=function(_){var _eD=rMV(_ed),_eE=function(_,_eF){var _eG=function(_){var _eH=__createJSFunc(2,function(_eI,_){var _eJ=B(_eK(_,_));return _48;}),_eL=__app1(E(_e7),_eH);return _7;},_eM=E(_eF);if(!_eM._){return new F(function(){return _eG(_);});}else{var _eN=B(A2(_ea,_eM.a,_));return new F(function(){return _eG(_);});}},_eO=E(_eD);if(!_eO._){return new F(function(){return _eE(_,new T1(1,_eO.a));});}else{return new F(function(){return _eE(_,_2o);});}},_eK=function(_eP,_){return new F(function(){return _eC(_);});},_eQ=B(_eK(_,_));return _48;},_eR=__createJSFunc(2,E(_eA)),_eS=__app1(E(_e7),_eR);return new T(function(){return B(A1(_ec,new T2(0,_7,_eb)));});}};},_eT=function(_eU,_eV){while(1){var _eW=E(_eU);if(!_eW._){return E(_eV);}else{var _eX=_eV+1|0;_eU=_eW.b;_eV=_eX;continue;}}},_eY=function(_eZ,_f0,_f1){return new F(function(){return A1(_f1,new T2(0,new T2(0,_eZ,_eZ),_f0));});},_f2=0,_f3=1,_f4=new T1(0,_),_f5=function(_f6,_f7,_f8){while(1){var _f9=B((function(_fa,_fb,_fc){var _fd=E(_fa);switch(_fd._){case 0:return new F(function(){return A1(_fb,_);});break;case 1:return new F(function(){return A2(_fc,_fd.a,_f4);});break;default:var _fe=_fd.b,_ff=function(_fg){var _fh=function(_fi){return new F(function(){return A1(_fb,new T(function(){var _fj=E(_fg),_fk=E(_fi);return _;}));});};return new F(function(){return _f5(_fe,_fh,new T(function(){var _fl=E(_fg);return E(_fc);}));});};_f6=_fd.a;_f7=_ff;_f8=function(_fm,_fn){return new F(function(){return A2(_fc,_fm,new T2(2,_fn,_fe));});};return __continue;}})(_f6,_f7,_f8));if(_f9!=__continue){return _f9;}}},_fo=function(_fp){var _fq=E(_fp),_fr=_fq.b,_fs=E(_fq.a);if(!_fs._){var _ft=_fs.a;return new F(function(){return _f5(_fr,function(_fu){var _fv=E(_fu);return new T1(0,_ft);},function(_fw,_fx){var _fy=B(A1(_fw,_ft));return new F(function(){return _fo(new T2(0,E(_fy.a),E(new T2(2,_fy.b,_fx))));});});});}else{return new T2(1,_fs.a,function(_fz){var _fA=B(A1(_fs.b,_fz));return new T2(0,E(_fA.a),E(new T2(2,_fA.b,_fr)));});}},_fB=function(_fC){return E(E(_fC).a);},_fD=function(_fE,_fF,_fG){var _fH=E(_fE);switch(_fH._){case 0:return new F(function(){return _5D(_fH.a,_fF,_fG);});break;case 1:return new F(function(){return _8s(_fH.a,_fF,_fG);});break;case 2:var _fI=E(_fH.a).c,_fJ=function(_fK){var _fL=new T(function(){var _fM=new T(function(){return B(A1(_fH.b,new T(function(){return B(_fB(_fK));})));});return B(A1(_fG,new T2(0,_fM,_fF)));});return new T1(0,B(_2K(_fI,_fK,function(_fN){return E(_fL);})));};return new T1(0,B(_8B(_fI,_fJ)));default:var _fO=E(_fH.a).c,_fP=function(_fQ){var _fR=function(_){var _fS=B(A2(_fH.b,new T(function(){return B(_fB(_fQ));}),_));return new T(function(){return B(A1(_fG,new T2(0,_fS,_fF)));});};return new T1(0,B(_2K(_fO,_fQ,function(_fT){return E(new T1(0,_fR));})));};return new T1(0,B(_8B(_fO,_fP)));}},_fU=function(_fV,_fW,_fX,_fY,_fZ,_g0,_g1){while(1){var _g2=B((function(_g3,_g4,_g5,_g6,_g7,_g8,_g9){var _ga=new T(function(){return 0*E(_g4)+0*E(_g5)+E(_g6);}),_gb=new T(function(){return 0*E(_g7)+0*E(_g8)+E(_g9);}),_gc=B(_fo(_g3));if(!_gc._){return function(_gd,_ge){return new F(function(){return _5D(_gc.a,_gd,_ge);});};}else{var _gf=_gc.b,_gg=E(_gc.a);switch(_gg._){case 0:var _gh=_g4,_gi=_g5,_gj=_g6,_gk=_g7,_gl=_g8,_gm=_g9;_fV=B(A1(_gf,_gg.b));_fW=_gh;_fX=_gi;_fY=_gj;_fZ=_gk;_g0=_gl;_g1=_gm;return __continue;case 1:var _gn=function(_go,_gp){var _gq=function(_){var _gr=B(A1(_gg.a,_));return new T(function(){return B(A(_fU,[B(A1(_gf,_gr)),_g4,_g5,_g6,_g7,_g8,_g9,_go,_gp]));});};return new T1(0,_gq);};return E(_gn);case 2:var _gs=new T(function(){return B(A(_gg.a,[_g4,_g5,_g6,_g7,_g8,_g9]));}),_gt=new T(function(){return B(_fU(B(A1(_gf,_gg.b)),_g4,_g5,_g6,_g7,_g8,_g9));}),_gu=function(_gv){var _gw=new T(function(){return B(A1(_gs,_gv));}),_gx=function(_gy){return new F(function(){return A1(_gw,function(_gz){return new F(function(){return A2(_gt,E(_gz).b,_gy);});});});};return E(_gx);};return E(_gu);case 3:var _gA=new T(function(){return B(_fU(_gg.b,_g4,_g5,_g6,_g7,_g8,_g9));}),_gB=new T(function(){return B(_fU(B(A1(_gf,_gg.c)),_g4,_g5,_g6,_g7,_g8,_g9));}),_gC=function(_gD){var _gE=new T(function(){return B(A1(_gA,_gD));}),_gF=function(_gG){return new F(function(){return A1(_gE,function(_gH){return new F(function(){return A2(_gB,E(_gH).b,_gG);});});});};return E(_gF);};return E(_gC);case 4:var _gI=new T(function(){return B(_fU(B(A1(_gf,_gg.h)),_g4,_g5,_g6,_g7,_g8,_g9));}),_gJ=function(_gK,_gL){var _gM=function(_gN){return new F(function(){return A2(_gI,E(_gN).b,_gL);});},_gO=function(_gP){var _gQ=E(_gP),_gR=_gQ.a,_gS=function(_gT){var _gU=E(_gT),_gV=_gU.a,_gW=function(_gX){var _gY=E(_gX),_gZ=_gY.a,_h0=function(_h1){var _h2=E(_h1),_h3=_h2.a,_h4=new T(function(){return E(_gR)*E(_g7)+E(_h3)*E(_g8);}),_h5=new T(function(){return E(_gR)*E(_g4)+E(_h3)*E(_g5);}),_h6=function(_h7){var _h8=E(_h7),_h9=_h8.a,_ha=new T(function(){return E(_gV)*E(_g7)+E(_h9)*E(_g8);}),_hb=new T(function(){return E(_gV)*E(_g4)+E(_h9)*E(_g5);}),_hc=function(_hd){var _he=E(_hd),_hf=_he.a;return new F(function(){return A(_fU,[_gg.g,_h5,_hb,new T(function(){return E(_gZ)*E(_g4)+E(_hf)*E(_g5)+E(_g6);}),_h4,_ha,new T(function(){return E(_gZ)*E(_g7)+E(_hf)*E(_g8)+E(_g9);}),_he.b,_gM]);});};return new F(function(){return _fD(_gg.f,_h8.b,_hc);});};return new F(function(){return _fD(_gg.e,_h2.b,_h6);});};return new F(function(){return _fD(_gg.d,_gY.b,_h0);});};return new F(function(){return _fD(_gg.c,_gU.b,_gW);});};return new F(function(){return _fD(_gg.b,_gQ.b,_gS);});};return new F(function(){return _fD(_gg.a,_gK,_gO);});};return E(_gJ);case 5:var _hg=E(_gg.a),_hh=new T(function(){return B(_fU(B(A1(_gf,_gg.c)),_g4,_g5,_g6,_g7,_g8,_g9));}),_hi=new T(function(){return 0*E(_g7)+E(_g8);}),_hj=new T(function(){return E(_g7)+0*E(_g8);}),_hk=new T(function(){return 0*E(_g4)+E(_g5);}),_hl=new T(function(){return E(_g4)+0*E(_g5);}),_hm=function(_hn,_ho){var _hp=function(_hq){return new F(function(){return A2(_hh,E(_hq).b,_ho);});},_hr=function(_hs){var _ht=E(_hs),_hu=_ht.a,_hv=function(_hw){var _hx=E(_hw),_hy=_hx.a;return new F(function(){return A(_fU,[_gg.b,_hl,_hk,new T(function(){return E(_hu)*E(_g4)+E(_hy)*E(_g5)+E(_g6);}),_hj,_hi,new T(function(){return E(_hu)*E(_g7)+E(_hy)*E(_g8)+E(_g9);}),_hx.b,_hp]);});};return new F(function(){return _fD(_hg.b,_ht.b,_hv);});};return new F(function(){return _fD(_hg.a,_hn,_hr);});};return E(_hm);case 6:var _hz=new T(function(){return B(_fU(B(A1(_gf,_gg.c)),_g4,_g5,_g6,_g7,_g8,_g9));}),_hA=function(_hB,_hC){var _hD=function(_hE){return new F(function(){return A2(_hz,E(_hE).b,_hC);});},_hF=function(_hG){var _hH=E(_hG),_hI=_hH.a,_hJ=new T(function(){return Math.cos(E(_hI));}),_hK=new T(function(){return Math.sin(E(_hI));}),_hL=new T(function(){return  -E(_hK);});return new F(function(){return A(_fU,[_gg.b,new T(function(){return E(_hJ)*E(_g4)+E(_hK)*E(_g5);}),new T(function(){return E(_hL)*E(_g4)+E(_hJ)*E(_g5);}),_ga,new T(function(){return E(_hJ)*E(_g7)+E(_hK)*E(_g8);}),new T(function(){return E(_hL)*E(_g7)+E(_hJ)*E(_g8);}),_gb,_hH.b,_hD]);});};return new F(function(){return _fD(_gg.a,_hB,_hF);});};return E(_hA);case 7:var _hM=E(_gg.a),_hN=new T(function(){return B(_fU(B(A1(_gf,_gg.c)),_g4,_g5,_g6,_g7,_g8,_g9));}),_hO=function(_hP,_hQ){var _hR=function(_hS){return new F(function(){return A2(_hN,E(_hS).b,_hQ);});},_hT=function(_hU){var _hV=E(_hU),_hW=_hV.a,_hX=new T(function(){return E(_hW)*E(_g7)+0*E(_g8);}),_hY=new T(function(){return E(_hW)*E(_g4)+0*E(_g5);}),_hZ=function(_i0){var _i1=E(_i0),_i2=_i1.a;return new F(function(){return A(_fU,[_gg.b,_hY,new T(function(){return 0*E(_g4)+E(_i2)*E(_g5);}),_ga,_hX,new T(function(){return 0*E(_g7)+E(_i2)*E(_g8);}),_gb,_i1.b,_hR]);});};return new F(function(){return _fD(_hM.b,_hV.b,_hZ);});};return new F(function(){return _fD(_hM.a,_hP,_hT);});};return E(_hO);default:var _i3=new T(function(){return B(_fU(_gg.b,_g4,_g5,_g6,_g7,_g8,_g9));}),_i4=new T(function(){return B(_fU(B(A1(_gf,_gg.c)),_g4,_g5,_g6,_g7,_g8,_g9));}),_i5=function(_i6){var _i7=new T(function(){return B(A1(_i3,_i6));}),_i8=function(_i9){return new F(function(){return A1(_i7,function(_ia){return new F(function(){return A2(_i4,E(_ia).b,_i9);});});});};return E(_i8);};return E(_i5);}}})(_fV,_fW,_fX,_fY,_fZ,_g0,_g1));if(_g2!=__continue){return _g2;}}},_ib=new T(function(){return eval("(function(e){e.width = e.width;})");}),_ic=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_id=function(_ie,_if,_ig){var _ih=E(_ie);return E(_if)*(1-_ih)+E(_ig)*_ih;},_ii=function(_ij,_ik,_il){var _im=new T(function(){return E(E(_ij).b);});return new F(function(){return A1(_il,new T2(0,new T2(0,_7,new T2(0,new T(function(){return E(E(_ij).a);}),new T4(0,new T(function(){return E(E(_im).a);}),new T(function(){return E(E(_im).b);}),new T(function(){return E(E(_im).c);}),_av))),_ik));});},_in=function(_io,_ip){return E(_io)/E(_ip);},_iq=0,_ir=function(_is,_it,_iu,_iv){var _iw=function(_ix,_iy,_iz){return new F(function(){return A1(_iz,new T2(0,new T2(0,_7,new T(function(){var _iA=E(_ix);return new T4(0,E(new T2(1,new T2(0,_is,_it),_iA.a)),_iA.b,E(_iA.c),E(_iA.d));})),_iy));});};return new F(function(){return A(_9I,[_8l,_iu,_iw,_iu,_iv]);});},_iB=function(_iC,_iD,_iE,_iF,_iG,_iH){var _iI=new T(function(){var _iJ=new T(function(){return B(A1(_iE,_2E));}),_iK=function(_iL,_iM,_iN){var _iO=E(_iL),_iP=E(_iO.b),_iQ=new T(function(){var _iR=new T(function(){return B(A1(_iJ,new T(function(){return B(_in(_iP.c,_iD));})));});return B(A3(_iC,_iR,_iP.a,_iP.b));});return new F(function(){return A1(_iN,new T2(0,new T2(0,_7,new T2(0,_iO.a,new T4(0,_iQ,_iG,_iq,_iP.d))),_iM));});};return B(_9I(_8l,_iF,_iK));}),_iS=new T(function(){return B(_9I(_8l,_iF,_ii));}),_iT=new T(function(){var _iU=new T(function(){return B(A1(_iH,_av));}),_iV=new T(function(){return B(A1(_iH,_aw));}),_iW=new T(function(){return B(A1(_iE,_2E));}),_iX=function(_iY,_iZ,_j0){var _j1=E(_iY),_j2=E(_j1.b),_j3=_j2.a,_j4=_j2.b;if(!E(_j2.d)){var _j5=E(_iD),_j6=E(_j2.c)+1,_j7=function(_j8,_j9){var _ja=new T(function(){var _jb=new T(function(){return B(A1(_iW,new T(function(){return _j8/_j5;})));});return B(A3(_iC,_jb,_j3,_j4));}),_jc=new T4(0,_j3,_j4,_j9,_aw);if(_j8>=_j5){return new F(function(){return A2(_iV,_iZ,function(_jd){return new F(function(){return A1(_j0,new T2(0,new T2(0,_av,new T2(0,_ja,_jc)),E(_jd).b));});});});}else{return new F(function(){return A1(_j0,new T2(0,new T2(0,_aw,new T2(0,_ja,_jc)),_iZ));});}};if(_j5>_j6){return new F(function(){return _j7(_j6,_j6);});}else{return new F(function(){return _j7(_j5,_j5);});}}else{return new F(function(){return A2(_iU,_iZ,function(_je){return new F(function(){return A1(_j0,new T2(0,new T2(0,_av,_j1),E(_je).b));});});});}};return B(_9I(_8l,_iF,_iX));}),_jf=function(_jg){var _jh=new T(function(){return B(A1(_iI,_jg));}),_ji=function(_jj){return new F(function(){return A1(_jh,function(_jk){return new F(function(){return _ir(_iS,_iT,E(_jk).b,_jj);});});});};return E(_ji);};return E(_jf);},_jl=function(_){return _7;},_jm=function(_jn,_jo,_jp,_jq,_){var _jr=function(_,_js){var _jt=function(_,_ju){var _jv=function(_,_jw){var _jx=E(_jq);switch(_jx._){case 0:return new T(function(){var _jy=function(_jz){var _jA=_jz*256,_jB=_jA&4294967295,_jC=function(_jD){var _jE=E(_ju)*256,_jF=_jE&4294967295,_jG=function(_jH){var _jI=function(_jJ){var _jK=_jJ*256,_jL=_jK&4294967295,_jM=function(_jN){var _jO=E(_jx.a);return (1>_jO)?(0>_jO)?new T4(1,_jD,_jH,_jN,0):new T4(1,_jD,_jH,_jN,_jO):new T4(1,_jD,_jH,_jN,1);};if(_jK>=_jL){if(255>_jL){if(0>_jL){return new F(function(){return _jM(0);});}else{return new F(function(){return _jM(_jL);});}}else{return new F(function(){return _jM(255);});}}else{var _jP=_jL-1|0;if(255>_jP){if(0>_jP){return new F(function(){return _jM(0);});}else{return new F(function(){return _jM(_jP);});}}else{return new F(function(){return _jM(255);});}}},_jQ=E(_jw);if(!_jQ._){return new F(function(){return _jI(0);});}else{return new F(function(){return _jI(E(_jQ.a));});}};if(_jE>=_jF){if(255>_jF){if(0>_jF){return new F(function(){return _jG(0);});}else{return new F(function(){return _jG(_jF);});}}else{return new F(function(){return _jG(255);});}}else{var _jR=_jF-1|0;if(255>_jR){if(0>_jR){return new F(function(){return _jG(0);});}else{return new F(function(){return _jG(_jR);});}}else{return new F(function(){return _jG(255);});}}};if(_jA>=_jB){if(255>_jB){if(0>_jB){return new F(function(){return _jC(0);});}else{return new F(function(){return _jC(_jB);});}}else{return new F(function(){return _jC(255);});}}else{var _jS=_jB-1|0;if(255>_jS){if(0>_jS){return new F(function(){return _jC(0);});}else{return new F(function(){return _jC(_jS);});}}else{return new F(function(){return _jC(255);});}}},_jT=E(_js);if(!_jT._){return B(_jy(0));}else{return B(_jy(E(_jT.a)));}});case 1:var _jU=B(A1(_jx.a,_)),_jV=_jU;return new T(function(){var _jW=function(_jX){var _jY=_jX*256,_jZ=_jY&4294967295,_k0=function(_k1){var _k2=E(_ju)*256,_k3=_k2&4294967295,_k4=function(_k5){var _k6=function(_k7){var _k8=_k7*256,_k9=_k8&4294967295,_ka=function(_kb){var _kc=E(_jV);return (1>_kc)?(0>_kc)?new T4(1,_k1,_k5,_kb,0):new T4(1,_k1,_k5,_kb,_kc):new T4(1,_k1,_k5,_kb,1);};if(_k8>=_k9){if(255>_k9){if(0>_k9){return new F(function(){return _ka(0);});}else{return new F(function(){return _ka(_k9);});}}else{return new F(function(){return _ka(255);});}}else{var _kd=_k9-1|0;if(255>_kd){if(0>_kd){return new F(function(){return _ka(0);});}else{return new F(function(){return _ka(_kd);});}}else{return new F(function(){return _ka(255);});}}},_ke=E(_jw);if(!_ke._){return new F(function(){return _k6(0);});}else{return new F(function(){return _k6(E(_ke.a));});}};if(_k2>=_k3){if(255>_k3){if(0>_k3){return new F(function(){return _k4(0);});}else{return new F(function(){return _k4(_k3);});}}else{return new F(function(){return _k4(255);});}}else{var _kf=_k3-1|0;if(255>_kf){if(0>_kf){return new F(function(){return _k4(0);});}else{return new F(function(){return _k4(_kf);});}}else{return new F(function(){return _k4(255);});}}};if(_jY>=_jZ){if(255>_jZ){if(0>_jZ){return new F(function(){return _k0(0);});}else{return new F(function(){return _k0(_jZ);});}}else{return new F(function(){return _k0(255);});}}else{var _kg=_jZ-1|0;if(255>_kg){if(0>_kg){return new F(function(){return _k0(0);});}else{return new F(function(){return _k0(_kg);});}}else{return new F(function(){return _k0(255);});}}},_kh=E(_js);if(!_kh._){return B(_jW(0));}else{return B(_jW(E(_kh.a)));}});case 2:var _ki=rMV(E(E(_jx.a).c)),_kj=E(_ki);return (_kj._==0)?new T(function(){var _kk=function(_kl){var _km=_kl*256,_kn=_km&4294967295,_ko=function(_kp){var _kq=E(_ju)*256,_kr=_kq&4294967295,_ks=function(_kt){var _ku=function(_kv){var _kw=_kv*256,_kx=_kw&4294967295,_ky=function(_kz){var _kA=B(A1(_jx.b,new T(function(){return B(_fB(_kj.a));})));return (1>_kA)?(0>_kA)?new T4(1,_kp,_kt,_kz,0):new T4(1,_kp,_kt,_kz,_kA):new T4(1,_kp,_kt,_kz,1);};if(_kw>=_kx){if(255>_kx){if(0>_kx){return new F(function(){return _ky(0);});}else{return new F(function(){return _ky(_kx);});}}else{return new F(function(){return _ky(255);});}}else{var _kB=_kx-1|0;if(255>_kB){if(0>_kB){return new F(function(){return _ky(0);});}else{return new F(function(){return _ky(_kB);});}}else{return new F(function(){return _ky(255);});}}},_kC=E(_jw);if(!_kC._){return new F(function(){return _ku(0);});}else{return new F(function(){return _ku(E(_kC.a));});}};if(_kq>=_kr){if(255>_kr){if(0>_kr){return new F(function(){return _ks(0);});}else{return new F(function(){return _ks(_kr);});}}else{return new F(function(){return _ks(255);});}}else{var _kD=_kr-1|0;if(255>_kD){if(0>_kD){return new F(function(){return _ks(0);});}else{return new F(function(){return _ks(_kD);});}}else{return new F(function(){return _ks(255);});}}};if(_km>=_kn){if(255>_kn){if(0>_kn){return new F(function(){return _ko(0);});}else{return new F(function(){return _ko(_kn);});}}else{return new F(function(){return _ko(255);});}}else{var _kE=_kn-1|0;if(255>_kE){if(0>_kE){return new F(function(){return _ko(0);});}else{return new F(function(){return _ko(_kE);});}}else{return new F(function(){return _ko(255);});}}},_kF=E(_js);if(!_kF._){return B(_kk(0));}else{return B(_kk(E(_kF.a)));}}):new T(function(){var _kG=function(_kH){var _kI=_kH*256,_kJ=_kI&4294967295,_kK=function(_kL){var _kM=E(_ju)*256,_kN=_kM&4294967295,_kO=function(_kP){var _kQ=function(_kR){var _kS=_kR*256,_kT=_kS&4294967295;if(_kS>=_kT){return (255>_kT)?(0>_kT)?new T4(1,_kL,_kP,0,1):new T4(1,_kL,_kP,_kT,1):new T4(1,_kL,_kP,255,1);}else{var _kU=_kT-1|0;return (255>_kU)?(0>_kU)?new T4(1,_kL,_kP,0,1):new T4(1,_kL,_kP,_kU,1):new T4(1,_kL,_kP,255,1);}},_kV=E(_jw);if(!_kV._){return new F(function(){return _kQ(0);});}else{return new F(function(){return _kQ(E(_kV.a));});}};if(_kM>=_kN){if(255>_kN){if(0>_kN){return new F(function(){return _kO(0);});}else{return new F(function(){return _kO(_kN);});}}else{return new F(function(){return _kO(255);});}}else{var _kW=_kN-1|0;if(255>_kW){if(0>_kW){return new F(function(){return _kO(0);});}else{return new F(function(){return _kO(_kW);});}}else{return new F(function(){return _kO(255);});}}};if(_kI>=_kJ){if(255>_kJ){if(0>_kJ){return new F(function(){return _kK(0);});}else{return new F(function(){return _kK(_kJ);});}}else{return new F(function(){return _kK(255);});}}else{var _kX=_kJ-1|0;if(255>_kX){if(0>_kX){return new F(function(){return _kK(0);});}else{return new F(function(){return _kK(_kX);});}}else{return new F(function(){return _kK(255);});}}},_kY=E(_js);if(!_kY._){return B(_kG(0));}else{return B(_kG(E(_kY.a)));}});default:var _kZ=rMV(E(E(_jx.a).c)),_l0=E(_kZ);if(!_l0._){var _l1=B(A2(_jx.b,E(_l0.a).a,_)),_l2=_l1;return new T(function(){var _l3=function(_l4){var _l5=_l4*256,_l6=_l5&4294967295,_l7=function(_l8){var _l9=E(_ju)*256,_la=_l9&4294967295,_lb=function(_lc){var _ld=function(_le){var _lf=_le*256,_lg=_lf&4294967295,_lh=function(_li){var _lj=E(_l2);return (1>_lj)?(0>_lj)?new T4(1,_l8,_lc,_li,0):new T4(1,_l8,_lc,_li,_lj):new T4(1,_l8,_lc,_li,1);};if(_lf>=_lg){if(255>_lg){if(0>_lg){return new F(function(){return _lh(0);});}else{return new F(function(){return _lh(_lg);});}}else{return new F(function(){return _lh(255);});}}else{var _lk=_lg-1|0;if(255>_lk){if(0>_lk){return new F(function(){return _lh(0);});}else{return new F(function(){return _lh(_lk);});}}else{return new F(function(){return _lh(255);});}}},_ll=E(_jw);if(!_ll._){return new F(function(){return _ld(0);});}else{return new F(function(){return _ld(E(_ll.a));});}};if(_l9>=_la){if(255>_la){if(0>_la){return new F(function(){return _lb(0);});}else{return new F(function(){return _lb(_la);});}}else{return new F(function(){return _lb(255);});}}else{var _lm=_la-1|0;if(255>_lm){if(0>_lm){return new F(function(){return _lb(0);});}else{return new F(function(){return _lb(_lm);});}}else{return new F(function(){return _lb(255);});}}};if(_l5>=_l6){if(255>_l6){if(0>_l6){return new F(function(){return _l7(0);});}else{return new F(function(){return _l7(_l6);});}}else{return new F(function(){return _l7(255);});}}else{var _ln=_l6-1|0;if(255>_ln){if(0>_ln){return new F(function(){return _l7(0);});}else{return new F(function(){return _l7(_ln);});}}else{return new F(function(){return _l7(255);});}}},_lo=E(_js);if(!_lo._){return B(_l3(0));}else{return B(_l3(E(_lo.a)));}});}else{return new T(function(){var _lp=function(_lq){var _lr=_lq*256,_ls=_lr&4294967295,_lt=function(_lu){var _lv=E(_ju)*256,_lw=_lv&4294967295,_lx=function(_ly){var _lz=function(_lA){var _lB=_lA*256,_lC=_lB&4294967295;if(_lB>=_lC){return (255>_lC)?(0>_lC)?new T4(1,_lu,_ly,0,1):new T4(1,_lu,_ly,_lC,1):new T4(1,_lu,_ly,255,1);}else{var _lD=_lC-1|0;return (255>_lD)?(0>_lD)?new T4(1,_lu,_ly,0,1):new T4(1,_lu,_ly,_lD,1):new T4(1,_lu,_ly,255,1);}},_lE=E(_jw);if(!_lE._){return new F(function(){return _lz(0);});}else{return new F(function(){return _lz(E(_lE.a));});}};if(_lv>=_lw){if(255>_lw){if(0>_lw){return new F(function(){return _lx(0);});}else{return new F(function(){return _lx(_lw);});}}else{return new F(function(){return _lx(255);});}}else{var _lF=_lw-1|0;if(255>_lF){if(0>_lF){return new F(function(){return _lx(0);});}else{return new F(function(){return _lx(_lF);});}}else{return new F(function(){return _lx(255);});}}};if(_lr>=_ls){if(255>_ls){if(0>_ls){return new F(function(){return _lt(0);});}else{return new F(function(){return _lt(_ls);});}}else{return new F(function(){return _lt(255);});}}else{var _lG=_ls-1|0;if(255>_lG){if(0>_lG){return new F(function(){return _lt(0);});}else{return new F(function(){return _lt(_lG);});}}else{return new F(function(){return _lt(255);});}}},_lH=E(_js);if(!_lH._){return B(_lp(0));}else{return B(_lp(E(_lH.a)));}});}}},_lI=E(_jp);switch(_lI._){case 0:return new F(function(){return _jv(_,new T1(1,_lI.a));});break;case 1:var _lJ=B(A1(_lI.a,_));return new F(function(){return _jv(_,new T1(1,_lJ));});break;case 2:var _lK=rMV(E(E(_lI.a).c)),_lL=E(_lK);if(!_lL._){var _lM=new T(function(){return B(A1(_lI.b,new T(function(){return B(_fB(_lL.a));})));});return new F(function(){return _jv(_,new T1(1,_lM));});}else{return new F(function(){return _jv(_,_2o);});}break;default:var _lN=rMV(E(E(_lI.a).c)),_lO=E(_lN);if(!_lO._){var _lP=B(A2(_lI.b,E(_lO.a).a,_));return new F(function(){return _jv(_,new T1(1,_lP));});}else{return new F(function(){return _jv(_,_2o);});}}},_lQ=function(_){var _lR=function(_,_lS){var _lT=E(_jq);switch(_lT._){case 0:return new T(function(){var _lU=function(_lV){var _lW=_lV*256,_lX=_lW&4294967295,_lY=function(_lZ){var _m0=function(_m1){var _m2=_m1*256,_m3=_m2&4294967295,_m4=function(_m5){var _m6=E(_lT.a);return (1>_m6)?(0>_m6)?new T4(1,_lZ,0,_m5,0):new T4(1,_lZ,0,_m5,_m6):new T4(1,_lZ,0,_m5,1);};if(_m2>=_m3){if(255>_m3){if(0>_m3){return new F(function(){return _m4(0);});}else{return new F(function(){return _m4(_m3);});}}else{return new F(function(){return _m4(255);});}}else{var _m7=_m3-1|0;if(255>_m7){if(0>_m7){return new F(function(){return _m4(0);});}else{return new F(function(){return _m4(_m7);});}}else{return new F(function(){return _m4(255);});}}},_m8=E(_lS);if(!_m8._){return new F(function(){return _m0(0);});}else{return new F(function(){return _m0(E(_m8.a));});}};if(_lW>=_lX){if(255>_lX){if(0>_lX){return new F(function(){return _lY(0);});}else{return new F(function(){return _lY(_lX);});}}else{return new F(function(){return _lY(255);});}}else{var _m9=_lX-1|0;if(255>_m9){if(0>_m9){return new F(function(){return _lY(0);});}else{return new F(function(){return _lY(_m9);});}}else{return new F(function(){return _lY(255);});}}},_ma=E(_js);if(!_ma._){return B(_lU(0));}else{return B(_lU(E(_ma.a)));}});case 1:var _mb=B(A1(_lT.a,_)),_mc=_mb;return new T(function(){var _md=function(_me){var _mf=_me*256,_mg=_mf&4294967295,_mh=function(_mi){var _mj=function(_mk){var _ml=_mk*256,_mm=_ml&4294967295,_mn=function(_mo){var _mp=E(_mc);return (1>_mp)?(0>_mp)?new T4(1,_mi,0,_mo,0):new T4(1,_mi,0,_mo,_mp):new T4(1,_mi,0,_mo,1);};if(_ml>=_mm){if(255>_mm){if(0>_mm){return new F(function(){return _mn(0);});}else{return new F(function(){return _mn(_mm);});}}else{return new F(function(){return _mn(255);});}}else{var _mq=_mm-1|0;if(255>_mq){if(0>_mq){return new F(function(){return _mn(0);});}else{return new F(function(){return _mn(_mq);});}}else{return new F(function(){return _mn(255);});}}},_mr=E(_lS);if(!_mr._){return new F(function(){return _mj(0);});}else{return new F(function(){return _mj(E(_mr.a));});}};if(_mf>=_mg){if(255>_mg){if(0>_mg){return new F(function(){return _mh(0);});}else{return new F(function(){return _mh(_mg);});}}else{return new F(function(){return _mh(255);});}}else{var _ms=_mg-1|0;if(255>_ms){if(0>_ms){return new F(function(){return _mh(0);});}else{return new F(function(){return _mh(_ms);});}}else{return new F(function(){return _mh(255);});}}},_mt=E(_js);if(!_mt._){return B(_md(0));}else{return B(_md(E(_mt.a)));}});case 2:var _mu=rMV(E(E(_lT.a).c)),_mv=E(_mu);return (_mv._==0)?new T(function(){var _mw=function(_mx){var _my=_mx*256,_mz=_my&4294967295,_mA=function(_mB){var _mC=function(_mD){var _mE=_mD*256,_mF=_mE&4294967295,_mG=function(_mH){var _mI=B(A1(_lT.b,new T(function(){return B(_fB(_mv.a));})));return (1>_mI)?(0>_mI)?new T4(1,_mB,0,_mH,0):new T4(1,_mB,0,_mH,_mI):new T4(1,_mB,0,_mH,1);};if(_mE>=_mF){if(255>_mF){if(0>_mF){return new F(function(){return _mG(0);});}else{return new F(function(){return _mG(_mF);});}}else{return new F(function(){return _mG(255);});}}else{var _mJ=_mF-1|0;if(255>_mJ){if(0>_mJ){return new F(function(){return _mG(0);});}else{return new F(function(){return _mG(_mJ);});}}else{return new F(function(){return _mG(255);});}}},_mK=E(_lS);if(!_mK._){return new F(function(){return _mC(0);});}else{return new F(function(){return _mC(E(_mK.a));});}};if(_my>=_mz){if(255>_mz){if(0>_mz){return new F(function(){return _mA(0);});}else{return new F(function(){return _mA(_mz);});}}else{return new F(function(){return _mA(255);});}}else{var _mL=_mz-1|0;if(255>_mL){if(0>_mL){return new F(function(){return _mA(0);});}else{return new F(function(){return _mA(_mL);});}}else{return new F(function(){return _mA(255);});}}},_mM=E(_js);if(!_mM._){return B(_mw(0));}else{return B(_mw(E(_mM.a)));}}):new T(function(){var _mN=function(_mO){var _mP=_mO*256,_mQ=_mP&4294967295,_mR=function(_mS){var _mT=function(_mU){var _mV=_mU*256,_mW=_mV&4294967295;if(_mV>=_mW){return (255>_mW)?(0>_mW)?new T4(1,_mS,0,0,1):new T4(1,_mS,0,_mW,1):new T4(1,_mS,0,255,1);}else{var _mX=_mW-1|0;return (255>_mX)?(0>_mX)?new T4(1,_mS,0,0,1):new T4(1,_mS,0,_mX,1):new T4(1,_mS,0,255,1);}},_mY=E(_lS);if(!_mY._){return new F(function(){return _mT(0);});}else{return new F(function(){return _mT(E(_mY.a));});}};if(_mP>=_mQ){if(255>_mQ){if(0>_mQ){return new F(function(){return _mR(0);});}else{return new F(function(){return _mR(_mQ);});}}else{return new F(function(){return _mR(255);});}}else{var _mZ=_mQ-1|0;if(255>_mZ){if(0>_mZ){return new F(function(){return _mR(0);});}else{return new F(function(){return _mR(_mZ);});}}else{return new F(function(){return _mR(255);});}}},_n0=E(_js);if(!_n0._){return B(_mN(0));}else{return B(_mN(E(_n0.a)));}});default:var _n1=rMV(E(E(_lT.a).c)),_n2=E(_n1);if(!_n2._){var _n3=B(A2(_lT.b,E(_n2.a).a,_)),_n4=_n3;return new T(function(){var _n5=function(_n6){var _n7=_n6*256,_n8=_n7&4294967295,_n9=function(_na){var _nb=function(_nc){var _nd=_nc*256,_ne=_nd&4294967295,_nf=function(_ng){var _nh=E(_n4);return (1>_nh)?(0>_nh)?new T4(1,_na,0,_ng,0):new T4(1,_na,0,_ng,_nh):new T4(1,_na,0,_ng,1);};if(_nd>=_ne){if(255>_ne){if(0>_ne){return new F(function(){return _nf(0);});}else{return new F(function(){return _nf(_ne);});}}else{return new F(function(){return _nf(255);});}}else{var _ni=_ne-1|0;if(255>_ni){if(0>_ni){return new F(function(){return _nf(0);});}else{return new F(function(){return _nf(_ni);});}}else{return new F(function(){return _nf(255);});}}},_nj=E(_lS);if(!_nj._){return new F(function(){return _nb(0);});}else{return new F(function(){return _nb(E(_nj.a));});}};if(_n7>=_n8){if(255>_n8){if(0>_n8){return new F(function(){return _n9(0);});}else{return new F(function(){return _n9(_n8);});}}else{return new F(function(){return _n9(255);});}}else{var _nk=_n8-1|0;if(255>_nk){if(0>_nk){return new F(function(){return _n9(0);});}else{return new F(function(){return _n9(_nk);});}}else{return new F(function(){return _n9(255);});}}},_nl=E(_js);if(!_nl._){return B(_n5(0));}else{return B(_n5(E(_nl.a)));}});}else{return new T(function(){var _nm=function(_nn){var _no=_nn*256,_np=_no&4294967295,_nq=function(_nr){var _ns=function(_nt){var _nu=_nt*256,_nv=_nu&4294967295;if(_nu>=_nv){return (255>_nv)?(0>_nv)?new T4(1,_nr,0,0,1):new T4(1,_nr,0,_nv,1):new T4(1,_nr,0,255,1);}else{var _nw=_nv-1|0;return (255>_nw)?(0>_nw)?new T4(1,_nr,0,0,1):new T4(1,_nr,0,_nw,1):new T4(1,_nr,0,255,1);}},_nx=E(_lS);if(!_nx._){return new F(function(){return _ns(0);});}else{return new F(function(){return _ns(E(_nx.a));});}};if(_no>=_np){if(255>_np){if(0>_np){return new F(function(){return _nq(0);});}else{return new F(function(){return _nq(_np);});}}else{return new F(function(){return _nq(255);});}}else{var _ny=_np-1|0;if(255>_ny){if(0>_ny){return new F(function(){return _nq(0);});}else{return new F(function(){return _nq(_ny);});}}else{return new F(function(){return _nq(255);});}}},_nz=E(_js);if(!_nz._){return B(_nm(0));}else{return B(_nm(E(_nz.a)));}});}}},_nA=E(_jp);switch(_nA._){case 0:return new F(function(){return _lR(_,new T1(1,_nA.a));});break;case 1:var _nB=B(A1(_nA.a,_));return new F(function(){return _lR(_,new T1(1,_nB));});break;case 2:var _nC=rMV(E(E(_nA.a).c)),_nD=E(_nC);if(!_nD._){var _nE=new T(function(){return B(A1(_nA.b,new T(function(){return B(_fB(_nD.a));})));});return new F(function(){return _lR(_,new T1(1,_nE));});}else{return new F(function(){return _lR(_,_2o);});}break;default:var _nF=rMV(E(E(_nA.a).c)),_nG=E(_nF);if(!_nG._){var _nH=B(A2(_nA.b,E(_nG.a).a,_));return new F(function(){return _lR(_,new T1(1,_nH));});}else{return new F(function(){return _lR(_,_2o);});}}},_nI=E(_jo);switch(_nI._){case 0:return new F(function(){return _jt(_,_nI.a);});break;case 1:var _nJ=B(A1(_nI.a,_));return new F(function(){return _jt(_,_nJ);});break;case 2:var _nK=rMV(E(E(_nI.a).c)),_nL=E(_nK);if(!_nL._){var _nM=new T(function(){return B(A1(_nI.b,new T(function(){return E(E(_nL.a).a);})));});return new F(function(){return _jt(_,_nM);});}else{return new F(function(){return _lQ(_);});}break;default:var _nN=rMV(E(E(_nI.a).c)),_nO=E(_nN);if(!_nO._){var _nP=B(A2(_nI.b,E(_nO.a).a,_));return new F(function(){return _jt(_,_nP);});}else{return new F(function(){return _lQ(_);});}}},_nQ=E(_jn);switch(_nQ._){case 0:return new F(function(){return _jr(_,new T1(1,_nQ.a));});break;case 1:var _nR=B(A1(_nQ.a,_));return new F(function(){return _jr(_,new T1(1,_nR));});break;case 2:var _nS=rMV(E(E(_nQ.a).c)),_nT=E(_nS);if(!_nT._){var _nU=new T(function(){return B(A1(_nQ.b,new T(function(){return B(_fB(_nT.a));})));});return new F(function(){return _jr(_,new T1(1,_nU));});}else{return new F(function(){return _jr(_,_2o);});}break;default:var _nV=rMV(E(E(_nQ.a).c)),_nW=E(_nV);if(!_nW._){var _nX=B(A2(_nQ.b,E(_nW.a).a,_));return new F(function(){return _jr(_,new T1(1,_nX));});}else{return new F(function(){return _jr(_,_2o);});}}},_nY=new T(function(){return toJSStr(_6);}),_nZ="rgb(",_o0=",",_o1="rgba(",_o2=")",_o3=new T2(1,_o2,_6),_o4=function(_o5){var _o6=E(_o5);if(!_o6._){var _o7=jsCat(new T2(1,_nZ,new T2(1,new T(function(){return String(_o6.a);}),new T2(1,_o0,new T2(1,new T(function(){return String(_o6.b);}),new T2(1,_o0,new T2(1,new T(function(){return String(_o6.c);}),_o3)))))),E(_nY));return E(_o7);}else{var _o8=jsCat(new T2(1,_o1,new T2(1,new T(function(){return String(_o6.a);}),new T2(1,_o0,new T2(1,new T(function(){return String(_o6.b);}),new T2(1,_o0,new T2(1,new T(function(){return String(_o6.c);}),new T2(1,_o0,new T2(1,new T(function(){return String(_o6.d);}),_o3)))))))),E(_nY));return E(_o8);}},_o9=function(_oa,_ob){var _oc=E(_oa),_od=function(_oe){var _of=E(_ob),_og=function(_oh){return new T2(0,E(new T1(0,new T(function(){return B(A1(_oe,_oh));}))),E(new T1(0,_)));};return new T2(0,E(_of.a),E(new T2(2,_of.b,new T1(1,_og))));};return new T2(0,E(_oc.a),E(new T2(2,_oc.b,new T1(1,_od))));},_oi=function(_oj){return E(E(_oj).b);},_ok=function(_ol,_om,_on){return new F(function(){return _o9(B(A3(_oi,_ol,_2E,_om)),_on);});},_oo=function(_op,_oq){return E(_op);},_or=function(_os){return E(E(_os).a);},_ot=function(_ou,_ov,_ow){return new F(function(){return _o9(B(A3(_or,_ou,_oo,_ov)),_ow);});},_ox=function(_oy,_oz){return new T2(0,E(new T1(0,_oz)),E(new T1(0,_)));},_oA=function(_oB,_oC){return new F(function(){return _ox(_oB,_oC);});},_oD=new T(function(){return B(_bo("w_s1yq Functor (Skeleton t)"));}),_oE=new T(function(){return B(_oF(_oD));}),_oG=function(_oC){return new F(function(){return _oA(_oE,_oC);});},_oH=function(_oI,_oC){return new F(function(){return _oG(_oC);});},_oJ=function(_oC){return new F(function(){return _oH(_,_oC);});},_oF=function(_oK){return new T5(0,_oK,_oJ,_o9,function(_oB,_oC){return new F(function(){return _ok(_oK,_oB,_oC);});},function(_oB,_oC){return new F(function(){return _ot(_oK,_oB,_oC);});});},_oL=function(_oM,_oN,_oO){return new F(function(){return A3(_6u,B(_oP(_oM)),_oN,function(_oQ){return E(_oO);});});},_oR=function(_oS,_oT,_oU){var _oV=E(_oT);return new T2(0,E(_oV.a),E(new T2(2,_oV.b,new T1(1,_oU))));},_oW=function(_oX){return new F(function(){return err(_oX);});},_oP=function(_oY){return new T5(0,_oY,function(_oB,_oC){return new F(function(){return _oR(_oY,_oB,_oC);});},function(_oB,_oC){return new F(function(){return _oL(_oY,_oB,_oC);});},function(_oC){return new F(function(){return _oA(_oY,_oC);});},_oW);},_oZ=new T(function(){return B(_oP(_p0));}),_p1=function(_p2,_p3,_p4){var _p5=function(_p6){return new F(function(){return A2(_6T,_p2,new T(function(){return B(A1(_p3,_p6));}));});};return new F(function(){return A3(_6u,_p2,_p4,_p5);});},_p7=function(_oB,_oC){return new F(function(){return _p1(_oZ,_oB,_oC);});},_p8=function(_p9,_pa){return new F(function(){return _p7(function(_pb){return E(_p9);},_pa);});},_pc=new T(function(){return new T2(0,_p7,_p8);}),_p0=new T(function(){return B(_oF(_pc));}),_pd=function(_oC){return new F(function(){return _oA(_p0,_oC);});},_pe=function(_pf){return new T2(0,E(new T2(1,_pf,_pd)),E(new T1(0,_)));},_pg=function(_oC){return new F(function(){return _pe(_oC);});},_ph=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_pi=function(_pj,_){var _pk=__app1(E(_ph),E(_pj));return new F(function(){return _jl(_);});},_pl=new T2(0,_pi,_7),_pm=new T(function(){return B(_pg(_pl));}),_pn=function(_po){return E(_pm);},_pp=new T1(1,_pn),_pq=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_pr=new T(function(){return eval("(function(ctx){ctx.save();})");}),_ps=function(_pt,_pu,_){var _pv=E(_pt);switch(_pv._){case 0:return new F(function(){return A2(_pu,_pv.a,_);});break;case 1:var _pw=B(A1(_pv.a,_));return new F(function(){return A2(_pu,_pw,_);});break;case 2:var _px=rMV(E(E(_pv.a).c)),_py=E(_px);if(!_py._){var _pz=new T(function(){return B(A1(_pv.b,new T(function(){return B(_fB(_py.a));})));});return new F(function(){return A2(_pu,_pz,_);});}else{return _7;}break;default:var _pA=rMV(E(E(_pv.a).c)),_pB=E(_pA);if(!_pB._){var _pC=B(A2(_pv.b,E(_pB.a).a,_));return new F(function(){return A2(_pu,_pC,_);});}else{return _7;}}},_pD="shadowBlur",_pE="shadowColor",_pF="shadowOffsetX",_pG="shadowOffsetY",_pH=function(_pI,_pJ,_pK,_pL,_pM){var _pN=function(_pO,_){var _pP=function(_pQ,_){var _pR=function(_pS,_){return new F(function(){return _ps(_pK,function(_pT,_){var _pU=E(_pL),_pV=B(_jm(_pU.a,_pU.b,_pU.c,_pU.d,_)),_pW=E(_pO),_pX=__app1(E(_pr),_pW),_pY=E(_ic),_pZ=__app3(_pY,_pW,E(_pE),B(_o4(_pV))),_q0=String(E(_pQ)),_q1=__app3(_pY,_pW,E(_pF),_q0),_q2=String(E(_pS)),_q3=__app3(_pY,_pW,E(_pG),_q2),_q4=String(E(_pT)),_q5=__app3(_pY,_pW,E(_pD),_q4),_q6=__app1(E(_pq),_pW);return new F(function(){return _jl(_);});},_);});};return new F(function(){return _ps(_pJ,_pR,_);});};return new F(function(){return _ps(_pI,_pP,_);});},_q7=B(_pg(new T2(0,_pN,_7)));return new T2(0,E(_q7.a),E(new T2(2,new T2(2,_q7.b,new T1(1,function(_q8){return E(_pM);})),_pp)));},_q9=function(_qa,_qb,_qc,_qd,_){var _qe=E(_qa);switch(_qe._){case 0:return new F(function(){return A(_qb,[_qe.a,_qc,_qd,_]);});break;case 1:var _qf=B(A1(_qe.a,_));return new F(function(){return A(_qb,[_qf,_qc,_qd,_]);});break;case 2:var _qg=rMV(E(E(_qe.a).c)),_qh=E(_qg);if(!_qh._){var _qi=new T(function(){return B(A1(_qe.b,new T(function(){return B(_fB(_qh.a));})));});return new F(function(){return A(_qb,[_qi,_qc,_qd,_]);});}else{return _7;}break;default:var _qj=rMV(E(E(_qe.a).c)),_qk=E(_qj);if(!_qk._){var _ql=B(A2(_qe.b,E(_qk.a).a,_));return new F(function(){return A(_qb,[_ql,_qc,_qd,_]);});}else{return _7;}}},_qm=new T(function(){return eval("(function(ctx,_){ctx.restore();})");}),_qn=function(_){return _av;},_qo=function(_qp,_){return new F(function(){return _qn(_);});},_qq=new T(function(){return eval("(function(ctx,_){ctx.save();})");}),_qr=new T(function(){return eval("(function(x,y,ctx,_){ctx.scale(x,y);})");}),_qs=new T(function(){return eval("(function(str,x,y,ctx,_){ctx.strokeText(str,x,y);})");}),_qt=new T(function(){return eval("(function(str,x,y,ctx,_){ctx.fillText(str,x,y);})");}),_qu=new T(function(){return eval("(function(x,y,ctx,_){ctx.translate(x,y);})");}),_qv="alphabetic",_qw="middle",_qx="hanging",_qy="right",_qz="center",_qA="left",_qB="(function(fn,a,b,ctx){ctx.font=\"10px \"+fn;ctx.textAlign=a;ctx.textBaseline=b;})",_qC=function(_qD,_qE,_qF,_qG,_qH,_qI,_qJ){var _qK=function(_qL,_qM,_qN,_){var _qO=function(_qP,_qQ,_qR,_){var _qS=function(_qT,_qU,_qV,_){var _qW=function(_qX,_qY,_qZ,_){var _r0=E(_qY),_r1=E(_qZ),_r2=__app2(E(_qq),_r0,_r1),_r3=function(_r4){var _r5=function(_r6){var _r7=eval(E(_qB)),_r8=__app4(E(_r7),E(_qD),_r4,_r6,_r0),_r9=__app4(E(_qu),E(_qP),E(_qT),_r0,_r1),_ra=E(_qX)/10,_rb=__app4(E(_qr),_ra,_ra,_r0,_r1);if(!_r1){var _rc=__app5(E(_qs),toJSStr(E(_qL)),0,0,_r0,false),_rd=__app2(E(_qm),_r0,false);return new F(function(){return _jl(_);});}else{var _re=__app5(E(_qt),toJSStr(E(_qL)),0,0,_r0,true),_rf=__app2(E(_qm),_r0,true);return new F(function(){return _jl(_);});}};switch(E(_qG)){case 0:return new F(function(){return _r5(E(_qx));});break;case 1:return new F(function(){return _r5(E(_qw));});break;default:return new F(function(){return _r5(E(_qv));});}};switch(E(_qF)){case 0:return new F(function(){return _r3(E(_qA));});break;case 1:return new F(function(){return _r3(E(_qz));});break;default:return new F(function(){return _r3(E(_qy));});}};return new F(function(){return _q9(_qJ,_qW,_qU,_qV,_);});};return new F(function(){return _q9(_qI,_qS,_qQ,_qR,_);});};return new F(function(){return _q9(_qH,_qO,_qM,_qN,_);});};return new T3(0,_qo,function(_rg,_rh,_){return new F(function(){return _q9(_qE,_qK,_rg,_rh,_);});},_7);},_ri=2,_rj=function(_rk){return new T1(1,_rk);},_rl=0,_rm="fillStyle",_rn=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_ro=function(_rp,_rq){return new F(function(){return _pg(new T2(0,function(_rr,_){var _rs=E(_rp),_rt=B(_jm(_rs.a,_rs.b,_rs.c,_rs.d,_)),_ru=E(_rr),_rv=__app3(E(_ic),_ru,E(_rm),B(_o4(_rt))),_rw=__app1(E(_pq),_ru),_rx=B(A3(E(_rq).b,_ru,_aw,_)),_ry=__app1(E(_rn),_ru);return new F(function(){return _jl(_);});},_7));});},_rz=function(_rA,_rB,_){var _rC=E(_rA);switch(_rC._){case 0:return new F(function(){return A2(_rB,_rC.a,_);});break;case 1:var _rD=B(A1(_rC.a,_));return new F(function(){return A2(_rB,_rD,_);});break;case 2:var _rE=rMV(E(E(_rC.a).c)),_rF=E(_rE);if(!_rF._){var _rG=new T(function(){return B(A1(_rC.b,new T(function(){return B(_fB(_rF.a));})));});return new F(function(){return A2(_rB,_rG,_);});}else{return _av;}break;default:var _rH=rMV(E(E(_rC.a).c)),_rI=E(_rH);if(!_rI._){var _rJ=B(A2(_rC.b,E(_rI.a).a,_));return new F(function(){return A2(_rB,_rJ,_);});}else{return _av;}}},_rK=new T(function(){return eval("(function(x,y,ctx,_){ctx.moveTo(x,y);})");}),_rL=new T(function(){return eval("(function(x,y,ctx,_){ctx.lineTo(x,y);})");}),_rM=function(_rN,_rO,_rP,_rQ){var _rR=function(_rS,_rT,_rU,_){var _rV=function(_rW,_rX,_rY,_){var _rZ=function(_s0,_s1,_s2,_){return new F(function(){return _q9(_rQ,function(_s3,_s4,_s5,_){var _s6=E(_rS),_s7=E(_rW),_s8=E(_s4),_s9=E(_s5),_sa=__app4(E(_rK),_s6,_s7,_s8,_s9),_sb=_s6+E(_s0),_sc=E(_rL),_sd=__app4(_sc,_sb,_s7,_s8,_s9),_se=_s7+E(_s3),_sf=__app4(_sc,_sb,_se,_s8,_s9),_sg=__app4(_sc,_s6,_se,_s8,_s9),_sh=__app4(_sc,_s6,_s7,_s8,_s9);return new F(function(){return _jl(_);});},_s1,_s2,_);});};return new F(function(){return _q9(_rP,_rZ,_rX,_rY,_);});};return new F(function(){return _q9(_rO,_rV,_rT,_rU,_);});},_si=function(_sj,_){var _sk=E(_sj),_sl=function(_sm,_){var _sn=function(_so,_){var _sp=function(_sq,_){var _sr=function(_ss,_){return new T(function(){var _st=E(_sq),_su=function(_sv){var _sw=E(_ss),_sx=E(_sk.b)-E(_so)-_sw/2;return (_sx==0)?0<_sw/2:(_sx<=0)? -_sx<_sw/2:_sx<_sw/2;},_sy=E(_sk.a)-E(_sm)-_st/2;if(!_sy){if(0>=_st/2){return false;}else{return B(_su(_));}}else{if(_sy<=0){if( -_sy>=_st/2){return false;}else{return B(_su(_));}}else{if(_sy>=_st/2){return false;}else{return B(_su(_));}}}});};return new F(function(){return _rz(_rQ,_sr,_);});};return new F(function(){return _rz(_rP,_sp,_);});};return new F(function(){return _rz(_rO,_sn,_);});};return new F(function(){return _rz(_rN,_sl,_);});};return new T3(0,_si,function(_rg,_rh,_){return new F(function(){return _q9(_rN,_rR,_rg,_rh,_);});},_7);},_sz=0,_sA=new T1(0,_sz),_sB=200,_sC=new T1(0,_sB),_sD=new T(function(){var _sE=B(_rM(_sA,_sA,_sC,_sC));return new T3(0,_sE.a,_sE.b,_sE.c);}),_sF=new T1(0,_f3),_sG=new T4(0,_sF,_sF,_sF,_sF),_sH=new T(function(){return B(_ro(_sG,_sD));}),_sI=function(_sJ,_sK){return new F(function(){return A1(_sK,new T2(0,_7,_sJ));});},_sL=new T1(0,_f2),_sM=new T4(0,_sL,_sL,_sL,_sF),_sN=2,_sO=function(_sP){switch(E(_sP)){case 0:return true;case 1:return false;case 2:return false;case 3:return false;case 4:return false;case 5:return false;default:return false;}},_sQ=function(_sR){return (E(_sR)==2)?true:false;},_sS=function(_sT){switch(E(_sT)){case 5:return true;case 6:return true;default:return false;}},_sU=function(_sV,_sW,_sX){var _sY=new T(function(){return B(_sU(_sV,_sW,_sX));});return new F(function(){return A3(_6u,_sV,_sX,function(_sZ){if(!B(A1(_sW,_sZ))){return E(_sY);}else{return new F(function(){return A2(_6T,_sV,_sZ);});}});});},_t0=function(_t1,_t2,_t3,_t4){var _t5=new T(function(){var _t6=new T(function(){var _t7=function(_t8,_t9){return new T1(0,B(_8B(_t4,function(_ta){return new F(function(){return A1(_t9,new T2(0,_ta,_t8));});})));};return B(_sU(_8f,_sS,_t7));}),_tb=function(_tc,_td){var _te=new T(function(){var _tf=function(_tg){var _th=E(_tg),_ti=_th.b,_tj=E(_th.a);if(_tj==6){return new F(function(){return A1(_td,new T2(0,_sN,_ti));});}else{return new F(function(){return A2(_t3,_ti,function(_tk){return new F(function(){return A1(_td,new T2(0,_tj,E(_tk).b));});});});}};return B(A2(_t6,_tc,_tf));});return new T1(0,B(_8B(_t4,function(_tl){var _tm=E(_tl);if(_tm==3){return E(_te);}else{return new F(function(){return A1(_td,new T2(0,_tm,_tc));});}})));};return B(_sU(_8f,_sQ,_tb));}),_tn=new T(function(){var _to=function(_tp,_tq){return new T1(0,B(_8B(_t4,function(_tr){return new F(function(){return A1(_tq,new T2(0,_tr,_tp));});})));};return B(_sU(_8f,_sO,_to));}),_ts=function(_tt){var _tu=new T(function(){return B(A1(_t1,_tt));}),_tv=function(_tw){var _tx=function(_ty){return new F(function(){return A2(_ts,E(_ty).b,_tw);});},_tz=function(_tA){return new F(function(){return A2(_t5,E(_tA).b,_tx);});},_tB=function(_tC){return new F(function(){return A2(_t2,E(_tC).b,_tz);});};return new F(function(){return A1(_tu,function(_tD){return new F(function(){return A2(_tn,E(_tD).b,_tB);});});});};return E(_tv);};return E(_ts);},_tE=new T(function(){return eval("(function(ctx){ctx.clip();})");}),_tF=function(_tG,_tH){var _tI=B(_pg(new T2(0,function(_tJ,_){var _tK=E(_tJ),_tL=__app1(E(_pr),_tK),_tM=__app1(E(_pq),_tK),_tN=B(A3(E(_tG).b,_tK,_aw,_)),_tO=__app1(E(_tE),_tK);return new F(function(){return _jl(_);});},_7)));return new T2(0,E(_tI.a),E(new T2(2,new T2(2,_tI.b,new T1(1,function(_tP){return E(_tH);})),_pp)));},_tQ=function(_tR,_tS){return new F(function(){return A1(_tS,new T2(0,_7,_tR));});},_tT=function(_tU,_tV,_tW){return new F(function(){return _tQ(_tV,_tW);});},_tX=function(_tY,_tZ){return new F(function(){return A1(_tY,_tZ);});},_u0=function(_tV,_tW){return new F(function(){return _tX(_tV,_tW);});},_u1=0.2,_u2=new T1(0,_u1),_u3=1,_u4=new T1(0,_u3),_u5=new T4(0,_u2,_u2,_u2,_u4),_u6="mplus",_u7=1.2,_u8=new T1(0,_u7),_u9=function(_ua,_ub,_uc,_){var _ud=B(A1(_ub,_)),_ue=B(A1(_uc,_));return new T(function(){return B(A2(_ua,_ud,_ue));});},_uf=new T(function(){return B(unCStr("Unable to operate opLift"));}),_ug=function(_uh){return new F(function(){return err(_uf);});},_ui=new T(function(){return B(_ug(_));}),_uj=function(_uk,_ul,_um){var _un=function(_uo){var _up=function(_){var _uq=function(_,_ur){var _us=E(_um);switch(_us._){case 0:return new T(function(){return B(A2(_uk,_ur,_us.a));});case 1:var _ut=B(A1(_us.a,_));return new T(function(){return B(A2(_uk,_ur,_ut));});case 2:var _uu=rMV(E(E(_us.a).c)),_uv=E(_uu);return (_uv._==0)?new T(function(){var _uw=new T(function(){return B(A1(_us.b,new T(function(){return B(_fB(_uv.a));})));});return B(A2(_uk,_ur,_uw));}):E(_ui);default:var _ux=rMV(E(E(_us.a).c)),_uy=E(_ux);if(!_uy._){var _uz=B(A2(_us.b,E(_uy.a).a,_));return new T(function(){return B(A2(_uk,_ur,_uz));});}else{return E(_ui);}}},_uA=function(_){var _uB=E(_um);switch(_uB._){case 0:return E(_ui);case 1:var _uC=B(A1(_uB.a,_));return E(_ui);case 2:var _uD=rMV(E(E(_uB.a).c));return (E(_uD)._==0)?E(_ui):E(_ui);default:var _uE=rMV(E(E(_uB.a).c)),_uF=E(_uE);if(!_uF._){var _uG=B(A2(_uB.b,E(_uF.a).a,_));return E(_ui);}else{return E(_ui);}}},_uH=E(_ul);switch(_uH._){case 0:return new F(function(){return _uq(_,_uH.a);});break;case 1:var _uI=B(A1(_uH.a,_));return new F(function(){return _uq(_,_uI);});break;case 2:var _uJ=rMV(E(E(_uH.a).c)),_uK=E(_uJ);if(!_uK._){var _uL=new T(function(){return B(A1(_uH.b,new T(function(){return E(E(_uK.a).a);})));});return new F(function(){return _uq(_,_uL);});}else{return new F(function(){return _uA(_);});}break;default:var _uM=rMV(E(E(_uH.a).c)),_uN=E(_uM);if(!_uN._){var _uO=B(A2(_uH.b,E(_uN.a).a,_));return new F(function(){return _uq(_,_uO);});}else{return new F(function(){return _uA(_);});}}};return new T1(1,_up);},_uP=E(_ul);switch(_uP._){case 0:var _uQ=_uP.a,_uR=E(_um);switch(_uR._){case 0:return new T1(0,new T(function(){return B(A2(_uk,_uQ,_uR.a));}));case 1:var _uS=function(_){var _uT=B(A1(_uR.a,_));return new T(function(){return B(A2(_uk,_uQ,_uT));});};return new T1(1,_uS);case 2:var _uU=new T(function(){return B(A1(_uk,_uQ));}),_uV=function(_uW){return new F(function(){return A1(_uU,new T(function(){return B(A1(_uR.b,_uW));}));});};return new T2(2,_uR.a,_uV);default:var _uX=new T(function(){return B(A1(_uk,_uQ));}),_uY=function(_uZ,_){var _v0=B(A2(_uR.b,_uZ,_));return new T(function(){return B(A1(_uX,_v0));});};return new T2(3,_uR.a,_uY);}break;case 1:var _v1=_uP.a,_v2=E(_um);switch(_v2._){case 0:var _v3=function(_){var _v4=B(A1(_v1,_));return new T(function(){return B(A2(_uk,_v4,_v2.a));});};return new T1(1,_v3);case 1:return new T1(1,function(_){return new F(function(){return _u9(_uk,_v1,_v2.a,_);});});case 2:var _v5=function(_v6,_){var _v7=B(A1(_v1,_));return new T(function(){return B(A2(_uk,_v7,new T(function(){return B(A1(_v2.b,_v6));})));});};return new T2(3,_v2.a,_v5);default:var _v8=function(_v9,_){var _va=B(A1(_v1,_)),_vb=B(A2(_v2.b,_v9,_));return new T(function(){return B(A2(_uk,_va,_vb));});};return new T2(3,_v2.a,_v8);}break;case 2:var _vc=_uP.a,_vd=_uP.b,_ve=E(_um);switch(_ve._){case 0:var _vf=function(_vg){return new F(function(){return A2(_uk,new T(function(){return B(A1(_vd,_vg));}),_ve.a);});};return new T2(2,_vc,_vf);case 1:var _vh=function(_vi,_){var _vj=B(A1(_ve.a,_));return new T(function(){return B(A2(_uk,new T(function(){return B(A1(_vd,_vi));}),_vj));});};return new T2(3,_vc,_vh);default:return new F(function(){return _un(_);});}break;default:var _vk=_uP.a,_vl=_uP.b,_vm=E(_um);switch(_vm._){case 0:var _vn=function(_vo,_){var _vp=B(A2(_vl,_vo,_));return new T(function(){return B(A2(_uk,_vp,_vm.a));});};return new T2(3,_vk,_vn);case 1:var _vq=function(_vr,_){var _vs=B(A2(_vl,_vr,_)),_vt=B(A1(_vm.a,_));return new T(function(){return B(A2(_uk,_vs,_vt));});};return new T2(3,_vk,_vq);default:return new F(function(){return _un(_);});}}},_vu=function(_vv,_vw){return E(_vv)*E(_vw);},_vx=new T(function(){return B(_uj(_vu,_sC,_u8));}),_vy=2,_vz=new T1(0,_vy),_vA=new T(function(){return B(_uj(_in,_sC,_vz));}),_vB=new T(function(){return B(_uj(_vu,_sC,_u2));}),_vC=15,_vD=6,_vE=function(_vF){var _vG=E(_vF);return new T0(2);},_vH=new T4(0,_vD,_vD,_iq,_av),_vI=new T2(0,_vD,_vH),_vJ=new T2(0,_vI,_6),_vK=10,_vL=3,_vM=new T1(0,_vL),_vN=5,_vO=new T1(0,_vN),_vP=new T4(0,_sA,_sA,_sA,_u2),_vQ=function(_vR,_vS,_vT,_){var _vU=__app2(E(_qm),E(_vS),E(_vT));return new F(function(){return _jl(_);});},_vV=function(_vW,_vX,_vY,_vZ,_w0,_w1,_w2){var _w3=function(_w4,_w5,_w6,_){var _w7=function(_w8,_w9,_wa,_){var _wb=function(_wc,_wd,_we,_){var _wf=function(_wg,_wh,_wi,_){return new F(function(){return _q9(_w0,function(_wj,_wk,_wl,_){return new F(function(){return _q9(_w1,_vQ,_wk,_wl,_);});},_wh,_wi,_);});};return new F(function(){return _q9(_vZ,_wf,_wd,_we,_);});};return new F(function(){return _q9(_vY,_wb,_w9,_wa,_);});};return new F(function(){return _q9(_vX,_w7,_w5,_w6,_);});},_wm=function(_wn,_){var _wo=E(_wn),_wp=_wo.a,_wq=_wo.b,_wr=function(_ws,_){var _wt=function(_wu,_){var _wv=function(_ww,_){var _wx=function(_wy,_){var _wz=function(_wA,_){var _wB=function(_wC){var _wD=new T(function(){return E(_wu)*E(_wy)-E(_ws)*E(_wA);});return new F(function(){return A1(_w2,new T2(0,new T(function(){var _wE=E(_wu),_wF=E(_wA);return ( -(_wE*E(_wC))+_wE*E(_wq)+_wF*E(_ww)-_wF*E(_wp))/E(_wD);}),new T(function(){var _wG=E(_ws),_wH=E(_wy);return (_wG*E(_wC)-_wG*E(_wq)-_wH*E(_ww)+_wH*E(_wp))/E(_wD);})));});};return new F(function(){return _rz(_w1,_wB,_);});};return new F(function(){return _rz(_w0,_wz,_);});};return new F(function(){return _rz(_vZ,_wx,_);});};return new F(function(){return _rz(_vY,_wv,_);});};return new F(function(){return _rz(_vX,_wt,_);});};return new F(function(){return _rz(_vW,_wr,_);});};return new T3(0,_wm,function(_rg,_rh,_){return new F(function(){return _q9(_vW,_w3,_rg,_rh,_);});},_7);},_wI=1,_wJ=function(_wK,_wL){var _wM=new T(function(){var _wN=function(_wO,_wP,_wQ){return new F(function(){return A1(_wQ,new T2(0,new T2(0,_7,new T2(0,_wL,new T4(0,_wL,_wL,_wI,new T(function(){return E(E(E(_wO).b).d);})))),_wP));});};return B(_9I(_8l,_wK,_wN));}),_wR=function(_wS,_wT){var _wU=new T(function(){return B(A2(_wM,_wS,_wT));}),_wV=function(_wW){var _wX=new T(function(){var _wY=E(_wW),_wZ=E(_wY.a),_x0=E(_wY.b),_x1=E(_x0.a),_x2=E(_x0.b),_x3=E(_x0.c),_x4=E(_x0.d);return E(_wU);});return new T1(0,B(_2K(_wK,_wW,function(_x5){return E(_wX);})));};return new T1(0,B(_8B(_wK,_wV)));};return E(_wR);},_x6=function(_x7,_x8,_x9){var _xa=E(_x8),_xb=E(_x9);switch(_xb._){case 0:var _xc=_xb.a,_xd=_xb.b,_xe=_xb.c,_xf=_xb.d,_xg=_xd>>>0;if(((_x7>>>0&((_xg-1>>>0^4294967295)>>>0^_xg)>>>0)>>>0&4294967295)==_xc){return ((_x7>>>0&_xg)>>>0==0)?new T4(0,_xc,_xd,E(B(_x6(_x7,_xa,_xe))),E(_xf)):new T4(0,_xc,_xd,E(_xe),E(B(_x6(_x7,_xa,_xf))));}else{var _xh=(_x7>>>0^_xc>>>0)>>>0,_xi=(_xh|_xh>>>1)>>>0,_xj=(_xi|_xi>>>2)>>>0,_xk=(_xj|_xj>>>4)>>>0,_xl=(_xk|_xk>>>8)>>>0,_xm=(_xl|_xl>>>16)>>>0,_xn=(_xm^_xm>>>1)>>>0&4294967295,_xo=_xn>>>0;return ((_x7>>>0&_xo)>>>0==0)?new T4(0,(_x7>>>0&((_xo-1>>>0^4294967295)>>>0^_xo)>>>0)>>>0&4294967295,_xn,E(new T2(1,_x7,_xa)),E(_xb)):new T4(0,(_x7>>>0&((_xo-1>>>0^4294967295)>>>0^_xo)>>>0)>>>0&4294967295,_xn,E(_xb),E(new T2(1,_x7,_xa)));}break;case 1:var _xp=_xb.a;if(_x7!=_xp){var _xq=(_x7>>>0^_xp>>>0)>>>0,_xr=(_xq|_xq>>>1)>>>0,_xs=(_xr|_xr>>>2)>>>0,_xt=(_xs|_xs>>>4)>>>0,_xu=(_xt|_xt>>>8)>>>0,_xv=(_xu|_xu>>>16)>>>0,_xw=(_xv^_xv>>>1)>>>0&4294967295,_xx=_xw>>>0;return ((_x7>>>0&_xx)>>>0==0)?new T4(0,(_x7>>>0&((_xx-1>>>0^4294967295)>>>0^_xx)>>>0)>>>0&4294967295,_xw,E(new T2(1,_x7,_xa)),E(_xb)):new T4(0,(_x7>>>0&((_xx-1>>>0^4294967295)>>>0^_xx)>>>0)>>>0&4294967295,_xw,E(_xb),E(new T2(1,_x7,_xa)));}else{return new T2(1,_x7,_xa);}break;default:return new T2(1,_x7,_xa);}},_xy=6,_xz=4,_xA=0,_xB=1,_xC=3,_xD=5,_xE=function(_xF,_xG){return new F(function(){return A1(_xG,new T2(0,_7,_xF));});},_xH=new T1(1,_6),_xI=0,_xJ=new T4(0,_xI,_xI,_iq,_av),_xK=new T2(0,_xI,_xJ),_xL=new T2(0,_xK,_6),_xM=1,_xN=new T4(0,_xM,_xM,_iq,_av),_xO=new T2(0,_xM,_xN),_xP=new T2(0,_xO,_6),_xQ=function(_xR){return E(E(_xR).c);},_xS=new T1(1,_6),_xT=function(_xU){var _xV=function(_){var _xW=nMV(_xS);return new T(function(){return B(A1(_xU,_xW));});};return new T1(0,_xV);},_xX=function(_xY,_xZ){var _y0=new T(function(){return B(_xQ(_xY));}),_y1=B(_9x(_xY)),_y2=function(_y3){var _y4=new T(function(){return B(A1(_y0,new T(function(){return B(A1(_xZ,_y3));})));});return new F(function(){return A3(_9z,_y1,_y4,new T(function(){return B(A2(_6T,_y1,_y3));}));});};return new F(function(){return A3(_6u,_y1,new T(function(){return B(A2(_2V,_xY,_xT));}),_y2);});},_y5=function(_y6,_y7,_y8,_y9){var _ya=new T(function(){return B(A1(_y6,_sN));}),_yb=new T(function(){return B(A1(_y6,_xA));}),_yc=new T(function(){return B(A1(_y6,_xz));}),_yd=new T(function(){return B(_xX(_8l,_y9));}),_ye=new T(function(){return B(A1(_y6,_xy));}),_yf=new T(function(){return B(A1(_y6,_xD));}),_yg=new T(function(){return B(A1(_y6,_xC));}),_yh=new T(function(){return B(A1(_y6,_xB));}),_yi=function(_yj){var _yk=new T(function(){return B(A1(_yd,_yj));}),_yl=function(_ym){var _yn=function(_yo){var _yp=E(_yo),_yq=_yp.a,_yr=_yp.b,_ys=new T(function(){var _yt=E(_ya);if(!_yt._){return E(_xE);}else{return B(_2X(_8l,_yq,_yt.a));}}),_yu=new T(function(){var _yv=E(_yb);if(!_yv._){return E(_xE);}else{return B(_2X(_8l,_yq,_yv.a));}}),_yw=new T(function(){var _yx=E(_yc);if(!_yx._){return E(_xE);}else{return B(_2X(_8l,_yq,_yx.a));}}),_yy=new T(function(){var _yz=E(_ye);if(!_yz._){return E(_xE);}else{return B(_2X(_8l,_yq,_yz.a));}}),_yA=new T(function(){var _yB=E(_yf);if(!_yB._){return E(_xE);}else{return B(_2X(_8l,_yq,_yB.a));}}),_yC=new T(function(){var _yD=E(_yg);if(!_yD._){return E(_xE);}else{return B(_2X(_8l,_yq,_yD.a));}}),_yE=new T(function(){var _yF=E(_yh);if(!_yF._){return E(_xE);}else{return B(_2X(_8l,_yq,_yF.a));}}),_yG=function(_){var _yH=nMV(_xP),_yI=_yH,_yJ=function(_){var _yK=nMV(_xL),_yL=_yK,_yM=function(_){var _yN=nMV(_xL),_yO=_yN,_yP=function(_){var _yQ=nMV(_xL),_yR=_yQ,_yS=function(_){var _yT=nMV(_xP),_yU=_yT,_yV=function(_){var _yW=nMV(_xL),_yX=_yW,_yY=new T(function(){var _yZ=function(_z0,_z1,_z2,_z3,_z4,_z5){var _z6=new T(function(){return B(_wJ(_yI,_z0));}),_z7=new T(function(){return B(_wJ(_yL,_z1));}),_z8=new T(function(){return B(_wJ(_yO,_z2));}),_z9=new T(function(){return B(_wJ(_yR,_z3));}),_za=new T(function(){return B(_wJ(_yU,_z4));}),_zb=new T(function(){return B(_wJ(_yX,_z5));}),_zc=function(_zd){var _ze=new T(function(){return B(A1(_z6,_zd));}),_zf=function(_zg){var _zh=function(_zi){return new F(function(){return A1(_zg,new T2(0,_7,E(_zi).b));});},_zj=function(_zk){return new F(function(){return A2(_zb,E(_zk).b,_zh);});},_zl=function(_zm){return new F(function(){return A2(_za,E(_zm).b,_zj);});},_zn=function(_zo){return new F(function(){return A2(_z9,E(_zo).b,_zl);});},_zp=function(_zq){return new F(function(){return A2(_z8,E(_zq).b,_zn);});};return new F(function(){return A1(_ze,function(_zr){return new F(function(){return A2(_z7,E(_zr).b,_zp);});});});};return E(_zf);};return E(_zc);};return B(_pg(new T2(2,_yZ,_7)));}),_zs=new T(function(){var _zt=E(_y8);return new T2(0,E(_zt.a),E(new T2(2,_zt.b,new T1(1,function(_zu){return E(_yY);}))));}),_zv=new T(function(){var _zw=B(_vV(new T2(2,new T3(0,_wI,_tX,_yI),_2E),new T2(2,new T3(0,_wI,_tX,_yL),_2E),new T2(2,new T3(0,_wI,_tX,_yO),_2E),new T2(2,new T3(0,_wI,_tX,_yR),_2E),new T2(2,new T3(0,_wI,_tX,_yU),_2E),new T2(2,new T3(0,_wI,_tX,_yX),_2E),E(_y7).a));return new T3(0,_zw.a,_zw.b,_zw.c);}),_zx=function(_){var _zy=nMV(_xH),_zz=_zy,_zA=new T(function(){var _zB=function(_zC){return new F(function(){return _zD(E(_zC).b);});},_zE=function(_zF){var _zG=new T(function(){return B(A2(_yE,_zF,_zH));}),_zI=new T(function(){return B(A2(_ys,_zF,_zB));}),_zJ=new T(function(){return B(A2(_yC,_zF,_zK));}),_zL=new T(function(){return B(_zE(_zF));}),_zM=function(_zN){var _zO=E(_zN);if(!_zO._){return (!E(_zO.a))?E(_zL):E(_zJ);}else{var _zP=function(_){var _zQ=B(A2(E(_zv).a,_zO.a,_));return new T(function(){if(!E(_zQ)){return E(_zI);}else{return E(_zG);}});};return new T1(0,_zP);}};return new T1(0,B(_8B(_zz,_zM)));},_zH=function(_zR){return new F(function(){return _zE(E(_zR).b);});},_zD=function(_zS){var _zT=new T(function(){return B(_zD(_zS));}),_zU=new T(function(){return B(A2(_yu,_zS,_zH));}),_zV=function(_zW){var _zX=E(_zW);if(!_zX._){return E(_zT);}else{var _zY=function(_){var _zZ=B(A2(E(_zv).a,_zX.a,_));return new T(function(){if(!E(_zZ)){return E(_zT);}else{return E(_zU);}});};return new T1(0,_zY);}};return new T1(0,B(_8B(_zz,_zV)));},_A0=function(_A1){var _A2=new T(function(){return B(A2(_yw,_A1,_zK));}),_A3=new T(function(){return B(A2(_ys,_A1,_A4));}),_A5=new T(function(){return B(_A0(_A1));}),_A6=new T(function(){return B(A2(_yA,_A1,_zH));}),_A7=function(_A8){var _A9=E(_A8);if(!_A9._){return (!E(_A9.a))?E(_A6):E(_A5);}else{var _Aa=function(_){var _Ab=B(A2(E(_zv).a,_A9.a,_));return new T(function(){if(!E(_Ab)){return E(_A3);}else{return E(_A2);}});};return new T1(0,_Aa);}};return new T1(0,B(_8B(_zz,_A7)));},_zK=function(_Ac){return new F(function(){return _A0(E(_Ac).b);});},_Ad=function(_Ae){var _Af=new T(function(){return B(A2(_yu,_Ae,_zK));}),_Ag=new T(function(){return B(A2(_yw,_Ae,_A4));}),_Ah=new T(function(){return B(_Ad(_Ae));}),_Ai=new T(function(){return B(A2(_yy,_Ae,_zB));}),_Aj=function(_Ak){var _Al=E(_Ak);if(!_Al._){return (!E(_Al.a))?E(_Ai):E(_Ah);}else{var _Am=function(_){var _An=B(A2(E(_zv).a,_Al.a,_));return new T(function(){if(!E(_An)){return E(_Ag);}else{return E(_Af);}});};return new T1(0,_Am);}};return new T1(0,B(_8B(_zz,_Aj)));},_A4=function(_Ao){return new F(function(){return _Ad(E(_Ao).b);});};return B(_zD(_yr));}),_Ap=new T(function(){var _Aq=function(_Ar){var _As=E(_Ar);return new F(function(){return A1(_ym,new T2(0,new T(function(){return new T3(0,E(_As.a),_zs,E(_yq));}),_As.b));});},_At=function(_Au,_Av,_Aw){var _Ax=new T(function(){return E(E(_Au).d);}),_Ay=new T(function(){return E(E(_Ax).a);}),_Az=new T(function(){var _AA=E(_Au);return new T4(0,E(_AA.a),_AA.b,E(_AA.c),E(new T2(0,new T(function(){return E(_Ay)+1|0;}),new T(function(){return B(_x6(E(_Ay),_zz,E(_Ax).b));}))));});return new F(function(){return A1(_Aw,new T2(0,new T2(0,_Ay,_Az),_Av));});};return B(A(_9I,[_8l,_yr,_At,_yr,_Aq]));});return new T1(1,new T2(1,_Ap,new T2(1,_zA,_6)));};return new T1(0,_zx);};return new T1(0,_yV);};return new T1(0,_yS);};return new T1(0,_yP);};return new T1(0,_yM);};return new T1(0,_yJ);};return new T1(0,_yG);};return new F(function(){return A1(_yk,_yn);});};return E(_yl);};return E(_yi);},_AB=function(_AC,_AD,_AE){var _AF=new T(function(){var _AG=new T(function(){return B(_ro(_u5,new T(function(){var _AH=B(_qC(_u6,new T1(0,_AE),_rl,_ri,_vx,_vA,_vB));return new T3(0,_AH.a,_AH.b,_AH.c);})));});return B(_pH(_sA,_vM,_vO,_vP,_AG));}),_AI=function(_AJ){return E(_AF);},_AK=new T(function(){return B(A1(_AD,_AC));}),_AL=function(_AM){var _AN=new T(function(){return B(A1(_AK,_AM));}),_AO=function(_AP){var _AQ=function(_AR){var _AS=E(_AR),_AT=E(_AS.a),_AU=new T(function(){var _AV=B(_tF(_sD,_AT.a));return new T2(0,E(_AV.a),E(new T2(2,_AV.b,new T1(1,_AI))));}),_AW=function(_){var _AX=nMV(_vJ);return new T(function(){var _AY=new T(function(){return B(_iB(_id,_vK,_u0,_AX,_vD,_tT));}),_AZ=new T(function(){return B(_iB(_id,_vK,_u0,_AX,_vC,_tT));}),_B0=function(_B1){var _B2=new T(function(){return B(_t0(_AY,_AZ,_sI,_B1));}),_B3=function(_B4,_B5){return new T1(1,new T2(1,new T(function(){return B(A2(_B2,_B4,_B5));}),new T2(1,new T(function(){return B(A2(_AT.b,_B4,_vE));}),_6)));};return E(_B3);},_B6=new T(function(){var _B7=B(_pH(_sA,_vM,new T2(2,new T3(0,_vK,_u0,_AX),_2E),_sM,_sH));return new T2(0,E(_B7.a),E(new T2(2,_B7.b,new T1(1,function(_B8){return E(_AU);}))));});return B(A(_y5,[_rj,_sD,_B6,_B0,_AS.b,_AP]));});};return new T1(0,_AW);};return new F(function(){return A1(_AN,_AQ);});};return E(_AO);};return E(_AL);},_B9=new T1(1,_6),_Ba=function(_Bb,_Bc,_Bd){return function(_){var _Be=nMV(_B9),_Bf=_Be;return new T(function(){var _Bg=function(_Bh){var _Bi=new T(function(){return B(A1(_Bd,new T2(0,_7,E(_Bh).b)));}),_Bj=function(_Bk){return E(_Bi);};return new T1(0,B(_8B(_Bf,function(_Bl){return new T1(0,B(_9p(_cp,_Bj)));})));},_Bm=function(_Bn,_Bo){return new T1(0,B(_2K(_Bf,_7,function(_Bp){return new F(function(){return A1(_Bo,new T2(0,_Bp,_Bn));});})));};return B(A3(_Bb,_Bm,_Bc,_Bg));});};},_Bq=100,_Br=function(_Bs,_Bt){var _Bu=B(A1(_Bs,new T(function(){return 1-(1-E(_Bt));})));return 1-(1-_Bu*_Bu);},_Bv=20,_Bw=function(_Bx,_By){var _Bz=B(A1(_Bx,new T(function(){return 1-E(_By);})));return 1-_Bz*_Bz;},_BA=50,_BB=3,_BC=function(_BD){return  -E(_BD);},_BE=0,_BF=new T4(0,_BE,_BE,_iq,_av),_BG=new T2(0,_BE,_BF),_BH=new T2(0,_BG,_6),_BI=new T4(0,_Bq,_Bq,_iq,_av),_BJ=new T2(0,_Bq,_BI),_BK=new T2(0,_BJ,_6),_BL=-30,_BM=30,_BN=-10,_BO=0,_BP=new T1(0,_Bq),_BQ=50,_BR=new T1(0,_BQ),_BS=75,_BT=new T1(0,_BS),_BU=function(_BV,_BW){return E(_BV)+E(_BW);},_BX=0,_BY=function(_BZ,_C0,_C1){var _C2=function(_C3){var _C4=E(_C3),_C5=_C4.b,_C6=new T(function(){return E(_C4.a)+E(_BZ)|0;}),_C7=function(_){var _C8=nMV(_B9),_C9=_C8;return new T(function(){var _Ca=function(_Cb){var _Cc=new T(function(){return B(A1(_C1,new T2(0,_7,E(_Cb).b)));});return new T1(0,B(_8B(_C9,function(_Cd){return E(_Cc);})));},_Ce=new T2(0,_C6,_C9),_Cf=function(_Cg){var _Ch=new T(function(){var _Ci=E(_Cg),_Cj=E(_Ci.c);if(!_Cj._){var _Ck=E(new T3(1,1,_Ce,E(_aC)));}else{var _Cl=_Cj.a,_Cm=_Cj.c,_Cn=E(_Cj.b),_Co=E(_C6),_Cp=E(_Cn.a);if(_Co>=_Cp){if(_Co!=_Cp){var _Cq=new T3(1,_Cl+1|0,_Cn,E(B(_aD(function(_Cr,_Cs){var _Ct=E(E(_Cr).a),_Cu=E(E(_Cs).a);return (_Ct>=_Cu)?_Ct==_Cu:true;},_Ce,_BX,_Cm))));}else{var _Cq=new T3(1,_Cl+1|0,_Ce,E(B(_aD(function(_Cv,_Cw){var _Cx=E(E(_Cv).a),_Cy=E(E(_Cw).a);return (_Cx>=_Cy)?_Cx==_Cy:true;},_Cn,_BX,_Cm))));}var _Cz=_Cq;}else{var _Cz=new T3(1,_Cl+1|0,_Ce,E(B(_aD(function(_CA,_CB){var _CC=E(E(_CA).a),_CD=E(E(_CB).a);return (_CC>=_CD)?_CC==_CD:true;},_Cn,_BX,_Cm))));}var _Ck=_Cz;}return new T4(0,E(_Ci.a),_Ci.b,E(_Ck),E(_Ci.d));});return function(_CE,_CF){return new F(function(){return A1(_CF,new T2(0,new T2(0,_7,_Ch),_CE));});};};return B(A(_9I,[_8l,_C5,_Cf,_C5,_Ca]));});};return new T1(0,_C7);};return new F(function(){return A(_9I,[_8l,_C0,_ar,_C0,_C2]);});},_CG=function(_CH,_CI,_CJ){return function(_){var _CK=nMV(_BK),_CL=_CK,_CM=function(_CN){return new F(function(){return _iB(_id,_Bv,_Br,_CL,_Bq,function(_CO){return E(_CN);});});},_CP=function(_CQ){return new F(function(){return _iB(_id,_Bv,_Bw,_CL,_BM,function(_CR){return E(_CQ);});});},_CS=function(_){var _CT=nMV(_BH),_CU=_CT,_CV=new T3(0,_wI,_tX,_CU),_CW=function(_){var _CX=nMV(_BH),_CY=_CX,_CZ=function(_){var _D0=nMV(_BH),_D1=_D0,_D2=new T3(0,_wI,_tX,_D1),_D3=function(_){var _D4=nMV(_BH),_D5=_D4,_D6=function(_){var _D7=nMV(_BH),_D8=_D7,_D9=function(_){var _Da=nMV(_BH),_Db=_Da,_Dc=function(_){var _Dd=nMV(_BH),_De=_Dd,_Df=new T(function(){return B(_wJ(_De,_BL));}),_Dg=function(_){var _Dh=nMV(_BH),_Di=_Dh,_Dj=function(_){var _Dk=nMV(_BH),_Dl=_Dk,_Dm=new T(function(){return B(_wJ(_Dl,_BB));}),_Dn=function(_){var _Do=nMV(_BH),_Dp=_Do,_Dq=new T(function(){return B(_wJ(_Dp,_BB));}),_Dr=function(_){var _Ds=nMV(_BH),_Dt=_Ds,_Du=function(_){var _Dv=nMV(_BH),_Dw=_Dv;return new T(function(){var _Dx=function(_Dy){return new F(function(){return _Dz(E(_Dy).b);});},_DA=function(_DB){return new F(function(){return _BY(_BO,E(_DB).b,_Dx);});},_Dz=function(_DC){var _DD=function(_DE){var _DF=new T(function(){var _DG=function(_DH){var _DI=new T(function(){var _DJ=function(_DK){var _DL=new T(function(){var _DM=function(_DN){var _DO=new T(function(){var _DP=function(_DQ){var _DR=new T(function(){var _DS=new T(function(){return E(E(_DQ).a);}),_DT=new T(function(){return B(_wJ(_CU,new T(function(){return (E(E(_DE).a)+E(_DS))*0.7;})));}),_DU=function(_DV){var _DW=new T(function(){var _DX=new T(function(){return E(E(_DV).a);}),_DY=new T(function(){return B(_wJ(_CY,new T(function(){return (E(E(_DH).a)+E(_DX))*0.7;})));}),_DZ=function(_E0){var _E1=new T(function(){var _E2=new T(function(){return E(E(_E0).a);}),_E3=new T(function(){return B(_wJ(_D1,new T(function(){return (E(E(_DK).a)+E(_E2))*0.7;})));}),_E4=function(_E5){var _E6=new T(function(){var _E7=new T(function(){return E(E(_E5).a);}),_E8=new T(function(){return B(_wJ(_D5,new T(function(){return (E(E(_DN).a)+E(_E7))*0.7;})));}),_E9=function(_Ea){return new F(function(){return A2(_E8,E(_Ea).b,_DA);});},_Eb=function(_Ec){return new F(function(){return A2(_E3,E(_Ec).b,_E9);});},_Ed=function(_Ee){return new F(function(){return A2(_DY,E(_Ee).b,_Eb);});},_Ef=function(_Eg){return new F(function(){return A2(_DT,E(_Eg).b,_Ed);});},_Eh=function(_Ei){var _Ej=new T(function(){var _Ek=new T(function(){return E(E(_Ei).a);}),_El=new T(function(){return B(_wJ(_Dl,new T(function(){return E(_Ek)*0.7;})));}),_Em=new T(function(){return B(_wJ(_D8,new T(function(){return (E(_DS)+E(_Ek))*0.7;})));}),_En=function(_Eo){var _Ep=new T(function(){var _Eq=new T(function(){return E(E(_Eo).a);}),_Er=new T(function(){return B(_wJ(_Dp,new T(function(){return E(_Eq)*0.7;})));}),_Es=new T(function(){return B(_wJ(_Db,new T(function(){return (E(_DX)+E(_Eq))*0.7;})));}),_Et=function(_Eu){var _Ev=new T(function(){var _Ew=new T(function(){return E(E(_Eu).a);}),_Ex=new T(function(){return B(_wJ(_Dt,new T(function(){return E(_Ew)*0.7;})));}),_Ey=new T(function(){return B(_wJ(_De,new T(function(){return (E(_E2)+E(_Ew))*0.7;})));}),_Ez=function(_EA){var _EB=new T(function(){var _EC=new T(function(){return E(E(_EA).a);}),_ED=new T(function(){return B(_wJ(_Dw,new T(function(){return E(_EC)*0.7;})));}),_EE=new T(function(){return B(_wJ(_Di,new T(function(){return (E(_E7)+E(_EC))*0.7;})));}),_EF=function(_EG){return new F(function(){return A2(_EE,E(_EG).b,_Ef);});},_EH=function(_EI){return new F(function(){return A2(_Ey,E(_EI).b,_EF);});},_EJ=function(_EK){return new F(function(){return A2(_Es,E(_EK).b,_EH);});},_EL=function(_EM){return new F(function(){return A2(_Em,E(_EM).b,_EJ);});},_EN=function(_EO){return new F(function(){return A2(_ED,E(_EO).b,_EL);});},_EP=function(_EQ){return new F(function(){return A2(_Ex,E(_EQ).b,_EN);});};return B(A2(_El,_DC,function(_ER){return new F(function(){return A2(_Er,E(_ER).b,_EP);});}));});return new T1(0,B(_2K(_Dw,_EA,function(_ES){return E(_EB);})));};return new T1(0,B(_8B(_Dw,_Ez)));});return new T1(0,B(_2K(_Dt,_Eu,function(_ET){return E(_Ev);})));};return new T1(0,B(_8B(_Dt,_Et)));});return new T1(0,B(_2K(_Dp,_Eo,function(_EU){return E(_Ep);})));};return new T1(0,B(_8B(_Dp,_En)));});return new T1(0,B(_2K(_Dl,_Ei,function(_EV){return E(_Ej);})));};return new T1(0,B(_8B(_Dl,_Eh)));});return new T1(0,B(_2K(_Di,_E5,function(_EW){return E(_E6);})));};return new T1(0,B(_8B(_Di,_E4)));});return new T1(0,B(_2K(_De,_E0,function(_EX){return E(_E1);})));};return new T1(0,B(_8B(_De,_DZ)));});return new T1(0,B(_2K(_Db,_DV,function(_EY){return E(_DW);})));};return new T1(0,B(_8B(_Db,_DU)));});return new T1(0,B(_2K(_D8,_DQ,function(_EZ){return E(_DR);})));};return new T1(0,B(_8B(_D8,_DP)));});return new T1(0,B(_2K(_D5,_DN,function(_F0){return E(_DO);})));};return new T1(0,B(_8B(_D5,_DM)));});return new T1(0,B(_2K(_D1,_DK,function(_F1){return E(_DL);})));};return new T1(0,B(_8B(_D1,_DJ)));});return new T1(0,B(_2K(_CY,_DH,function(_F2){return E(_DI);})));};return new T1(0,B(_8B(_CY,_DG)));});return new T1(0,B(_2K(_CU,_DE,function(_F3){return E(_DF);})));};return new T1(0,B(_8B(_CU,_DD)));},_F4=new T(function(){return B(_wJ(_Dw,_BN));}),_F5=function(_F6){return new F(function(){return _F7(E(_F6).b);});},_F8=function(_F9){return new F(function(){return _BY(_BA,E(_F9).b,_F5);});},_Fa=function(_Fb){return new F(function(){return A2(_Dq,E(_Fb).b,_F8);});},_Fc=function(_Fd){return new F(function(){return A2(_Dm,E(_Fd).b,_Fa);});},_Fe=function(_Ff){return new F(function(){return A2(_Df,E(_Ff).b,_Fc);});},_Fg=function(_Fh){return new T1(0,B(_Ba(_CM,E(_Fh).b,_Fe)));},_Fi=function(_Fj){return new T1(0,B(_Ba(_CP,E(_Fj).b,_Fg)));},_F7=function(_Fk){return new F(function(){return A2(_F4,_Fk,_Fi);});},_Fl=function(_Fm,_Fn){return new T1(1,new T2(1,new T(function(){return B(_F7(_Fm));}),new T2(1,new T(function(){return B(_Dz(_Fm));}),_6)));},_Fo=new T(function(){var _Fp=new T(function(){var _Fq=B(_rM(new T(function(){return B(_uj(_BU,_BT,new T2(2,_CV,_BC)));}),new T(function(){return B(_uj(_BU,new T2(2,new T3(0,_Bv,_Bw,_CL),_2E),new T2(2,_D2,_BC)));}),new T(function(){return B(_uj(_BU,B(_uj(_BU,_BR,new T2(2,_CV,_2E))),new T2(2,new T3(0,_wI,_tX,_CY),_2E)));}),new T(function(){return B(_uj(_BU,B(_uj(_BU,_BP,new T2(2,_D2,_2E))),new T2(2,new T3(0,_wI,_tX,_D5),_2E)));})));return new T3(0,_Fq.a,_Fq.b,_Fq.c);});return B(_ro(_CH,_Fp));});return B(A1(_CJ,new T2(0,new T2(0,_Fo,_Fl),_CI)));});};return new T1(0,_Du);};return new T1(0,_Dr);};return new T1(0,_Dn);};return new T1(0,_Dj);};return new T1(0,_Dg);};return new T1(0,_Dc);};return new T1(0,_D9);};return new T1(0,_D6);};return new T1(0,_D3);};return new T1(0,_CZ);};return new T1(0,_CW);};return new T1(0,_CS);};},_Fr=function(_Fs,_Ft,_Fu){return new T1(0,B(_CG(_Fs,_Ft,_Fu)));},_Fv=0.3,_Fw=new T1(0,_Fv),_Fx=new T4(0,_sA,_Fw,_u4,_u4),_Fy=new T(function(){return B(unCStr("Bounce"));}),_Fz=new T(function(){return B(_AB(_Fx,_Fr,_Fy));}),_FA=function(_FB){return  -E(_FB);},_FC=function(_FD,_FE,_FF,_FG){var _FH=new T(function(){var _FI=new T(function(){var _FJ=new T(function(){var _FK=E(_FF);switch(_FK._){case 0:return new T1(0,new T(function(){return  -E(_FK.a);}));break;case 1:var _FL=function(_){var _FM=B(A1(_FK.a,_));return new T(function(){return B(_FA(_FM));});};return new T1(1,_FL);break;case 2:return new T2(2,_FK.a,function(_FN){return  -B(A1(_FK.b,_FN));});break;default:var _FO=function(_FP,_){var _FQ=B(A2(_FK.b,_FP,_));return new T(function(){return B(_FA(_FQ));});};return new T2(3,_FK.a,_FO);}}),_FR=new T(function(){var _FS=E(_FE);switch(_FS._){case 0:return new T1(0,new T(function(){return  -E(_FS.a);}));break;case 1:var _FT=function(_){var _FU=B(A1(_FS.a,_));return new T(function(){return B(_FA(_FU));});};return new T1(1,_FT);break;case 2:return new T2(2,_FS.a,function(_FV){return  -B(A1(_FS.b,_FV));});break;default:var _FW=function(_FX,_){var _FY=B(A2(_FS.b,_FX,_));return new T(function(){return B(_FA(_FY));});};return new T2(3,_FS.a,_FW);}});return B(_pg(new T3(5,new T2(0,_FR,_FJ),_FG,_7)));});return B(_pg(new T3(7,_FD,_FI,_7)));});return new F(function(){return _pg(new T3(5,new T2(0,_FE,_FF),_FH,_7));});},_FZ=0,_G0=20,_G1=0.9999999999999998,_G2=new T4(0,_FZ,_FZ,_iq,_av),_G3=new T2(0,_FZ,_G2),_G4=new T2(0,_G3,_6),_G5=function(_G6,_G7,_G8){return function(_){var _G9=nMV(_G4);return new T(function(){var _Ga=function(_Gb,_Gc){return 1-B(A1(_Gb,new T(function(){var _Gd=E(_Gc)/0.3-_G6/4*2.3333333333333335;if(1>_Gd){if(0>_Gd){return E(_G1);}else{var _Ge=1-_Gd;return _Ge*_Ge*(2.70158*_Ge-1.70158);}}else{return E(_FZ);}})));},_Gf=new T3(0,_G0,function(_Gg,_Gh){return new F(function(){return _Ga(_Gg,_Gh);});},_G9),_Gi=E(_G6);if(_Gi==4){return B(A1(_G8,new T2(0,new T2(1,_Gf,_6),_G7)));}else{return new T1(0,B(_G5(_Gi+1|0,_G7,function(_Gj){var _Gk=E(_Gj);return new F(function(){return A1(_G8,new T2(0,new T2(1,_Gf,_Gk.a),_Gk.b));});})));}});};},_Gl=function(_Gm,_Gn,_Go,_Gp){var _Gq=function(_Gr,_Gs,_Gt,_){var _Gu=function(_Gv,_Gw,_Gx,_){var _Gy=function(_Gz){var _GA=new T(function(){return E(_Gz)/2;}),_GB=function(_GC,_GD,_GE,_){var _GF=E(_Gr),_GG=E(_GA),_GH=_GF+_GG,_GI=_GF-_GG,_GJ=E(_Gv),_GK=E(_GC)/2,_GL=_GJ+_GK,_GM=_GJ-_GK,_GN=E(_GD),_GO=E(_GE),_GP=__app4(E(_rK),_GI,_GM,_GN,_GO),_GQ=E(_rL),_GR=__app4(_GQ,_GH,_GJ-_GK,_GN,_GO),_GS=__app4(_GQ,_GH,_GL,_GN,_GO),_GT=__app4(_GQ,_GF-_GG,_GL,_GN,_GO),_GU=__app4(_GQ,_GI,_GM,_GN,_GO);return new F(function(){return _jl(_);});};return function(_gd,_ge,_GV){return new F(function(){return _q9(_Gp,_GB,_gd,_ge,_GV);});};};return new F(function(){return _q9(_Go,_Gy,_Gw,_Gx,_);});};return new F(function(){return _q9(_Gn,_Gu,_Gs,_Gt,_);});},_GW=function(_GX,_){var _GY=E(_GX),_GZ=function(_H0,_){var _H1=function(_H2,_){var _H3=function(_H4,_){var _H5=function(_H6,_){return new T(function(){var _H7=function(_H8){if(_H8>=E(_H4)/2){return false;}else{var _H9=E(_GY.b)-E(_H2);return (_H9==0)?0<E(_H6)/2:(_H9<=0)? -_H9<E(_H6)/2:_H9<E(_H6)/2;}},_Ha=E(_GY.a)-E(_H0);if(!_Ha){return B(_H7(0));}else{if(_Ha<=0){return B(_H7( -_Ha));}else{return B(_H7(_Ha));}}});};return new F(function(){return _rz(_Gp,_H5,_);});};return new F(function(){return _rz(_Go,_H3,_);});};return new F(function(){return _rz(_Gn,_H1,_);});};return new F(function(){return _rz(_Gm,_GZ,_);});};return new T3(0,_GW,function(_rg,_rh,_){return new F(function(){return _q9(_Gm,_Gq,_rg,_rh,_);});},_7);},_Hb=new T1(0,_),_Hc=new T1(0,_6),_Hd=new T2(0,E(_Hc),E(_Hb)),_He=function(_Hf,_Hg){return new F(function(){return A1(_Hg,new T2(0,_7,_Hf));});},_Hh=1,_Hi=function(_Hj){var _Hk=E(_Hj);if(!_Hk._){return E(_He);}else{var _Hl=new T(function(){var _Hm=E(_Hk.a);return B(_iB(_id,_Hm.a,_Hm.b,_Hm.c,_Hh,_tT));}),_Hn=new T(function(){return B(_Hi(_Hk.b));}),_Ho=function(_Hp){var _Hq=new T(function(){return B(A1(_Hl,_Hp));}),_Hr=function(_Hs){return new F(function(){return A1(_Hq,function(_Ht){return new F(function(){return A2(_Hn,E(_Ht).b,_Hs);});});});};return E(_Hr);};return E(_Ho);}},_Hu=function(_Hv){var _Hw=E(_Hv);if(!_Hw._){return E(_He);}else{var _Hx=new T(function(){var _Hy=E(_Hw.a),_Hz=function(_HA){var _HB=new T(function(){return B(A1(_Hy.b,_HA));}),_HC=function(_HD){return 1-B(A1(_HB,new T(function(){return 1-E(_HD);})));};return E(_HC);};return B(_iB(_id,_Hy.a,_Hz,_Hy.c,_FZ,_tT));}),_HE=new T(function(){return B(_Hu(_Hw.b));}),_HF=function(_HG){var _HH=new T(function(){return B(A1(_Hx,_HG));}),_HI=function(_HJ){return new F(function(){return A1(_HH,function(_HK){return new F(function(){return A2(_HE,E(_HK).b,_HJ);});});});};return E(_HI);};return E(_HF);}},_HL=function(_HM,_HN){if(_HM<=_HN){var _HO=function(_HP){return new T2(1,_HP,new T(function(){if(_HP!=_HN){return B(_HO(_HP+1|0));}else{return __Z;}}));};return new F(function(){return _HO(_HM);});}else{return __Z;}},_HQ=new T(function(){return B(_HL(0,2147483647));}),_HR=40,_HS=new T1(0,_HR),_HT=40,_HU=new T1(0,_G0),_HV=50,_HW=new T1(0,_HV),_HX=new T(function(){return B(_uj(_BU,_HW,_HU));}),_HY=function(_HZ){return new T2(2,_HZ,_2E);},_I0=function(_I1,_I2,_I3){var _I4=function(_I5,_I6){var _I7=E(_I5);if(!_I7._){return E(_Hd);}else{var _I8=E(_I6);if(!_I8._){return E(_Hd);}else{var _I9=_I8.a,_Ia=new T(function(){return 4-E(_I7.a);}),_Ib=new T(function(){var _Ic=new T(function(){var _Id=B(_Gl(_HX,new T(function(){return B(_uj(_BU,B(_uj(_vu,new T1(0,_Ia),_HS)),_HU));}),_HS,_HS));return new T3(0,_Id.a,_Id.b,_Id.c);});return B(_ro(_I1,_Ic));}),_Ie=B(_FC(new T2(0,new T(function(){return B(_HY(_I9));}),new T(function(){return B(_HY(_I9));})),_HX,new T(function(){return B(_uj(_BU,B(_uj(_vu,new T1(0,_Ia),_HS)),_HS));}),_Ib)),_If=new T(function(){return B(_I4(_I7.b,_I8.b));}),_Ig=function(_Ih){var _Ii=E(_If);return new T2(0,E(_Ii.a),E(new T2(2,_Ii.b,new T1(1,function(_Ij){return new T2(0,E(new T1(0,new T2(1,_Ih,_Ij))),E(_Hb));}))));};return new T2(0,E(_Ie.a),E(new T2(2,_Ie.b,new T1(1,_Ig))));}}},_Ik=function(_Il){var _Im=E(_Il),_In=_Im.a,_Io=new T(function(){return B(_Hu(_In));}),_Ip=new T(function(){return B(_Hi(_In));}),_Iq=function(_Ir){var _Is=new T(function(){return B(A1(_Ip,_Ir));}),_It=function(_Iu){var _Iv=function(_Iw){return new F(function(){return A2(_Iq,E(_Iw).b,_Iu);});},_Ix=function(_Iy){return new F(function(){return _BY(_HT,E(_Iy).b,_Iv);});},_Iz=function(_IA){return new F(function(){return A2(_Io,E(_IA).b,_Ix);});};return new F(function(){return A1(_Is,function(_IB){return new F(function(){return _BY(_HT,E(_IB).b,_Iz);});});});};return E(_It);},_IC=new T(function(){return B(_p8(_7,new T(function(){return B(_I4(_HQ,_In));})));});return new F(function(){return A1(_I3,new T2(0,new T2(0,_IC,_Iq),_Im.b));});};return new F(function(){return _G5(0,_I2,_Ik);});},_ID=function(_IE,_IF,_IG){return new T1(0,B(_I0(_IE,_IF,_IG)));},_IH=0.8,_II=new T1(0,_IH),_IJ=new T4(0,_Fw,_II,_sA,_u4),_IK=new T(function(){return B(unCStr("Grow"));}),_IL=new T(function(){return B(_AB(_IJ,_ID,_IK));}),_IM=new T4(0,_u4,_u2,_sA,_u4),_IN=new T(function(){return B(unCStr("Speed"));}),_IO=function(_IP,_IQ){return new F(function(){return A1(_IQ,new T2(0,_7,_IP));});},_IR=0,_IS=new T1(0,_IR),_IT=new T2(0,_IS,_IS),_IU=function(_IV){var _IW=hs_intToInt64(_IV);return E(_IW);},_IX=function(_IY){var _IZ=E(_IY);if(!_IZ._){return new F(function(){return _IU(_IZ.a);});}else{return new F(function(){return I_toInt64(_IZ.a);});}},_J0=function(_J1){return new F(function(){return _IX(_J1);});},_J2=function(_J3,_J4){return new F(function(){return hs_timesInt64(E(_J3),E(_J4));});},_J5=function(_J6,_J7){return new F(function(){return hs_plusInt64(E(_J6),E(_J7));});},_J8=function(_J9,_Ja){return new F(function(){return hs_minusInt64(E(_J9),E(_Ja));});},_Jb=function(_Jc){var _Jd=hs_geInt64(_Jc,new Long(0,0));if(!_Jd){var _Je=hs_negateInt64(_Jc);return E(_Je);}else{return E(_Jc);}},_Jf=function(_Jg){return new F(function(){return _Jb(E(_Jg));});},_Jh=function(_Ji){return new F(function(){return hs_negateInt64(E(_Ji));});},_Jj=function(_Jk){var _Jl=hs_gtInt64(_Jk,new Long(0,0));if(!_Jl){var _Jm=hs_eqInt64(_Jk,new Long(0,0));if(!_Jm){return new F(function(){return new Long(4294967295,-1);});}else{return new F(function(){return new Long(0,0);});}}else{return new F(function(){return new Long(1,0);});}},_Jn=function(_Jo){return new F(function(){return _Jj(E(_Jo));});},_Jp={_:0,a:_J5,b:_J8,c:_J2,d:_Jh,e:_Jf,f:_Jn,g:_J0},_Jq=new T1(0,0),_Jr=function(_Js,_Jt){while(1){var _Ju=E(_Js);if(!_Ju._){var _Jv=_Ju.a,_Jw=E(_Jt);if(!_Jw._){return new T1(0,(_Jv>>>0|_Jw.a>>>0)>>>0&4294967295);}else{_Js=new T1(1,I_fromInt(_Jv));_Jt=_Jw;continue;}}else{var _Jx=E(_Jt);if(!_Jx._){_Js=_Ju;_Jt=new T1(1,I_fromInt(_Jx.a));continue;}else{return new T1(1,I_or(_Ju.a,_Jx.a));}}}},_Jy=function(_Jz,_JA){while(1){var _JB=E(_Jz);if(!_JB._){_Jz=new T1(1,I_fromInt(_JB.a));continue;}else{return new T1(1,I_shiftLeft(_JB.a,_JA));}}},_JC=function(_JD){var _JE=E(_JD);if(!_JE._){return E(_Jq);}else{return new F(function(){return _Jr(new T1(0,E(_JE.a)),B(_Jy(B(_JC(_JE.b)),31)));});}},_JF=new T1(0,1),_JG=new T1(0,2147483647),_JH=function(_JI,_JJ){while(1){var _JK=E(_JI);if(!_JK._){var _JL=_JK.a,_JM=E(_JJ);if(!_JM._){var _JN=_JM.a,_JO=addC(_JL,_JN);if(!E(_JO.b)){return new T1(0,_JO.a);}else{_JI=new T1(1,I_fromInt(_JL));_JJ=new T1(1,I_fromInt(_JN));continue;}}else{_JI=new T1(1,I_fromInt(_JL));_JJ=_JM;continue;}}else{var _JP=E(_JJ);if(!_JP._){_JI=_JK;_JJ=new T1(1,I_fromInt(_JP.a));continue;}else{return new T1(1,I_add(_JK.a,_JP.a));}}}},_JQ=new T(function(){return B(_JH(_JG,_JF));}),_JR=function(_JS){var _JT=E(_JS);if(!_JT._){var _JU=E(_JT.a);return (_JU==(-2147483648))?E(_JQ):new T1(0, -_JU);}else{return new T1(1,I_negate(_JT.a));}},_JV=function(_JW,_JX){if(!E(_JW)){return new F(function(){return _JR(B(_JC(_JX)));});}else{return new F(function(){return _JC(_JX);});}},_JY=2147483647,_JZ=2147483647,_K0=1,_K1=new T2(1,_K0,_6),_K2=new T2(1,_JZ,_K1),_K3=new T2(1,_JY,_K2),_K4=new T(function(){return B(_JV(_aw,_K3));}),_K5=0,_K6=0,_K7=2,_K8=new T2(1,_K7,_6),_K9=new T2(1,_K6,_K8),_Ka=new T2(1,_K5,_K9),_Kb=new T(function(){return B(_JV(_av,_Ka));}),_Kc=new Long(2,0),_Kd=new T(function(){return B(unCStr("Negative exponent"));}),_Ke=new T(function(){return B(err(_Kd));}),_Kf=new Long(1,0),_Kg=new Long(4294967295,2147483647),_Kh=new Long(0,-2147483648),_Ki=new T2(0,_Kh,_Kg),_Kj=new T1(0,1),_Kk=function(_Kl){return E(E(_Kl).a);},_Km=function(_Kn){return E(E(_Kn).a);},_Ko=function(_Kp){return E(E(_Kp).g);},_Kq=function(_Kr,_Ks){var _Kt=E(_Kr);if(!_Kt._){var _Ku=_Kt.a,_Kv=E(_Ks);return (_Kv._==0)?_Ku>_Kv.a:I_compareInt(_Kv.a,_Ku)<0;}else{var _Kw=_Kt.a,_Kx=E(_Ks);return (_Kx._==0)?I_compareInt(_Kw,_Kx.a)>0:I_compare(_Kw,_Kx.a)>0;}},_Ky=function(_Kz){return E(E(_Kz).b);},_KA=function(_KB){return E(E(_KB).i);},_KC=function(_KD,_KE,_KF){var _KG=new T(function(){return B(_Ko(new T(function(){return B(_Km(new T(function(){return B(_Kk(_KD));})));})));}),_KH=new T(function(){return B(_Ky(_KE));}),_KI=function(_KJ){return (!B(_Kq(_KJ,B(A2(_KA,_KD,_KH)))))?new T2(1,new T(function(){return B(A1(_KG,_KJ));}),new T(function(){return B(_KI(B(_JH(_KJ,_Kj))));})):__Z;};return new F(function(){return _KI(B(A2(_KA,_KD,_KF)));});},_KK=function(_KL){return new F(function(){return _KC(_KM,_Ki,_KL);});},_KN=new T1(0,0),_KO=function(_KP,_KQ){var _KR=E(_KP);if(!_KR._){var _KS=_KR.a,_KT=E(_KQ);return (_KT._==0)?_KS>=_KT.a:I_compareInt(_KT.a,_KS)<=0;}else{var _KU=_KR.a,_KV=E(_KQ);return (_KV._==0)?I_compareInt(_KU,_KV.a)>=0:I_compare(_KU,_KV.a)>=0;}},_KW=function(_KX,_KY){var _KZ=E(_KX);if(!_KZ._){var _L0=_KZ.a,_L1=E(_KY);return (_L1._==0)?_L0<_L1.a:I_compareInt(_L1.a,_L0)>0;}else{var _L2=_KZ.a,_L3=E(_KY);return (_L3._==0)?I_compareInt(_L2,_L3.a)<0:I_compare(_L2,_L3.a)<0;}},_L4=function(_L5,_L6,_L7,_L8,_L9){var _La=function(_Lb){if(!B(_Kq(_Lb,_L9))){return new F(function(){return A2(_L5,_Lb,new T(function(){return B(_La(B(_JH(_Lb,_L8))));}));});}else{return E(_L6);}};return new F(function(){return _La(_L7);});},_Lc=function(_Ld,_Le,_Lf,_Lg,_Lh){if(!B(_KO(_Lg,_KN))){var _Li=function(_Lj){if(!B(_KW(_Lj,_Lh))){return new F(function(){return A2(_Ld,_Lj,new T(function(){return B(_Li(B(_JH(_Lj,_Lg))));}));});}else{return E(_Le);}};return new F(function(){return _Li(_Lf);});}else{return new F(function(){return _L4(_Ld,_Le,_Lf,_Lg,_Lh);});}},_Lk=function(_Ll){return E(E(_Ll).a);},_Lm=function(_Ln,_Lo){while(1){var _Lp=E(_Ln);if(!_Lp._){var _Lq=_Lp.a,_Lr=E(_Lo);if(!_Lr._){var _Ls=_Lr.a,_Lt=subC(_Lq,_Ls);if(!E(_Lt.b)){return new T1(0,_Lt.a);}else{_Ln=new T1(1,I_fromInt(_Lq));_Lo=new T1(1,I_fromInt(_Ls));continue;}}else{_Ln=new T1(1,I_fromInt(_Lq));_Lo=_Lr;continue;}}else{var _Lu=E(_Lo);if(!_Lu._){_Ln=_Lp;_Lo=new T1(1,I_fromInt(_Lu.a));continue;}else{return new T1(1,I_sub(_Lp.a,_Lu.a));}}}},_Lv=function(_Lw,_Lx,_Ly,_Lz){var _LA=B(A2(_KA,_Lw,_Lz)),_LB=B(A2(_KA,_Lw,_Ly));if(!B(_KO(_LA,_LB))){var _LC=new T(function(){return B(_Ko(new T(function(){return B(_Km(new T(function(){return B(_Kk(_Lw));})));})));}),_LD=function(_LE,_LF){return new T2(1,new T(function(){return B(A1(_LC,_LE));}),_LF);};return new F(function(){return _Lc(_LD,_6,_LB,B(_Lm(_LA,_LB)),B(A2(_KA,_Lw,new T(function(){return B(_Lk(_Lx));}))));});}else{var _LG=new T(function(){return B(_Ko(new T(function(){return B(_Km(new T(function(){return B(_Kk(_Lw));})));})));}),_LH=function(_LI,_LJ){return new T2(1,new T(function(){return B(A1(_LG,_LI));}),_LJ);};return new F(function(){return _Lc(_LH,_6,_LB,B(_Lm(_LA,_LB)),B(A2(_KA,_Lw,new T(function(){return B(_Ky(_Lx));}))));});}},_LK=function(_LL,_KL){return new F(function(){return _Lv(_KM,_Ki,_LL,_KL);});},_LM=function(_LN,_LO,_LP,_LQ){var _LR=B(A2(_KA,_LN,_LO)),_LS=new T(function(){return B(_Ko(new T(function(){return B(_Km(new T(function(){return B(_Kk(_LN));})));})));}),_LT=function(_LU,_LV){return new T2(1,new T(function(){return B(A1(_LS,_LU));}),_LV);};return new F(function(){return _Lc(_LT,_6,_LR,B(_Lm(B(A2(_KA,_LN,_LP)),_LR)),B(A2(_KA,_LN,_LQ)));});},_LW=function(_LX,_LL,_KL){return new F(function(){return _LM(_KM,_LX,_LL,_KL);});},_LY=function(_LZ,_M0,_M1){var _M2=new T(function(){return B(_Ko(new T(function(){return B(_Km(new T(function(){return B(_Kk(_LZ));})));})));}),_M3=function(_M4){return (!B(_Kq(_M4,B(A2(_KA,_LZ,_M1)))))?new T2(1,new T(function(){return B(A1(_M2,_M4));}),new T(function(){return B(_M3(B(_JH(_M4,_Kj))));})):__Z;};return new F(function(){return _M3(B(A2(_KA,_LZ,_M0)));});},_M5=function(_LL,_KL){return new F(function(){return _LY(_KM,_LL,_KL);});},_M6=new T(function(){return hs_intToInt64(2147483647);}),_M7=function(_M8){return new T1(0,_M8);},_M9=function(_Ma){var _Mb=hs_intToInt64(2147483647),_Mc=hs_leInt64(_Ma,_Mb);if(!_Mc){return new T1(1,I_fromInt64(_Ma));}else{var _Md=hs_intToInt64(-2147483648),_Me=hs_geInt64(_Ma,_Md);if(!_Me){return new T1(1,I_fromInt64(_Ma));}else{var _Mf=hs_int64ToInt(_Ma);return new F(function(){return _M7(_Mf);});}}},_Mg=function(_Mh){return new F(function(){return _M9(E(_Mh));});},_Mi=function(_Mj){while(1){var _Mk=E(_Mj);if(!_Mk._){_Mj=new T1(1,I_fromInt(_Mk.a));continue;}else{return new F(function(){return I_toString(_Mk.a);});}}},_Ml=function(_Mm,_Mn){return new F(function(){return _2(fromJSStr(B(_Mi(_Mm))),_Mn);});},_Mo=new T1(0,0),_Mp=function(_Mq,_Mr,_Ms){if(_Mq<=6){return new F(function(){return _Ml(_Mr,_Ms);});}else{if(!B(_KW(_Mr,_Mo))){return new F(function(){return _Ml(_Mr,_Ms);});}else{return new T2(1,_3c,new T(function(){return B(_2(fromJSStr(B(_Mi(_Mr))),new T2(1,_3b,_Ms)));}));}}},_Mt=function(_Mu){return new F(function(){return _Mp(0,B(_Mg(_Mu)),_6);});},_Mv=function(_Mw,_Mx){return new F(function(){return _Mp(0,B(_M9(E(_Mw))),_Mx);});},_My=function(_Mz,_MA){return new F(function(){return _26(_Mv,_Mz,_MA);});},_MB=function(_MC,_MD){var _ME=new T(function(){return B(_M9(E(_MD)));});return function(_MF){return new F(function(){return _Mp(E(_MC),_ME,_MF);});};},_MG=new T3(0,_MB,_Mt,_My),_MH=new T2(1,_3b,_6),_MI=function(_MJ,_MK,_ML){return new F(function(){return A1(_MJ,new T2(1,_23,new T(function(){return B(A1(_MK,_ML));})));});},_MM=new T(function(){return B(unCStr(": empty list"));}),_MN=new T(function(){return B(unCStr("Prelude."));}),_MO=function(_MP){return new F(function(){return err(B(_2(_MN,new T(function(){return B(_2(_MP,_MM));},1))));});},_MQ=new T(function(){return B(unCStr("foldr1"));}),_MR=new T(function(){return B(_MO(_MQ));}),_MS=function(_MT,_MU){var _MV=E(_MU);if(!_MV._){return E(_MR);}else{var _MW=_MV.a,_MX=E(_MV.b);if(!_MX._){return E(_MW);}else{return new F(function(){return A2(_MT,_MW,new T(function(){return B(_MS(_MT,_MX));}));});}}},_MY=function(_MZ){return new F(function(){return _3d(0,-2147483648,_MZ);});},_N0=function(_N1){return new F(function(){return _3d(0,2147483647,_N1);});},_N2=new T2(1,_N0,_6),_N3=new T2(1,_MY,_N2),_N4=new T(function(){return B(_MS(_MI,_N3));}),_N5=new T(function(){return B(A1(_N4,_MH));}),_N6=new T2(1,_3c,_N5),_N7=new T(function(){return B(unAppCStr(") is outside of Int\'s bounds ",_N6));}),_N8=function(_N9){return E(E(_N9).b);},_Na=function(_Nb,_Nc,_Nd){var _Ne=new T(function(){var _Nf=new T(function(){return B(unAppCStr("}: value (",new T(function(){return B(_2(B(A2(_N8,_Nd,_Nc)),_N7));})));},1);return B(_2(_Nb,_Nf));});return new F(function(){return err(B(unAppCStr("Enum.fromEnum{",_Ne)));});},_Ng=function(_Nh,_Ni,_Nj){return new F(function(){return _Na(_Ni,_Nj,_Nh);});},_Nk=new T(function(){return B(unCStr("Int64"));}),_Nl=function(_Nm){return new F(function(){return _Ng(_MG,_Nk,_Nm);});},_Nn=function(_No){return new F(function(){return _Nl(_No);});},_Np=new T(function(){return hs_intToInt64(-2147483648);}),_Nq=function(_Nr){var _Ns=hs_geInt64(_Nr,E(_Np));if(!_Ns){return new F(function(){return _Nn(_Nr);});}else{var _Nt=hs_leInt64(_Nr,E(_M6));if(!_Nt){return new F(function(){return _Nn(_Nr);});}else{var _Nu=hs_int64ToInt(_Nr);return E(_Nu);}}},_Nv=function(_Nw){return new F(function(){return _Nq(E(_Nw));});},_Nx=new T(function(){return B(unCStr("}: tried to take `pred\' of minBound"));}),_Ny=function(_Nz){return new F(function(){return err(B(unAppCStr("Enum.pred{",new T(function(){return B(_2(_Nz,_Nx));}))));});},_NA=function(_NB){return new F(function(){return _Ny(_NB);});},_NC=new T(function(){return B(_NA(_Nk));}),_ND=function(_NE){var _NF=hs_neInt64(_NE,new Long(0,-2147483648));if(!_NF){return E(_NC);}else{var _NG=hs_minusInt64(_NE,new Long(1,0));return E(_NG);}},_NH=function(_NI){return new F(function(){return _ND(E(_NI));});},_NJ=new T(function(){return B(unCStr("}: tried to take `succ\' of maxBound"));}),_NK=function(_NL){return new F(function(){return err(B(unAppCStr("Enum.succ{",new T(function(){return B(_2(_NL,_NJ));}))));});},_NM=function(_NB){return new F(function(){return _NK(_NB);});},_NN=new T(function(){return B(_NM(_Nk));}),_NO=function(_NP){var _NQ=hs_neInt64(_NP,new Long(4294967295,2147483647));if(!_NQ){return E(_NN);}else{var _NR=hs_plusInt64(_NP,new Long(1,0));return E(_NR);}},_NS=function(_NT){return new F(function(){return _NO(E(_NT));});},_NU=function(_NV){return new F(function(){return hs_intToInt64(E(_NV));});},_NW=new T(function(){return {_:0,a:_NS,b:_NH,c:_NU,d:_Nv,e:_KK,f:_LK,g:_M5,h:_LW};}),_NX=function(_NY,_NZ){var _O0=hs_minusInt64(_NY,_NZ);return E(_O0);},_O1=function(_O2,_O3){var _O4=hs_quotInt64(_O2,_O3);return E(_O4);},_O5=function(_O6,_O7){var _O8=hs_intToInt64(1),_O9=_O8,_Oa=hs_intToInt64(0),_Ob=_Oa,_Oc=hs_gtInt64(_O6,_Ob),_Od=function(_Oe){var _Of=hs_ltInt64(_O6,_Ob);if(!_Of){return new F(function(){return _O1(_O6,_O7);});}else{var _Og=hs_gtInt64(_O7,_Ob);if(!_Og){return new F(function(){return _O1(_O6,_O7);});}else{var _Oh=hs_plusInt64(_O6,_O9),_Oi=hs_quotInt64(_Oh,_O7);return new F(function(){return _NX(_Oi,_O9);});}}};if(!_Oc){return new F(function(){return _Od(_);});}else{var _Oj=hs_ltInt64(_O7,_Ob);if(!_Oj){return new F(function(){return _Od(_);});}else{var _Ok=hs_minusInt64(_O6,_O9),_Ol=hs_quotInt64(_Ok,_O7);return new F(function(){return _NX(_Ol,_O9);});}}},_Om=new T(function(){return B(unCStr("base"));}),_On=new T(function(){return B(unCStr("GHC.Exception"));}),_Oo=new T(function(){return B(unCStr("ArithException"));}),_Op=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_Om,_On,_Oo),_Oq=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_Op,_6,_6),_Or=function(_Os){return E(_Oq);},_Ot=function(_Ou){var _Ov=E(_Ou);return new F(function(){return _S(B(_Q(_Ov.a)),_Or,_Ov.b);});},_Ow=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_Ox=new T(function(){return B(unCStr("denormal"));}),_Oy=new T(function(){return B(unCStr("divide by zero"));}),_Oz=new T(function(){return B(unCStr("loss of precision"));}),_OA=new T(function(){return B(unCStr("arithmetic underflow"));}),_OB=new T(function(){return B(unCStr("arithmetic overflow"));}),_OC=function(_OD,_OE){switch(E(_OD)){case 0:return new F(function(){return _2(_OB,_OE);});break;case 1:return new F(function(){return _2(_OA,_OE);});break;case 2:return new F(function(){return _2(_Oz,_OE);});break;case 3:return new F(function(){return _2(_Oy,_OE);});break;case 4:return new F(function(){return _2(_Ox,_OE);});break;default:return new F(function(){return _2(_Ow,_OE);});}},_OF=function(_OG){return new F(function(){return _OC(_OG,_6);});},_OH=function(_OI,_OJ,_OK){return new F(function(){return _OC(_OJ,_OK);});},_OL=function(_OM,_ON){return new F(function(){return _26(_OC,_OM,_ON);});},_OO=new T3(0,_OH,_OF,_OL),_OP=new T(function(){return new T5(0,_Or,_OO,_OQ,_Ot,_OF);}),_OQ=function(_OR){return new T2(0,_OP,_OR);},_OS=3,_OT=new T(function(){return B(_OQ(_OS));}),_OU=new T(function(){return die(_OT);}),_OV=0,_OW=new T(function(){return B(_OQ(_OV));}),_OX=new T(function(){return die(_OW);}),_OY=function(_OZ,_P0){var _P1=hs_eqInt64(_P0,new Long(0,0));if(!_P1){var _P2=hs_eqInt64(_P0,new Long(4294967295,-1));if(!_P2){return new F(function(){return _O5(_OZ,_P0);});}else{var _P3=hs_eqInt64(_OZ,new Long(0,-2147483648));if(!_P3){return new F(function(){return _O5(_OZ,_P0);});}else{return E(_OX);}}}else{return E(_OU);}},_P4=function(_P5,_P6){return new F(function(){return _OY(E(_P5),E(_P6));});},_P7=new Long(0,0),_P8=function(_P9,_Pa){var _Pb=hs_plusInt64(_P9,_Pa);return E(_Pb);},_Pc=function(_Pd,_Pe){var _Pf=hs_remInt64(_Pd,_Pe),_Pg=_Pf,_Ph=hs_intToInt64(0),_Pi=_Ph,_Pj=hs_gtInt64(_Pd,_Pi),_Pk=function(_Pl){var _Pm=hs_neInt64(_Pg,_Pi);if(!_Pm){return E(_Pi);}else{return new F(function(){return _P8(_Pg,_Pe);});}},_Pn=function(_Po){var _Pp=hs_ltInt64(_Pd,_Pi);if(!_Pp){return E(_Pg);}else{var _Pq=hs_gtInt64(_Pe,_Pi);if(!_Pq){return E(_Pg);}else{return new F(function(){return _Pk(_);});}}};if(!_Pj){return new F(function(){return _Pn(_);});}else{var _Pr=hs_ltInt64(_Pe,_Pi);if(!_Pr){return new F(function(){return _Pn(_);});}else{return new F(function(){return _Pk(_);});}}},_Ps=function(_Pt,_Pu){var _Pv=hs_eqInt64(_Pu,new Long(0,0));if(!_Pv){var _Pw=hs_eqInt64(_Pu,new Long(4294967295,-1));if(!_Pw){return new T2(0,new T(function(){return B(_O5(_Pt,_Pu));}),new T(function(){return B(_Pc(_Pt,_Pu));}));}else{var _Px=hs_eqInt64(_Pt,new Long(0,-2147483648));return (!_Px)?new T2(0,new T(function(){return B(_O5(_Pt,_Pu));}),new T(function(){return B(_Pc(_Pt,_Pu));})):new T2(0,_OX,_P7);}}else{return E(_OU);}},_Py=function(_Pz,_PA){var _PB=B(_Ps(E(_Pz),E(_PA)));return new T2(0,_PB.a,_PB.b);},_PC=function(_PD,_PE){var _PF=hs_eqInt64(_PE,new Long(0,0));if(!_PF){var _PG=hs_eqInt64(_PE,new Long(4294967295,-1));if(!_PG){return new F(function(){return _Pc(_PD,_PE);});}else{return new F(function(){return new Long(0,0);});}}else{return E(_OU);}},_PH=function(_PI,_PJ){return new F(function(){return _PC(E(_PI),E(_PJ));});},_PK=function(_PL,_PM){var _PN=hs_eqInt64(_PM,new Long(0,0));if(!_PN){var _PO=hs_eqInt64(_PM,new Long(4294967295,-1));if(!_PO){var _PP=hs_quotInt64(_PL,_PM);return E(_PP);}else{var _PQ=hs_eqInt64(_PL,new Long(0,-2147483648));if(!_PQ){var _PR=hs_quotInt64(_PL,_PM);return E(_PR);}else{return E(_OX);}}}else{return E(_OU);}},_PS=function(_PT,_PU){return new F(function(){return _PK(E(_PT),E(_PU));});},_PV=function(_PW,_PX){var _PY=hs_eqInt64(_PX,new Long(0,0));if(!_PY){var _PZ=hs_eqInt64(_PX,new Long(4294967295,-1));if(!_PZ){return new T2(0,new T(function(){return hs_quotInt64(_PW,_PX);}),new T(function(){return hs_remInt64(_PW,_PX);}));}else{var _Q0=hs_eqInt64(_PW,new Long(0,-2147483648));return (!_Q0)?new T2(0,new T(function(){return hs_quotInt64(_PW,_PX);}),new T(function(){return hs_remInt64(_PW,_PX);})):new T2(0,_OX,_P7);}}else{return E(_OU);}},_Q1=function(_Q2,_Q3){var _Q4=B(_PV(E(_Q2),E(_Q3)));return new T2(0,_Q4.a,_Q4.b);},_Q5=function(_Q6,_Q7){var _Q8=hs_eqInt64(_Q7,new Long(0,0));if(!_Q8){var _Q9=hs_eqInt64(_Q7,new Long(4294967295,-1));if(!_Q9){var _Qa=hs_remInt64(_Q6,_Q7);return E(_Qa);}else{return new F(function(){return new Long(0,0);});}}else{return E(_OU);}},_Qb=function(_Qc,_Qd){return new F(function(){return _Q5(E(_Qc),E(_Qd));});},_Qe=function(_Qf,_Qg){return new F(function(){return hs_neInt64(E(_Qf),E(_Qg));});},_Qh=function(_Qi,_Qj){return new F(function(){return hs_eqInt64(E(_Qi),E(_Qj));});},_Qk=new T2(0,_Qh,_Qe),_Ql=function(_Qm,_Qn){return new F(function(){return hs_ltInt64(E(_Qm),E(_Qn));});},_Qo=function(_Qp,_Qq){return new F(function(){return hs_leInt64(E(_Qp),E(_Qq));});},_Qr=function(_Qs,_Qt){return new F(function(){return hs_gtInt64(E(_Qs),E(_Qt));});},_Qu=function(_Qv,_Qw){return new F(function(){return hs_geInt64(E(_Qv),E(_Qw));});},_Qx=function(_Qy,_Qz){var _QA=hs_eqInt64(_Qy,_Qz);if(!_QA){var _QB=hs_leInt64(_Qy,_Qz);return (!_QB)?2:0;}else{return 1;}},_QC=function(_QD,_QE){return new F(function(){return _Qx(E(_QD),E(_QE));});},_QF=function(_QG,_QH){var _QI=E(_QG),_QJ=E(_QH),_QK=hs_leInt64(_QI,_QJ);return (!_QK)?E(_QI):E(_QJ);},_QL=function(_QM,_QN){var _QO=E(_QM),_QP=E(_QN),_QQ=hs_leInt64(_QO,_QP);return (!_QQ)?E(_QP):E(_QO);},_QR={_:0,a:_Qk,b:_QC,c:_Ql,d:_Qo,e:_Qr,f:_Qu,g:_QF,h:_QL},_QS=new T1(0,1),_QT=function(_QU,_QV){var _QW=E(_QU);if(!_QW._){var _QX=_QW.a,_QY=E(_QV);return (_QY._==0)?_QX==_QY.a:(I_compareInt(_QY.a,_QX)==0)?true:false;}else{var _QZ=_QW.a,_R0=E(_QV);return (_R0._==0)?(I_compareInt(_QZ,_R0.a)==0)?true:false:(I_compare(_QZ,_R0.a)==0)?true:false;}},_R1=new T1(0,0),_R2=function(_R3,_R4){while(1){var _R5=E(_R3);if(!_R5._){var _R6=E(_R5.a);if(_R6==(-2147483648)){_R3=new T1(1,I_fromInt(-2147483648));continue;}else{var _R7=E(_R4);if(!_R7._){return new T1(0,_R6%_R7.a);}else{_R3=new T1(1,I_fromInt(_R6));_R4=_R7;continue;}}}else{var _R8=_R5.a,_R9=E(_R4);return (_R9._==0)?new T1(1,I_rem(_R8,I_fromInt(_R9.a))):new T1(1,I_rem(_R8,_R9.a));}}},_Ra=function(_Rb,_Rc){if(!B(_QT(_Rc,_R1))){return new F(function(){return _R2(_Rb,_Rc);});}else{return E(_OU);}},_Rd=function(_Re,_Rf){while(1){if(!B(_QT(_Rf,_R1))){var _Rg=_Rf,_Rh=B(_Ra(_Re,_Rf));_Re=_Rg;_Rf=_Rh;continue;}else{return E(_Re);}}},_Ri=function(_Rj){var _Rk=E(_Rj);if(!_Rk._){var _Rl=E(_Rk.a);return (_Rl==(-2147483648))?E(_JQ):(_Rl<0)?new T1(0, -_Rl):E(_Rk);}else{var _Rm=_Rk.a;return (I_compareInt(_Rm,0)>=0)?E(_Rk):new T1(1,I_negate(_Rm));}},_Rn=function(_Ro,_Rp){while(1){var _Rq=E(_Ro);if(!_Rq._){var _Rr=E(_Rq.a);if(_Rr==(-2147483648)){_Ro=new T1(1,I_fromInt(-2147483648));continue;}else{var _Rs=E(_Rp);if(!_Rs._){return new T1(0,quot(_Rr,_Rs.a));}else{_Ro=new T1(1,I_fromInt(_Rr));_Rp=_Rs;continue;}}}else{var _Rt=_Rq.a,_Ru=E(_Rp);return (_Ru._==0)?new T1(0,I_toInt(I_quot(_Rt,I_fromInt(_Ru.a)))):new T1(1,I_quot(_Rt,_Ru.a));}}},_Rv=5,_Rw=new T(function(){return B(_OQ(_Rv));}),_Rx=new T(function(){return die(_Rw);}),_Ry=function(_Rz,_RA){if(!B(_QT(_RA,_R1))){var _RB=B(_Rd(B(_Ri(_Rz)),B(_Ri(_RA))));return (!B(_QT(_RB,_R1)))?new T2(0,B(_Rn(_Rz,_RB)),B(_Rn(_RA,_RB))):E(_OU);}else{return E(_Rx);}},_RC=function(_RD,_RE){while(1){var _RF=E(_RD);if(!_RF._){var _RG=_RF.a,_RH=E(_RE);if(!_RH._){var _RI=_RH.a;if(!(imul(_RG,_RI)|0)){return new T1(0,imul(_RG,_RI)|0);}else{_RD=new T1(1,I_fromInt(_RG));_RE=new T1(1,I_fromInt(_RI));continue;}}else{_RD=new T1(1,I_fromInt(_RG));_RE=_RH;continue;}}else{var _RJ=E(_RE);if(!_RJ._){_RD=_RF;_RE=new T1(1,I_fromInt(_RJ.a));continue;}else{return new T1(1,I_mul(_RF.a,_RJ.a));}}}},_RK=function(_RL){var _RM=B(_Ry(B(_RC(B(_M9(E(_RL))),_QS)),_QS));return new T2(0,E(_RM.a),E(_RM.b));},_RN=new T3(0,_Jp,_QR,_RK),_KM=new T(function(){return {_:0,a:_RN,b:_NW,c:_PS,d:_Qb,e:_P4,f:_PH,g:_Q1,h:_Py,i:_Mg};}),_RO=function(_RP){return E(E(_RP).a);},_RQ=function(_RR){return E(E(_RR).b);},_RS=function(_RT){return E(E(_RT).a);},_RU=new T1(0,2),_RV=function(_RW){return E(E(_RW).d);},_RX=function(_RY,_RZ){var _S0=B(_Kk(_RY)),_S1=new T(function(){return B(_Km(_S0));}),_S2=new T(function(){return B(A3(_RV,_RY,_RZ,new T(function(){return B(A2(_Ko,_S1,_RU));})));});return new F(function(){return A3(_RS,B(_RO(B(_RQ(_S0)))),_S2,new T(function(){return B(A2(_Ko,_S1,_R1));}));});},_S3=function(_S4,_S5,_S6){while(1){var _S7=B((function(_S8,_S9,_Sa){if(!B(_RX(_KM,_S9))){var _Sb=hs_eqInt64(_S9,new Long(1,0));if(!_Sb){var _Sc=hs_minusInt64(_S9,new Long(1,0));_S4=new T(function(){return B(_J2(_S8,_S8));});_S5=B(_PK(_Sc,new Long(2,0)));_S6=new T(function(){return B(_J2(_S8,_Sa));},1);return __continue;}else{var _Sd=hs_timesInt64(E(_S8),E(_Sa));return E(_Sd);}}else{var _Se=B(_PK(_S9,new Long(2,0))),_Sf=_Sa;_S4=new T(function(){return B(_J2(_S8,_S8));});_S5=_Se;_S6=_Sf;return __continue;}})(_S4,_S5,_S6));if(_S7!=__continue){return _S7;}}},_Sg=function(_Sh,_Si){while(1){var _Sj=B((function(_Sk,_Sl){if(!B(_RX(_KM,_Sl))){var _Sm=hs_eqInt64(_Sl,new Long(1,0));if(!_Sm){var _Sn=hs_minusInt64(_Sl,new Long(1,0));return new F(function(){return _S3(new T(function(){return B(_J2(_Sk,_Sk));}),B(_PK(_Sn,new Long(2,0))),_Sk);});}else{return E(_Sk);}}else{var _So=B(_PK(_Sl,new Long(2,0)));_Sh=new T(function(){return B(_J2(_Sk,_Sk));});_Si=_So;return __continue;}})(_Sh,_Si));if(_Sj!=__continue){return _Sj;}}},_Sp=function(_Sq,_Sr){var _Ss=hs_ltInt64(_Sr,new Long(0,0));if(!_Ss){var _St=hs_eqInt64(_Sr,new Long(0,0));if(!_St){return new F(function(){return _Sg(_Sq,_Sr);});}else{return E(_Kf);}}else{return E(_Ke);}},_Su=new T(function(){return B(_Sp(_Kc,new Long(53,0)));}),_Sv=function(_Sw){var _Sx=E(_Sw);if(!_Sx._){return _Sx.a;}else{return new F(function(){return I_toNumber(_Sx.a);});}},_Sy=new T(function(){return B(_Sv(B(_M9(E(_Su)))));}),_Sz=new T(function(){return hs_minusInt64(E(_Su),new Long(1,0));}),_SA=function(_SB,_SC){var _SD=hs_int64ToWord64(_SC),_SE=hs_int64ToWord64(_SB),_SF=hs_and64(_SE,_SD),_SG=hs_word64ToInt64(_SF);return E(_SG);},_SH=new T1(0,1),_SI=function(_SJ,_SK){return new T2(0,E(_SJ),E(_SK));},_SL=function(_SM,_SN){var _SO=quot(_SN,52774),_SP=(imul(40692,_SN-(imul(_SO,52774)|0)|0)|0)-(imul(_SO,3791)|0)|0,_SQ=new T(function(){if(_SP>=0){return _SP;}else{return _SP+2147483399|0;}}),_SR=quot(_SM,53668),_SS=(imul(40014,_SM-(imul(_SR,53668)|0)|0)|0)-(imul(_SR,12211)|0)|0,_ST=new T(function(){if(_SS>=0){return _SS;}else{return _SS+2147483563|0;}});return new T2(0,new T(function(){var _SU=E(_ST)-E(_SQ)|0;if(_SU>=1){return _SU;}else{return _SU+2147483562|0;}}),new T(function(){return B(_SI(_ST,_SQ));}));},_SV=new T1(0,2147483562),_SW=new T1(0,0),_SX=new T1(0,1000),_SY=function(_SZ,_T0){var _T1=_SZ%_T0;if(_SZ<=0){if(_SZ>=0){return E(_T1);}else{if(_T0<=0){return E(_T1);}else{var _T2=E(_T1);return (_T2==0)?0:_T2+_T0|0;}}}else{if(_T0>=0){if(_SZ>=0){return E(_T1);}else{if(_T0<=0){return E(_T1);}else{var _T3=E(_T1);return (_T3==0)?0:_T3+_T0|0;}}}else{var _T4=E(_T1);return (_T4==0)?0:_T4+_T0|0;}}},_T5=function(_T6,_T7){while(1){var _T8=E(_T6);if(!_T8._){var _T9=E(_T8.a);if(_T9==(-2147483648)){_T6=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ta=E(_T7);if(!_Ta._){return new T1(0,B(_SY(_T9,_Ta.a)));}else{_T6=new T1(1,I_fromInt(_T9));_T7=_Ta;continue;}}}else{var _Tb=_T8.a,_Tc=E(_T7);return (_Tc._==0)?new T1(1,I_mod(_Tb,I_fromInt(_Tc.a))):new T1(1,I_mod(_Tb,_Tc.a));}}},_Td=function(_Te,_Tf,_Tg,_Th){while(1){var _Ti=B((function(_Tj,_Tk,_Tl,_Tm){if(!B(_Kq(_Tk,_Tl))){var _Tn=B(_JH(B(_Lm(_Tl,_Tk)),_SH)),_To=function(_Tp,_Tq,_Tr){while(1){if(!B(_KO(_Tp,B(_RC(_Tn,_SX))))){var _Ts=E(_Tr),_Tt=B(_SL(_Ts.a,_Ts.b)),_Tu=B(_RC(_Tp,_SV)),_Tv=B(_JH(B(_RC(_Tq,_SV)),B(_Lm(B(_M7(E(_Tt.a))),_SH))));_Tp=_Tu;_Tq=_Tv;_Tr=_Tt.b;continue;}else{return new T2(0,_Tq,_Tr);}}},_Tw=B(_To(_SH,_SW,_Tm)),_Tx=new T(function(){return B(A2(_Ko,_Tj,new T(function(){if(!B(_QT(_Tn,_SW))){return B(_JH(_Tk,B(_T5(_Tw.a,_Tn))));}else{return E(_OU);}})));});return new T2(0,_Tx,_Tw.b);}else{var _Ty=_Tj,_Tz=_Tl,_TA=_Tk,_TB=_Tm;_Te=_Ty;_Tf=_Tz;_Tg=_TA;_Th=_TB;return __continue;}})(_Te,_Tf,_Tg,_Th));if(_Ti!=__continue){return _Ti;}}},_TC=function(_TD){var _TE=B(_Td(_Jp,_Kb,_K4,_TD));return new T2(0,new T(function(){return B(_Sv(B(_M9(B(_SA(E(_Sz),E(_TE.a)))))))/E(_Sy);}),_TE.b);},_TF=function(_TG,_TH,_TI){while(1){var _TJ=B((function(_TK,_TL,_TM){if(_TK<=_TL){var _TN=new T(function(){var _TO=B(_TC(_TM));return new T2(0,_TO.a,_TO.b);});return new T2(0,new T(function(){var _TP=E(E(_TN).a);return 0.5*_TK+_TP*(0.5*_TL-0.5*_TK)+0.5*_TK+_TP*(0.5*_TL-0.5*_TK);}),new T(function(){return E(E(_TN).b);}));}else{var _TQ=_TL,_TR=_TK,_TS=_TM;_TG=_TQ;_TH=_TR;_TI=_TS;return __continue;}})(_TG,_TH,_TI));if(_TJ!=__continue){return _TJ;}}},_TT=1420103680,_TU=465,_TV=new T2(1,_TU,_6),_TW=new T2(1,_TT,_TV),_TX=new T(function(){return B(_JV(_aw,_TW));}),_TY=0,_TZ=function(_U0,_U1){var _U2=E(_U1);if(!_U2){return E(_OU);}else{var _U3=function(_U4){if(_U0<=0){if(_U0>=0){var _U5=quotRemI(_U0,_U2);return new T2(0,_U5.a,_U5.b);}else{if(_U2<=0){var _U6=quotRemI(_U0,_U2);return new T2(0,_U6.a,_U6.b);}else{var _U7=quotRemI(_U0+1|0,_U2);return new T2(0,_U7.a-1|0,(_U7.b+_U2|0)-1|0);}}}else{if(_U2>=0){if(_U0>=0){var _U8=quotRemI(_U0,_U2);return new T2(0,_U8.a,_U8.b);}else{if(_U2<=0){var _U9=quotRemI(_U0,_U2);return new T2(0,_U9.a,_U9.b);}else{var _Ua=quotRemI(_U0+1|0,_U2);return new T2(0,_Ua.a-1|0,(_Ua.b+_U2|0)-1|0);}}}else{var _Ub=quotRemI(_U0-1|0,_U2);return new T2(0,_Ub.a-1|0,(_Ub.b+_U2|0)+1|0);}}};if(E(_U2)==(-1)){if(E(_U0)==(-2147483648)){return new T2(0,_OX,_TY);}else{return new F(function(){return _U3(_);});}}else{return new F(function(){return _U3(_);});}}},_Uc=new T1(0,-1),_Ud=function(_Ue){var _Uf=E(_Ue);if(!_Uf._){var _Ug=_Uf.a;return (_Ug>=0)?(E(_Ug)==0)?E(_Jq):E(_JF):E(_Uc);}else{var _Uh=I_compareInt(_Uf.a,0);return (_Uh<=0)?(E(_Uh)==0)?E(_Jq):E(_Uc):E(_JF);}},_Ui=function(_Uj,_Uk,_Ul,_Um){var _Un=B(_RC(_Uk,_Ul));return new F(function(){return _Ry(B(_RC(B(_RC(_Uj,_Um)),B(_Ud(_Un)))),B(_Ri(_Un)));});},_Uo=function(_Up){return E(_TX);},_Uq=new T1(0,1),_Ur=function(_Us,_Ut){var _Uu=E(_Us);return new T2(0,_Uu,new T(function(){var _Uv=B(_Ur(B(_JH(_Uu,_Ut)),_Ut));return new T2(1,_Uv.a,_Uv.b);}));},_Uw=function(_Ux){var _Uy=B(_Ur(_Ux,_Uq));return new T2(1,_Uy.a,_Uy.b);},_Uz=function(_UA,_UB){var _UC=B(_Ur(_UA,new T(function(){return B(_Lm(_UB,_UA));})));return new T2(1,_UC.a,_UC.b);},_UD=function(_UE,_UF,_UG){if(!B(_KO(_UF,_KN))){var _UH=function(_UI){return (!B(_KW(_UI,_UG)))?new T2(1,_UI,new T(function(){return B(_UH(B(_JH(_UI,_UF))));})):__Z;};return new F(function(){return _UH(_UE);});}else{var _UJ=function(_UK){return (!B(_Kq(_UK,_UG)))?new T2(1,_UK,new T(function(){return B(_UJ(B(_JH(_UK,_UF))));})):__Z;};return new F(function(){return _UJ(_UE);});}},_UL=function(_UM,_UN,_UO){return new F(function(){return _UD(_UM,B(_Lm(_UN,_UM)),_UO);});},_UP=function(_UQ,_UR){return new F(function(){return _UD(_UQ,_Uq,_UR);});},_US=function(_UT){var _UU=E(_UT);if(!_UU._){return E(_UU.a);}else{return new F(function(){return I_toInt(_UU.a);});}},_UV=function(_UW){return new F(function(){return _US(_UW);});},_UX=function(_UY){return new F(function(){return _Lm(_UY,_Uq);});},_UZ=function(_V0){return new F(function(){return _JH(_V0,_Uq);});},_V1=function(_V2){return new F(function(){return _M7(E(_V2));});},_V3={_:0,a:_UZ,b:_UX,c:_V1,d:_UV,e:_Uw,f:_Uz,g:_UP,h:_UL},_V4=function(_V5,_V6){if(_V5<=0){if(_V5>=0){return new F(function(){return quot(_V5,_V6);});}else{if(_V6<=0){return new F(function(){return quot(_V5,_V6);});}else{return quot(_V5+1|0,_V6)-1|0;}}}else{if(_V6>=0){if(_V5>=0){return new F(function(){return quot(_V5,_V6);});}else{if(_V6<=0){return new F(function(){return quot(_V5,_V6);});}else{return quot(_V5+1|0,_V6)-1|0;}}}else{return quot(_V5-1|0,_V6)-1|0;}}},_V7=function(_V8,_V9){while(1){var _Va=E(_V8);if(!_Va._){var _Vb=E(_Va.a);if(_Vb==(-2147483648)){_V8=new T1(1,I_fromInt(-2147483648));continue;}else{var _Vc=E(_V9);if(!_Vc._){return new T1(0,B(_V4(_Vb,_Vc.a)));}else{_V8=new T1(1,I_fromInt(_Vb));_V9=_Vc;continue;}}}else{var _Vd=_Va.a,_Ve=E(_V9);return (_Ve._==0)?new T1(1,I_div(_Vd,I_fromInt(_Ve.a))):new T1(1,I_div(_Vd,_Ve.a));}}},_Vf=function(_Vg,_Vh){if(!B(_QT(_Vh,_R1))){return new F(function(){return _V7(_Vg,_Vh);});}else{return E(_OU);}},_Vi=function(_Vj,_Vk){while(1){var _Vl=E(_Vj);if(!_Vl._){var _Vm=E(_Vl.a);if(_Vm==(-2147483648)){_Vj=new T1(1,I_fromInt(-2147483648));continue;}else{var _Vn=E(_Vk);if(!_Vn._){var _Vo=_Vn.a;return new T2(0,new T1(0,B(_V4(_Vm,_Vo))),new T1(0,B(_SY(_Vm,_Vo))));}else{_Vj=new T1(1,I_fromInt(_Vm));_Vk=_Vn;continue;}}}else{var _Vp=E(_Vk);if(!_Vp._){_Vj=_Vl;_Vk=new T1(1,I_fromInt(_Vp.a));continue;}else{var _Vq=I_divMod(_Vl.a,_Vp.a);return new T2(0,new T1(1,_Vq.a),new T1(1,_Vq.b));}}}},_Vr=function(_Vs,_Vt){if(!B(_QT(_Vt,_R1))){var _Vu=B(_Vi(_Vs,_Vt));return new T2(0,_Vu.a,_Vu.b);}else{return E(_OU);}},_Vv=function(_Vw,_Vx){if(!B(_QT(_Vx,_R1))){return new F(function(){return _T5(_Vw,_Vx);});}else{return E(_OU);}},_Vy=function(_Vz,_VA){if(!B(_QT(_VA,_R1))){return new F(function(){return _Rn(_Vz,_VA);});}else{return E(_OU);}},_VB=function(_VC,_VD){while(1){var _VE=E(_VC);if(!_VE._){var _VF=E(_VE.a);if(_VF==(-2147483648)){_VC=new T1(1,I_fromInt(-2147483648));continue;}else{var _VG=E(_VD);if(!_VG._){var _VH=_VG.a;return new T2(0,new T1(0,quot(_VF,_VH)),new T1(0,_VF%_VH));}else{_VC=new T1(1,I_fromInt(_VF));_VD=_VG;continue;}}}else{var _VI=E(_VD);if(!_VI._){_VC=_VE;_VD=new T1(1,I_fromInt(_VI.a));continue;}else{var _VJ=I_quotRem(_VE.a,_VI.a);return new T2(0,new T1(1,_VJ.a),new T1(1,_VJ.b));}}}},_VK=function(_VL,_VM){if(!B(_QT(_VM,_R1))){var _VN=B(_VB(_VL,_VM));return new T2(0,_VN.a,_VN.b);}else{return E(_OU);}},_VO=function(_VP){return E(_VP);},_VQ=function(_VR){return E(_VR);},_VS={_:0,a:_JH,b:_Lm,c:_RC,d:_JR,e:_Ri,f:_Ud,g:_VQ},_VT=function(_VU,_VV){var _VW=E(_VU);if(!_VW._){var _VX=_VW.a,_VY=E(_VV);return (_VY._==0)?_VX!=_VY.a:(I_compareInt(_VY.a,_VX)==0)?false:true;}else{var _VZ=_VW.a,_W0=E(_VV);return (_W0._==0)?(I_compareInt(_VZ,_W0.a)==0)?false:true:(I_compare(_VZ,_W0.a)==0)?false:true;}},_W1=new T2(0,_QT,_VT),_W2=function(_W3,_W4){var _W5=E(_W3);if(!_W5._){var _W6=_W5.a,_W7=E(_W4);return (_W7._==0)?_W6<=_W7.a:I_compareInt(_W7.a,_W6)>=0;}else{var _W8=_W5.a,_W9=E(_W4);return (_W9._==0)?I_compareInt(_W8,_W9.a)<=0:I_compare(_W8,_W9.a)<=0;}},_Wa=function(_Wb,_Wc){return (!B(_W2(_Wb,_Wc)))?E(_Wb):E(_Wc);},_Wd=function(_We,_Wf){return (!B(_W2(_We,_Wf)))?E(_Wf):E(_We);},_Wg=function(_Wh,_Wi){var _Wj=E(_Wh);if(!_Wj._){var _Wk=_Wj.a,_Wl=E(_Wi);if(!_Wl._){var _Wm=_Wl.a;return (_Wk!=_Wm)?(_Wk>_Wm)?2:0:1;}else{var _Wn=I_compareInt(_Wl.a,_Wk);return (_Wn<=0)?(_Wn>=0)?1:2:0;}}else{var _Wo=_Wj.a,_Wp=E(_Wi);if(!_Wp._){var _Wq=I_compareInt(_Wo,_Wp.a);return (_Wq>=0)?(_Wq<=0)?1:2:0;}else{var _Wr=I_compare(_Wo,_Wp.a);return (_Wr>=0)?(_Wr<=0)?1:2:0;}}},_Ws={_:0,a:_W1,b:_Wg,c:_KW,d:_W2,e:_Kq,f:_KO,g:_Wa,h:_Wd},_Wt=function(_Wu){return new T2(0,E(_Wu),E(_Kj));},_Wv=new T3(0,_VS,_Ws,_Wt),_Ww={_:0,a:_Wv,b:_V3,c:_Vy,d:_Ra,e:_Vf,f:_Vv,g:_VK,h:_Vr,i:_VO},_Wx=new T1(0,0),_Wy=function(_Wz,_WA,_WB){var _WC=B(A1(_Wz,_WA));if(!B(_QT(_WC,_Wx))){return new F(function(){return _V7(B(_RC(_WA,_WB)),_WC);});}else{return E(_OU);}},_WD=function(_WE,_WF,_WG){var _WH=new T(function(){if(!B(_QT(_WG,_R1))){var _WI=B(_VB(_WF,_WG));return new T2(0,_WI.a,_WI.b);}else{return E(_OU);}}),_WJ=new T(function(){return B(A2(_Ko,B(_Km(B(_Kk(_WE)))),new T(function(){return E(E(_WH).a);})));});return new T2(0,_WJ,new T(function(){return new T2(0,E(E(_WH).b),E(_WG));}));},_WK=function(_WL){return E(E(_WL).b);},_WM=function(_WN,_WO,_WP){var _WQ=B(_WD(_WN,_WO,_WP)),_WR=_WQ.a,_WS=E(_WQ.b);if(!B(_KW(B(_RC(_WS.a,_Kj)),B(_RC(_R1,_WS.b))))){return E(_WR);}else{var _WT=B(_Km(B(_Kk(_WN))));return new F(function(){return A3(_WK,_WT,_WR,new T(function(){return B(A2(_Ko,_WT,_Kj));}));});}},_WU=479723520,_WV=40233135,_WW=new T2(1,_WV,_6),_WX=new T2(1,_WU,_WW),_WY=new T(function(){return B(_JV(_aw,_WX));}),_WZ=new T1(0,40587),_X0=function(_X1){var _X2=new T(function(){var _X3=B(_Ui(_X1,_Kj,_TX,_Kj)),_X4=B(_Ui(_WY,_Kj,_TX,_Kj)),_X5=B(_Ui(_X3.a,_X3.b,_X4.a,_X4.b));return B(_WM(_Ww,_X5.a,_X5.b));});return new T2(0,new T(function(){return B(_JH(_WZ,_X2));}),new T(function(){return B(_Lm(_X1,B(_Wy(_Uo,B(_RC(_X2,_TX)),_WY))));}));},_X6=new T1(0,0),_X7=function(_X8,_){var _X9=__get(_X8,0),_Xa=__get(_X8,1),_Xb=Number(_X9),_Xc=jsTrunc(_Xb),_Xd=Number(_Xa),_Xe=jsTrunc(_Xd);return new T2(0,_Xc,_Xe);},_Xf=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_Xg=660865024,_Xh=465661287,_Xi=new T2(1,_Xh,_6),_Xj=new T2(1,_Xg,_Xi),_Xk=new T(function(){return B(_JV(_aw,_Xj));}),_Xl=function(_){var _Xm=__app0(E(_Xf)),_Xn=B(_X7(_Xm,_));return new T(function(){var _Xo=E(_Xn);if(!B(_QT(_Xk,_Wx))){return B(_JH(B(_RC(B(_M7(E(_Xo.a))),_TX)),B(_V7(B(_RC(B(_RC(B(_M7(E(_Xo.b))),_TX)),_TX)),_Xk))));}else{return E(_OU);}});},_Xp=new T1(0,12345),_Xq=function(_){var _Xr=B(_Xl(0)),_Xs=B(_Ui(B(_X0(_Xr)).b,_Kj,_TX,_Kj)),_Xt=_Xs.b;if(!B(_QT(_Xt,_SW))){var _Xu=B(_VB(_Xs.a,_Xt));return new F(function(){return nMV(new T(function(){var _Xv=B(_TZ((B(_US(B(_JH(B(_JH(B(_JH(B(_RC(_Xu.a,_Xp)),_Xu.b)),_X6)),_SW))))>>>0&2147483647)>>>0&4294967295,2147483562));return new T2(0,E(_Xv.b)+1|0,B(_SY(E(_Xv.a),2147483398))+1|0);}));});}else{return E(_OU);}},_Xw=new T(function(){return B(_44(_Xq));}),_Xx=function(_Xy,_){var _Xz=mMV(E(_Xw),function(_XA){var _XB=E(_Xy),_XC=B(_TF(E(_XB.a),E(_XB.b),_XA));return new T2(0,E(_XC.b),_XC.a);}),_XD=E(_Xz);return _Xz;},_XE=1,_XF=new T2(0,_IR,_XE),_XG=function(_){return new F(function(){return _Xx(_XF,_);});},_XH=new T1(1,_XG),_XI=new T(function(){return B(_pg(_XH));}),_XJ=60,_XK=new T1(0,_XJ),_XL=100,_XM=new T1(0,_XL),_XN=new T2(0,_XM,_XM),_XO=-30,_XP=new T1(0,_XO),_XQ=new T(function(){return  -0;}),_XR=new T1(0,_XQ),_XS=new T2(0,_XR,_XR),_XT=3.141592653589793,_XU=new T1(0,_XT),_XV=6,_XW=new T1(0,_XV),_XX=new T(function(){return B(_uj(_in,_XU,_XW));}),_XY=function(_XZ){var _Y0=new T(function(){var _Y1=new T(function(){var _Y2=E(_XI),_Y3=_Y2.a,_Y4=_Y2.b,_Y5=function(_Y6){var _Y7=new T(function(){var _Y8=Math.log(E(_Y6));return Math.sqrt( -(_Y8+_Y8));}),_Y9=function(_Ya){var _Yb=new T(function(){var _Yc=E(_Y7),_Yd=E(_Ya);return _Yc*Math.sin(6.283185307179586*_Yd)+_Yc*Math.sin(6.283185307179586*_Yd);}),_Ye=function(_Yf){var _Yg=new T(function(){var _Yh=new T(function(){var _Yi=new T(function(){var _Yj=new T(function(){var _Yk=new T(function(){return B(_uj(_BU,_XP,new T1(0,new T(function(){return 4/(1-E(_Yf));}))));}),_Yl=B(_Gl(new T1(0,_Yb),_Yk,_XK,_XK));return new T3(0,_Yl.a,_Yl.b,_Yl.c);});return B(_ro(_XZ,_Yj));});return B(_pg(new T3(5,_XS,_Yi,_7)));});return B(_pg(new T3(6,_XX,_Yh,_7)));});return new F(function(){return _pg(new T3(5,_IT,_Yg,_7));});};return new T2(0,E(_Y3),E(new T2(2,_Y4,new T1(1,_Ye))));};return new T2(0,E(_Y3),E(new T2(2,_Y4,new T1(1,_Y9))));};return new T2(0,E(_Y3),E(new T2(2,_Y4,new T1(1,_Y5))));});return B(_pg(new T3(5,_XN,_Y1,_7)));});return function(_Ym,_Yn){return new F(function(){return A1(_Yn,new T2(0,new T2(0,_Y0,_IO),_Ym));});};},_Yo=new T(function(){return B(_AB(_IM,_XY,_IN));}),_Yp=new T(function(){return B(unCStr("height"));}),_Yq=1,_Yr=new T1(1,_6),_Ys=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_Yt=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_Yu=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_Yv=new T(function(){return eval("(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})");}),_Yw=function(_Yx,_Yy,_){while(1){var _Yz=B((function(_YA,_YB,_){var _YC=B(_fo(_YA));if(!_YC._){return _YC.a;}else{var _YD=_YC.b,_YE=E(_YC.a);switch(_YE._){case 0:var _YF=B(A2(_YE.a,_YB,_)),_YG=_YB;_Yx=B(A1(_YD,_YE.b));_Yy=_YG;return __continue;case 1:var _YH=B(A1(_YE.a,_)),_YG=_YB;_Yx=B(A1(_YD,_YH));_Yy=_YG;return __continue;case 2:var _YG=_YB;_Yx=B(A1(_YD,_YE.b));_Yy=_YG;return __continue;case 3:var _YI=B(_Yw(_YE.b,_YE.a,_)),_YG=_YB;_Yx=B(A1(_YD,_YE.c));_Yy=_YG;return __continue;case 4:var _YJ=_YE.h,_YK=function(_YL,_){var _YM=function(_YN,_){var _YO=function(_YP,_){var _YQ=function(_YR,_){var _YS=function(_YT,_){return new F(function(){return _ps(_YE.f,function(_YU,_){var _YV=E(_YB),_YW=__app1(E(_pr),_YV),_YX=__apply(E(_Yv),new T2(1,E(_YU),new T2(1,E(_YT),new T2(1,E(_YR),new T2(1,E(_YP),new T2(1,E(_YN),new T2(1,E(_YL),new T2(1,_YV,_6)))))))),_YY=B(_Yw(_YE.g,_YV,_)),_YZ=__app1(E(_ph),_YV);return new F(function(){return _jl(_);});},_);});};return new F(function(){return _ps(_YE.e,_YS,_);});};return new F(function(){return _ps(_YE.d,_YQ,_);});};return new F(function(){return _ps(_YE.c,_YO,_);});};return new F(function(){return _ps(_YE.b,_YM,_);});},_Z0=E(_YE.a);switch(_Z0._){case 0:var _Z1=B(_YK(_Z0.a,_)),_YG=_YB;_Yx=B(A1(_YD,_YJ));_Yy=_YG;return __continue;case 1:var _Z2=B(A1(_Z0.a,_)),_Z3=B(_YK(_Z2,_)),_YG=_YB;_Yx=B(A1(_YD,_YJ));_Yy=_YG;return __continue;case 2:var _Z4=rMV(E(E(_Z0.a).c)),_Z5=E(_Z4);if(!_Z5._){var _Z6=new T(function(){return B(A1(_Z0.b,new T(function(){return B(_fB(_Z5.a));})));},1),_Z7=B(_YK(_Z6,_)),_YG=_YB;_Yx=B(A1(_YD,_YJ));_Yy=_YG;return __continue;}else{var _YG=_YB;_Yx=B(A1(_YD,_YJ));_Yy=_YG;return __continue;}break;default:var _Z8=rMV(E(E(_Z0.a).c)),_Z9=E(_Z8);if(!_Z9._){var _Za=B(A2(_Z0.b,E(_Z9.a).a,_)),_Zb=B(_YK(_Za,_)),_YG=_YB;_Yx=B(A1(_YD,_YJ));_Yy=_YG;return __continue;}else{var _YG=_YB;_Yx=B(A1(_YD,_YJ));_Yy=_YG;return __continue;}}break;case 5:var _Zc=_YE.c,_Zd=E(_YE.a),_Ze=function(_Zf,_){return new F(function(){return _ps(_Zd.b,function(_Zg,_){var _Zh=E(_YB),_Zi=__app1(E(_pr),_Zh),_Zj=__app3(E(_Yu),_Zh,E(_Zf),E(_Zg)),_Zk=B(_Yw(_YE.b,_Zh,_)),_Zl=__app1(E(_ph),_Zh);return new F(function(){return _jl(_);});},_);});},_Zm=E(_Zd.a);switch(_Zm._){case 0:var _Zn=B(_Ze(_Zm.a,_)),_YG=_YB;_Yx=B(A1(_YD,_Zc));_Yy=_YG;return __continue;case 1:var _Zo=B(A1(_Zm.a,_)),_Zp=B(_Ze(_Zo,_)),_YG=_YB;_Yx=B(A1(_YD,_Zc));_Yy=_YG;return __continue;case 2:var _Zq=rMV(E(E(_Zm.a).c)),_Zr=E(_Zq);if(!_Zr._){var _Zs=new T(function(){return B(A1(_Zm.b,new T(function(){return B(_fB(_Zr.a));})));},1),_Zt=B(_Ze(_Zs,_)),_YG=_YB;_Yx=B(A1(_YD,_Zc));_Yy=_YG;return __continue;}else{var _YG=_YB;_Yx=B(A1(_YD,_Zc));_Yy=_YG;return __continue;}break;default:var _Zu=rMV(E(E(_Zm.a).c)),_Zv=E(_Zu);if(!_Zv._){var _Zw=B(A2(_Zm.b,E(_Zv.a).a,_)),_Zx=B(_Ze(_Zw,_)),_YG=_YB;_Yx=B(A1(_YD,_Zc));_Yy=_YG;return __continue;}else{var _YG=_YB;_Yx=B(A1(_YD,_Zc));_Yy=_YG;return __continue;}}break;case 6:var _Zy=_YE.c,_Zz=function(_ZA,_){var _ZB=E(_YB),_ZC=__app1(E(_pr),_ZB),_ZD=__app2(E(_Yt),_ZB,E(_ZA)),_ZE=B(_Yw(_YE.b,_ZB,_)),_ZF=__app1(E(_ph),_ZB);return new F(function(){return _jl(_);});},_ZG=E(_YE.a);switch(_ZG._){case 0:var _ZH=B(_Zz(_ZG.a,_)),_YG=_YB;_Yx=B(A1(_YD,_Zy));_Yy=_YG;return __continue;case 1:var _ZI=B(A1(_ZG.a,_)),_ZJ=B(_Zz(_ZI,_)),_YG=_YB;_Yx=B(A1(_YD,_Zy));_Yy=_YG;return __continue;case 2:var _ZK=rMV(E(E(_ZG.a).c)),_ZL=E(_ZK);if(!_ZL._){var _ZM=new T(function(){return B(A1(_ZG.b,new T(function(){return B(_fB(_ZL.a));})));},1),_ZN=B(_Zz(_ZM,_)),_YG=_YB;_Yx=B(A1(_YD,_Zy));_Yy=_YG;return __continue;}else{var _YG=_YB;_Yx=B(A1(_YD,_Zy));_Yy=_YG;return __continue;}break;default:var _ZO=rMV(E(E(_ZG.a).c)),_ZP=E(_ZO);if(!_ZP._){var _ZQ=B(A2(_ZG.b,E(_ZP.a).a,_)),_ZR=B(_Zz(_ZQ,_)),_YG=_YB;_Yx=B(A1(_YD,_Zy));_Yy=_YG;return __continue;}else{var _YG=_YB;_Yx=B(A1(_YD,_Zy));_Yy=_YG;return __continue;}}break;case 7:var _ZS=_YE.c,_ZT=E(_YE.a),_ZU=function(_ZV,_){return new F(function(){return _ps(_ZT.b,function(_ZW,_){var _ZX=E(_YB),_ZY=__app1(E(_pr),_ZX),_ZZ=__app3(E(_Ys),_ZX,E(_ZV),E(_ZW)),_100=B(_Yw(_YE.b,_ZX,_)),_101=__app1(E(_ph),_ZX);return new F(function(){return _jl(_);});},_);});},_102=E(_ZT.a);switch(_102._){case 0:var _103=B(_ZU(_102.a,_)),_YG=_YB;_Yx=B(A1(_YD,_ZS));_Yy=_YG;return __continue;case 1:var _104=B(A1(_102.a,_)),_105=B(_ZU(_104,_)),_YG=_YB;_Yx=B(A1(_YD,_ZS));_Yy=_YG;return __continue;case 2:var _106=rMV(E(E(_102.a).c)),_107=E(_106);if(!_107._){var _108=new T(function(){return B(A1(_102.b,new T(function(){return B(_fB(_107.a));})));},1),_109=B(_ZU(_108,_)),_YG=_YB;_Yx=B(A1(_YD,_ZS));_Yy=_YG;return __continue;}else{var _YG=_YB;_Yx=B(A1(_YD,_ZS));_Yy=_YG;return __continue;}break;default:var _10a=rMV(E(E(_102.a).c)),_10b=E(_10a);if(!_10b._){var _10c=B(A2(_102.b,E(_10b.a).a,_)),_10d=B(_ZU(_10c,_)),_YG=_YB;_Yx=B(A1(_YD,_ZS));_Yy=_YG;return __continue;}else{var _YG=_YB;_Yx=B(A1(_YD,_ZS));_Yy=_YG;return __continue;}}break;default:var _10e=B(_Yw(_YE.a,_YB,_)),_YG=_YB;_Yx=B(A1(_YD,_YE.c));_Yy=_YG;return __continue;}}})(_Yx,_Yy,_));if(_Yz!=__continue){return _Yz;}}},_10f=new T1(0,_),_10g=new T1(0,_6),_10h=new T2(0,E(_10g),E(_10f)),_10i=40,_10j=new T1(0,_10i),_10k=function(_10l){return E(E(_10l).b);},_10m=function(_10n,_10o){var _10p=E(_10n);if(!_10p._){return E(_10h);}else{var _10q=E(_10o);if(!_10q._){return E(_10h);}else{var _10r=B(_pg(new T3(5,new T2(0,_10j,new T1(0,new T(function(){return 40+240*E(_10p.a);}))),new T(function(){return B(_10k(_10q.a));}),_7))),_10s=new T(function(){return B(_10m(_10p.b,_10q.b));}),_10t=function(_10u){var _10v=E(_10s);return new T2(0,E(_10v.a),E(new T2(2,_10v.b,new T1(1,function(_10w){return new T2(0,E(new T1(0,new T2(1,_10u,_10w))),E(_10f));}))));};return new T2(0,E(_10r.a),E(new T2(2,_10r.b,new T1(1,_10t))));}}},_10x=function(_10y){return new F(function(){return _p8(_7,new T(function(){return B(_10m(_HQ,_10y));}));});},_10z=function(_10A,_10B){var _10C=function(_10D,_){var _10E=E(_10A),_10F=__app1(E(_ib),_10E.b);return new F(function(){return _Yw(B(_10x(_10D)),_10E.a,_);});},_10G=new T(function(){return B(A1(_Fz,_10B));}),_10H=function(_10I){var _10J=function(_10K){var _10L=E(_10K),_10M=function(_10N){var _10O=E(_10N),_10P=function(_10Q){var _10R=E(_10Q),_10S=new T2(1,_10L.a,new T2(1,_10O.a,new T2(1,_10R.a,_6))),_10T=function(_){var _10U=jsShow(40+B(_eT(_10S,0))*240),_10V=__app3(E(_ic),E(_10A).b,toJSStr(E(_Yp)),toJSStr(fromJSStr(_10U))),_10W=function(_){var _10X=nMV(new T2(0,_10S,_6));return new T(function(){var _10Y=new T(function(){return B(_9I(_8l,_10X,_eY));}),_10Z=function(_110){return new F(function(){return _111(E(_110).b);});},_112=function(_113){return new F(function(){return _BY(_Yq,E(_113).b,_10Z);});},_114=function(_115){var _116=E(_115);return new F(function(){return A(_fU,[B(_10x(_116.a)),_f3,_f2,_f2,_f2,_f3,_f2,_116.b,_112]);});},_111=function(_117){return new F(function(){return A2(_10Y,_117,_114);});},_118=function(_119){var _11a=E(_119).b,_11b=function(_){var _11c=nMV(_Yr);return new T1(1,new T2(1,new T(function(){return B(A1(_10I,new T2(0,_7,_11a)));}),new T2(1,new T(function(){return B(_111(_11a));}),_6)));};return new T1(0,_11b);};return new T1(0,B(_e8(_10X,_10C,_10R.b,_118)));});};return new T1(0,_10W);};return new T1(0,_10T);};return new F(function(){return A2(_Yo,_10O.b,_10P);});};return new F(function(){return A2(_IL,_10L.b,_10M);});};return new F(function(){return A1(_10G,_10J);});};return E(_10H);},_11d=new T(function(){return B(unCStr("Canvas not found!"));}),_11e=new T(function(){return B(err(_11d));}),_11f="canvas",_11g=new T(function(){return eval("(Util.onload)");}),_11h=function(_){var _11i=__app1(E(_11g),E(_48)),_11j=B(A3(_e1,_2G,_11f,_)),_11k=E(_11j);if(!_11k._){return E(_11e);}else{var _11l=E(_11k.a),_11m=__app1(E(_1),_11l);if(!_11m){return E(_11e);}else{var _11n=__app1(E(_0),_11l),_11o=_11n,_11p=new T(function(){return new T1(0,B(_d7(function(_11q){return new F(function(){return _10z(new T2(0,_11o,_11l),_11q);});},_2I)));});return new F(function(){return _e(_11p,_6,_);});}}},_11r=function(_){return new F(function(){return _11h(_);});};
var hasteMain = function() {B(A(_11r, [0]));};window.onload = hasteMain;