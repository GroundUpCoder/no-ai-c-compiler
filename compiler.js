(() => {
  "use strict";

  // #region WASM

  /**
   * @template {*} A
   * @template {*} B
   * @param {A} a 
   * @param {B} b 
   * @returns {[A, B]}
   */
  function pairOf(a, b) {
    return [a, b];
  }
  
  function lebu(x) {
    const CONTINUE_BIT = 0b10000000;
    x = BigInt(x);
    if (x < 0n) throw new Error(`lebu(${x})`);
    const bytes = [];
    for (;;) {
      const byte = Number(x & 0b1111111n); // low 7 bits
      x >>= 7n;
      bytes.push(x ? (CONTINUE_BIT | byte) : byte);
      if (!x) break;
    }
    return bytes;
  }

  function lebs(x) {
    const CONTINUE_BIT = 0b10000000;
    x = BigInt(x);
    const bytes = [];
    for (;;) {
      const byte = Number(x & 0b1111111n); // low 7 bits
      x >>= 7n;
      const byteIsNegative = 0b1000000 & byte;
      const done =
        (byteIsNegative && x === -1n) ||
        (!byteIsNegative && x === 0n);
      bytes.push(done ? byte : (byte | CONTINUE_BIT));
      if (done) break;
    }
    return bytes;
  }

  function lebI32(x) {
    return lebs(BigInt.asIntN(32, BigInt(x)));
  }

  function lebI64(x) {
    return lebs(BigInt.asIntN(64, BigInt(x)));
  }

  const _f32arr = new Float32Array(1);
  const _f32arrbytes = new Uint8Array(_f32arr.buffer);
  function emitF32(x) {
    _f32arr[0] = x;
    return [
      _f32arrbytes[0],
      _f32arrbytes[1],
      _f32arrbytes[2],
      _f32arrbytes[3],
    ];
  }

  const _f64arr = new Float64Array(1);
  const _f64arrbytes = new Uint8Array(_f64arr.buffer);
  function emitF64(x) {
    _f64arr[0] = x;
    return [
      _f64arrbytes[0], _f64arrbytes[1],
      _f64arrbytes[2], _f64arrbytes[3],
      _f64arrbytes[4], _f64arrbytes[5],
      _f64arrbytes[6], _f64arrbytes[7],
    ];
  }

  const _utf8Encoder = new TextEncoder();
  function emitName(name) {
    const bytes = _utf8Encoder.encode(name);
    return [lebu(bytes.length), ...bytes];
  }

  function emitList(items) {
    return [lebu(items.length), items];
  }

  function emitSection(id, contents) {
    contents = contents.flat(Infinity);
    return [id, lebu(contents.length), contents];
  }

  const I32 = /** @type {WValType} */ ('i32');
  const I64 = /** @type {WValType} */ ('i64');
  const F32 = /** @type {WValType} */ ('f32');
  const F64 = /** @type {WValType} */ ('f64');

  /** @typedef {'i32'|'i64'|'f32'|'f64'} WValType */

  const WVAL_ENCODING_MAP = /** @type {const} */ ({
    f64: 0x7C,
    f32: 0x7D,
    i64: 0x7E,
    i32: 0x7F,
  });

  /**
   * @param {(b: typeof builder) => ()} f
   */
  function emit(f) {

    class WVariable {
      /** @param {WValType} type */
      constructor(type) {
        if (!type) {
          throw new Error(`WVariable(type=${type})`);
        }
        this.type = type;
        this.slotId = -1;
      }
    }
    let _nextGlobalSlotId = 0;
    class WGlobal extends WVariable {
      constructor(type) {
        super(type);
        this.slotId = _nextGlobalSlotId++;
      }
    }
    class WLocal extends WVariable {}

    /**
     * @typedef {number | {
     *  kind: "get",
     *  variable: WVariable,
     * } | {
     *  kind: "set",
     *  variable: WVariable,
     * } | {
     *  kind: "tee",
     *  variable: WVariable,
     * } | {
     *  kind: "call",
     *  func: WFunc,
     * }} Opcode
     */

    class WFunc {
      constructor() {
        this.funcidx = -1;
        this.parameters = /** @type {WLocal[]} */ ([]);
        this.returnType = I32; // 'void' will use i32 instead of empty return type
        this.export = /** @type {string | null} */ (null);
        this.import = /** @type {[string, string] | null} */ (null);
        this.code = /** @type {Opcode[] | null} */ (null);
      }

      /** @param {WValType} */
      newParameter(type) {
        const parameter = this.newLocal(type);
        this.parameters.push(parameter);
        return parameter;
      }

      /** @param {WValType} */
      newLocal(type) {
        if (!type) throw new Error(`newLocal(${type})`);
        return new WLocal(type);
      }
    }

    const CODE = /** @type {const} */ ({
      // parametric
      unreachable: 0x00,
      nop: 0x01,
      drop: 0x1A,

      // control
      block(body) {
        return [0x02, 0x40, body, 0x0B];
      },
      loop(body) {
        return [0x03, 0x40, body, 0x0B];
      },
      call(func) {
        return /** @type {Opcode} */ ({ kind: "call", func });
      },

      // variable
      get(variable) {
        if (!(variable instanceof WVariable)) {
          throw new Error(`CODE.get(${variable})`);
        }
        return /** @type {Opcode} */ ({ kind: "get", variable });
      },
      set(variable) {
        return /** @type {Opcode} */ ({ kind: "set", variable });
      },
      tee(variable) {
        return /** @type {Opcode} */ ({ kind: "tee", variable });
      },

      get add() {
        throw new Error(`CODE.add is invalid, do CODE.i32.add, etc`);
      },

      // numeric
      i32: {
        const(value) {
          return [0x41, lebI32(value)];
        },

        eqz: 0x45,
        eq: 0x46,
        ne: 0x47,
        lt_s: 0x48,
        lt_u: 0x49,
        gt_s: 0x4A,
        gt_u: 0x4B,
        le_s: 0x4C,
        le_u: 0x4D,
        ge_s: 0x4E,
        ge_u: 0x4F,

        clz: 0x67,
        ctz: 0x68,
        popcnt: 0x69,
        add: 0x6A,
        sub: 0x6B,
        mul: 0x6C,
        div_s: 0x6D,
        div_u: 0x6E,
        rem_s: 0x6F,
        rem_u: 0x70,
        and: 0x71,
        or: 0x72,
        xor: 0x73,
        shl: 0x74,
        shr_s: 0x75,
        shr_u: 0x76,
        rotl: 0x77,
        rotr: 0x78,
      },
      i64: {
        const(value) {
          return [0x42, lebI64(value)];
        },

        eqz: 0x50,
        eq: 0x51,
        ne: 0x52,
        lt_s: 0x53,
        lt_u: 0x54,
        gt_s: 0x55,
        gt_u: 0x56,
        le_s: 0x57,
        le_u: 0x58,
        ge_s: 0x59,
        ge_u: 0x5A,

        clz: 0x79,
        ctz: 0x7A,
        popcnt: 0x7B,
        add: 0x7C,
        sub: 0x7D,
        mul: 0x7E,
        div_s: 0x7F,
        div_u: 0x80,
        rem_s: 0x81,
        rem_u: 0x82,
        and: 0x83,
        or: 0x84,
        xor: 0x85,
        shl: 0x86,
        shr_s: 0x87,
        shr_u: 0x88,
        rotl: 0x89,
        rotr: 0x8A,
      },
      f32: {
        const(value) {
          return [0x43, emitF32(value)];
        },

        eq: 0x5B,
        ne: 0x5C,
        lt: 0x5D,
        gt: 0x5E,
        le: 0x5F,
        ge: 0x60,

        abs: 0x8B,
        neg: 0x8C,
        ceil: 0x8D,
        floor: 0x8E,
        trunc: 0x8F,
        nearest: 0x90,
        sqrt: 0x91,
        add: 0x92,
        sub: 0x93,
        mul: 0x94,
        div: 0x95,
        min: 0x96,
        max: 0x97,
        copysign: 0x98,
      },
      f64: {
        const(value) {
          return [0x44, emitF64(value)];
        },

        eq: 0x61,
        ne: 0x62,
        lt: 0x63,
        gt: 0x64,
        le: 0x65,
        ge: 0x66,

        abs: 0x99,
        neg: 0x9A,
        ceil: 0x9B,
        floor: 0x9C,
        trunc: 0x9D,
        nearest: 0x9E,
        sqrt: 0x9F,
        add: 0xA0,
        sub: 0xA1,
        mul: 0xA2,
        div: 0xA3,
        min: 0xA4,
        max: 0xA5,
        copysign: 0xA6,
      },

      /** @param {WValType} type */
      zeroForType(type) {
        switch (type) {
          case "f32": return CODE.f32.const(0);
          case "f64": return CODE.f64.const(0);
          case "i32": return CODE.i32.const(0);
          case "i64": return CODE.i64.const(0);
        }
        throw new Error(`zeroForType(${type})`);
      },

      ret: 0x0F,
    });

    const wfuncs = /** @type {WFunc[]} */ ([]);
    const wglobals = /** @type {WGlobal[]} */ ([]);

    const builder = /** @type {const} */ {
      CODE,

      newFunc() {
        const func = new WFunc();
        wfuncs.push(func);
        return func;
      },

      /** @param {WValType} type */
      newGlobal(type) {
        const variable = new WGlobal(type);
        wglobals.push(variable);
        return variable;
      },
    };

    f(builder);

    {
      const tempIds = new Map(wfuncs.map((f, i) => [f, i]));
      wfuncs.sort((fa, fb) => {
        if (fa.import && !fb.import) {
          return -1; // fa < fb
        }
        if (!fa.import && fb.import) {
          return 1; // fb < fa
        }
        const ida = tempIds.get(fa);
        const idb = tempIds.get(fb);
        return ida < idb ? -1 : idb < ida ? 1 : 0;
      });
    }

    wfuncs.forEach((f, i) => f.funcidx = i);
    const importFuncs = wfuncs.filter(f => f.import);
    const definedFuncs = wfuncs.filter(f => !f.import);

    const typeSection = emitSection(1, emitList([
      // this way, wasm functions map to their type id directly.
      ...wfuncs.map(f => [
        0x60,
        emitList(f.parameters.map(p => WVAL_ENCODING_MAP[p.type])),
        emitList([WVAL_ENCODING_MAP[f.returnType]]),
      ]),
    ]));

    const importSection = emitSection(2, emitList([
      ...importFuncs.map(f => {
        const [moduleName, itemName] = f.import;
        return [
          emitName(moduleName),
          emitName(itemName),
          0x00, lebu(f.funcidx),
        ];
      }),
    ]));

    const functionSection = emitSection(3, emitList([
      ...definedFuncs.map(f => lebu(f.funcidx)),
    ]));

    const globalSection = emitSection(6, emitList([
      ...wglobals.map(g => [
        WVAL_ENCODING_MAP[g.type], // global's type
        0x01, // mutable
        CODE.zeroForType(g.type), 0x0B, // expr
      ]),
    ]));

    const exportSection = emitSection(7, emitList([
      ...wfuncs.filter(f => f.export).map(f => {
        return [
          emitName(f.export),
          0x00, lebu(f.funcidx),
        ];
      }),
    ]));

    const codeSection = emitSection(10, emitList([
      ...definedFuncs.map(f => {

        const flatCode = f.code.flat(Infinity);

        f.parameters.forEach((p, i) => p.slotId = i);

        const locals = /** @type {WLocal[]} */ ([]);
        {
          // collect all local variables inferred from code/body
          // of the function itself
          const seenVariables = new Set(f.parameters);
          for (const item of flatCode) {
            if (typeof item === 'number') continue;
            switch (item.kind) {
              case "get":
              case "set":
              case "tee": {
                const variable = item.variable;
                if (!(variable instanceof WLocal)) continue;
                if (!seenVariables.has(variable)) {
                  seenVariables.add(variable);
                  locals.push(variable);
                }
              }
            }
          }

          // temporary slotId assignments for tie breakers in the sort
          locals.forEach((v, i) => v.slotId = i);

          // sort the locals so that locals of the same type
          // are right next to each other.
          locals.sort((a, b) => {
            if (a.type !== b.type) {
              return a.type < b.type ? -1 : b.type < a.type ? 1 : 0;
            }
            return a.slotId - b.slotId;
          });

          // Assign the final slot ids for each local variable.
          locals.forEach((v, i) => v.slotId = f.parameters.length + i);
        }

        // TODO: actually group the declarations so that it's per-type
        // not per-slot.
        const localsEncoded = emitList([
          ...locals.map(v => [lebu(1), WVAL_ENCODING_MAP[v.type]]),
        ]);

        const reifiedCode = /** @type {number[]} */ ([]);
        for (const item of flatCode) {
          if (typeof item === 'number') {
            reifiedCode.push(item); // raw opcode
            continue;
          }
          switch (item.kind) {
            case "get":
            case "set":
            case "tee": {
              const variable = item.variable;
              const code =
                (variable instanceof WLocal) ? (
                  item.kind === "get" ? 0x20 :
                  item.kind === "set" ? 0x21 :
                  item.kind === "tee" ? 0x22 : -1) :
                (variable instanceof WGlobal) ? (
                  item.kind === "get" ? 0x23 :
                  item.kind === "set" ? 0x24 : -1) : -1;
              if (code === -1) {
                throw new Error(
                  `invalid variable get/set/tee combo ${
                    JSON.stringify(item)}`);
              }
              if (variable.slotId < 0) {
                throw new Error(
                  `Variable used before slot assigned ${
                    JSON.stringify(variable)} (${
                      variable.constructor.name})`);
              }
              reifiedCode.push(code, lebu(variable.slotId));
              break;
            }
            case "call": {
              const func = /** @type {WFunc} */ (item.func);
              reifiedCode.push(0x10, lebu(func.funcidx));
              break;
            }
            default:
              throw new Error(`Unrecognized item kind ${item.kind}`);
          }
        }
        const expr = [
          ...reifiedCode,
          0x0B,
        ];
        const func = [localsEncoded, expr].flat(Infinity);
        const code = [lebu(func.length), func];
        return code;
      }),
    ]));

    return new Uint8Array([
      0x00, 0x61, 0x73, 0x6D, // magic
      0x01, 0x00, 0x00, 0x00, // version
      // sections
      ...typeSection, // 1
      ...importSection, // 2
      ...functionSection, // 3
      ...globalSection, // 6
      ...exportSection, // 7
      ...codeSection, // 10
    ].flat(Infinity));
  }

  // #endregion WASM

  // #region TOKENIZER

  const KEYWORDS = /** @type {const} */ ([
    "auto", "extern", "short", "while", "break",
    "float", "signed", "_Alignas", "case", "for",
    "sizeof", "_Alignof", "char", "goto", "static",
    "_Atomic", "const", "if", "struct", "_Bool", "continue",
    "inline", "switch", "_Complex", "default", "int",
    "typedef", "_Generic", "do", "long", "union", "_Imaginary",
    "double", "register", "unsigned", "_Noreturn", "else",
    "restrict", "void", "_Static_assert", "enum", "return",
    "volatile", "_Thread_local",
  ]);

  const KEYWORD_SET = new Set(KEYWORDS);

  const PUNCTUATORS = /** @type {const} */ ([
    "[", "]", "(", ")", "{", "}", ".", "->",
    "++", "--", "&", "*", "+", "-", "~", "!",
    "/", "%", "<<", ">>", "<", ">", "<=", ">=", "==", "!=", "^", "|", "&&", "||",
    "?", ":", ";", "...",
    "=", "*=", "/=", "%=", "+=", "-=", "<<=", ">>=", "&=", "^=", "|=",
    ",",
  ]);

  const REVERSE_SORTED_PUNCTUATORS = PUNCTUATORS.toSorted().reverse();

  /**
   * @typedef {{
   *  type: typeof KEYWORDS[number] |
   *    "IDENT" | "INT" | "DOUBLE" | "STR" |
   *    typeof PUNCTUATORS[number]
   *  value?: string | number
   *  line: number
   * }} Token
   * 
   * @typedef {Token["type"]} TokenType
   */

  /**
   * @param {string} source
   * @returns {Token[]}
   */
  function tokenize(source) {
    const s = source;
    const n = s.length;
    let i = 0, line = 1;
    const tokens = /** @type {Token[]} */ ([]);

    const isspace = c => (typeof c === 'string' && " \f\n\r\t\v".includes(c));
    const isdigit = c => (typeof c === 'string' && /[0-9]/.test(c));
    const isident = c => (typeof c === 'string' && /[a-z0-9A-Z_]/.test(c));

    nextToken: while (i < n) {
      // Skip spaces and comments
      if (isspace(s[i])) {
        if (s[i] === '\n') line++;
        i++;
        continue;
      }
      if (s.startsWith("//", i)) {
        while (i < n && s[i] !== '\n') i++;
        continue;
      }
      if (s.startsWith("/*", i)) {
        i += 2;
        while (!s.startsWith("*/", i)) {
          if (s[i] === '\n') line++;
          i++;
        }
        i += 2;
        continue;
      }

      const j = i; // start of next token

      // keywords and identifiers
      if (!isdigit(s[i]) && isident(s[i])) {
        while (isident(s[i])) i++;
        const value = s.slice(j, i);
        if (KEYWORD_SET.has(value)) {
          tokens.push({ type: value, line });
        } else {
          tokens.push({ type: "IDENT", value, line });
        }
        continue nextToken;
      }

      // constants
      // integers
      if (isdigit(s[i]) || (s[i] === '.' && isdigit(s[i + 1]))) {
        let radix = 10;
        let start = j;
        if (s.startsWith("0x", i)) {
          i += 2;
          start += i;
          radix = 16;
        }
        while (isdigit(s[i])) i++;
        if (s[i] === '.') {
          i++;
          while (isdigit(s[i])) i++;
          const value = parseFloat(s.slice(start, i));
          tokens.push({ type: "DOUBLE", value, line });
          continue nextToken;
        }
        const value = parseInt(s.slice(start, i), radix);
        tokens.push({ type: "INT", value, line });
        continue nextToken;
      }

      // string literals
      if (s[i] === '"') {
        let value = '';
        i++;
        while (i < n && s[i] !== '"') {
          if (s[i] === '\\') {
            i++;
            switch (s[i]) {
              case "\\":
              case "'":
              case '"': value += s[i]; i++; break;
              case 'f': value += '\f'; i++; break;
              case 'n': value += '\n'; i++; break;
              case 'r': value += '\r'; i++; break;
              case 't': value += '\t'; i++; break;
              case 'v': value += '\v'; i++; break;
              default:
                throw new Error(`Invalid or unsupported string escape ${
                  JSON.stringify(s[i])} on line ${line}`);
            }
          } else if (s[i] === '\n') {
            throw new Error(
              `Unterminated string literal on line ${line} (newline encountered)`);
          } else value += s[i++]; // TODO: consider if this is ok with UTF-16
        }
        if (s[i] !== '"') {
          throw new Error(`Unterminated string literal on line ${line}`);
        }
        i++; // closing quote
        tokens.push({ type: "STR", value, line });
        continue nextToken;
      }

      // punctuator
      for (const punct of REVERSE_SORTED_PUNCTUATORS) {
        if (s.startsWith(punct, i)) {
          tokens.push({ type: punct, line });
          i += punct.length;
          continue nextToken;
        }
      }

      // TODO: emit error token instead of throwing
      // Unrecognized token
      while (!isspace(s[i])) i++;
      throw new Error(`Unrecognized token ${s.slice(j, i)} on line ${line}`);
    }

    return tokens;
  }

  // #endregion

  // #region PARSER

  /**
   * @param {Token[]} tokens
   * @returns {Uint8Array} wasm bytes
   */
  function parseTokens(tokens) {
    const ts = tokens;
    const n = ts.length;
    let i = 0;

    function at(tokenType, offset = 0) {
      return ts[i + offset]?.type === tokenType;
    }

    function consume(tokenType) {
      if (ts[i]?.type === tokenType) {
        return ts[i++];
      }
    }

    /** @param {TokenType} tokenType */
    function expect(tokenType) {
      const token = consume(tokenType);
      if (!token) throw new Error(`Expected ${tokenType} but got ${token?.type}`);
      return token;
    }

    return emit(b => {
      const { CODE } = b;

      let activeFunc = null;


      function parsePrimaryExpression() {
        const value = expect("INT").value;
        activeFunc.code.push(CODE.i32.const(value));
      }

      function parseExpression() {
        parsePrimaryExpression();
        while (consume("+")) {
          parsePrimaryExpression();
          activeFunc.code.push(CODE.i32.add);
        }
      }

      function parseStatement() {
        if (consume("{")) { // compound
          while (!consume("}")) {
            parseStatement();
          }
        } else if (consume("return")) {
          parseExpression();
          expect(";");
          activeFunc.code.push(CODE.ret);
        } else {
          parseExpression();
          expect(";");
        }
      }

      function parseFunction() {
        expect("int"); // TODO: return types
        const functionName = expect("IDENT").value;
        const wfunc = b.newFunc();
        wfunc.export = functionName;
        activeFunc = wfunc;
        wfunc.code = [];
        expect("("); // TODO: parameters
        expect(")");
        parseStatement();
      }

      function parseTranslationUnit() {
        while (i < n) {
          parseFunction();
        }
      }

      parseTranslationUnit();
    });
  }

  // #endregion PARSER

  // // #region WASM TESTS
  // const wasmBytes = emit(b => {
  //   const { CODE } = b;

  //   const globalA = b.newGlobal(I32);

  //   const puti = b.newFunc();
  //   puti.newParameter(I32);
  //   puti.import = ["c", "puti"];

  //   const putd = b.newFunc();
  //   putd.newParameter(F64);
  //   putd.import = ["c", "putd"];

  //   const func2 = b.newFunc();
  //   {
  //     const param1 = func2.newParameter(I32);
  //     func2.code = [

  //       // puti(param1 + 1);
  //       CODE.get(param1),
  //       CODE.i32.const(2),
  //       CODE.i32.add,
  //       CODE.call(puti),
  //       CODE.drop,

  //       CODE.i32.const(0), CODE.ret, // return 0
  //     ];
  //   }

  //   const main = b.newFunc();
  //   {
  //     const localA = main.newLocal(I32);
  //     main.export = "main";
  //     main.code = [

  //       // func2(15);
  //       CODE.i32.const(15),
  //       CODE.call(func2),

  //       CODE.f64.const(7.5),
  //       CODE.f64.const(7.5),
  //       CODE.f64.mul,
  //       CODE.call(putd),
  //       CODE.drop,

  //       CODE.i32.const(888),
  //       CODE.call(puti),
  //       CODE.drop,

  //       CODE.i32.const(777), // A = 777
  //       // CODE.tee(localA),
  //       CODE.set(globalA),
  //       CODE.get(globalA), // A + A
  //       CODE.get(globalA),
  //       CODE.i32.add,

  //       // CODE.i32.const(555),
  //       // CODE.i32.const(47),
  //       // CODE.i32.add,
  //       CODE.ret,
  //     ];
  //   }
  // });
  // WebAssembly.instantiate(wasmBytes, {
  //   c: {
  //     puti(x) {
  //       console.log(x);
  //     },
  //     putd(x) {
  //       console.log(x);
  //     },
  //   },
  // })
  //   .then(({ instance }) => {
  //     const { exports } = instance;
  //     if (exports.main) {
  //       const returnValue = exports.main();
  //       console.log('main returned', returnValue);
  //     } else {
  //       console.log('no main function found');
  //     }
  //   })
  //   .catch(e => console.log('error', e));

  // // #endregion WASM TESTS

  // // #region TOKENIZER TESTS

  // const tokens = tokenize(`
  //   int main() { return 123; }
  // `);
  // console.log(`tokens`, tokens);

  // // #endregion TOKENIZER TESTS

  // #region PARSER TESTS
  {
    const tokens = tokenize(`
      int main() { return 2 + 5; }
    `);
    console.log(`tokens`, tokens);
    const wasmBytes = parseTokens(tokens);
    WebAssembly.instantiate(wasmBytes, {
      c: {
        puti(x) {
          console.log(x);
        },
        putd(x) {
          console.log(x);
        },
      },
    })
      .then(({ instance }) => {
        const { exports } = instance;
        if (exports.main) {
          const returnValue = exports.main();
          console.log('main returned', returnValue);
        } else {
          console.log('no main function found');
        }
      })
      .catch(e => console.log('error', e));
  }
  // #endregion PARSER TESTS

})();
