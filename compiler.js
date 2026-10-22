(() => {
  "use strict";

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
     * }} Opcode
     */

    class WFunc {
      constructor() {
        this.parameters = /** @type {WLocal[]} */ ([]);
        this.returnType = /** @type {WValType} */ ('i32');
        this.export = /** @type {string | null} */ (null);
        this.import = /** @type {[string, string] | null} */ (null);
        this.code = /** @type {Opcode[] | null} */ (null);
      }

      /** @param {WValType} */
      newParameter(type) {
        const parameter = this.newLocal(type);
        this.parameters.push(parameter);
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

      // variable
      get(variable) {
        return /** @type {Opcode} */ ({ kind: "get", variable });
      },
      set(variable) {
        return /** @type {Opcode} */ ({ kind: "set", variable });
      },
      tee(variable) {
        return /** @type {Opcode} */ ({ kind: "tee", variable });
      },

      // numeric
      i32: {
        const(value) {
          return [0x41, lebI32(value)];
        },

        add: 0x6A,
      },
      i64: {
        const(value) {
          return [0x42, lebI64(value)];
        },
      },
      f32: {
        const(value) {
          return [0x43, emitF32(value)];
        },
      },
      f64: {
        const(value) {
          return [0x44, emitF64(value)];
        }
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
        ida = tempIds.get(fa);
        idb = tempIds.get(fb);
        return ida < idb ? -1 : idb < ida ? 1 : 0;
      });
    }

    const wfuncsWithIds = wfuncs.map((f, i) => pairOf(f, i));
    const importFuncsWithIds = wfuncsWithIds.filter(([f, i]) => f.import);
    const definedFuncsWithIds = wfuncsWithIds.filter(([f, i]) => !f.import);
    const definedFuncs = definedFuncsWithIds.map(([f, i]) => f);

    const typeSection = emitSection(1, emitList([
      // this way, wasm functions map to their type id directly.
      ...wfuncs.map(f => [
        0x60,
        emitList(f.parameters.map(p => WVAL_ENCODING_MAP[p.type])),
        emitList([WVAL_ENCODING_MAP[f.returnType]]),
      ]),
    ]));

    const importSection = emitSection(2, emitList([
      ...importFuncsWithIds.map(([f, i]) => {
        const [moduleName, itemName] = f.import;
        return [
          emitName(moduleName),
          emitName(itemName),
          0x00, lebu(i),
        ];
      }),
    ]));

    const functionSection = emitSection(3, emitList([
      ...definedFuncsWithIds
        .map(([f, i]) => { return lebu(i); }),
    ]));

    const globalSection = emitSection(6, emitList([
      ...wglobals.map(g => [
        WVAL_ENCODING_MAP[g.type], // global's type
        0x01, // mutable
        CODE.zeroForType(g.type), 0x0B, // expr
      ]),
    ]));

    const exportSection = emitSection(7, emitList([
      ...wfuncsWithIds.filter(([f, i]) => f.export).map(([f, i]) => {
        return [
          emitName(f.export),
          0x00, lebu(i),
        ];
      }),
    ]));

    const codeSection = emitSection(10, emitList([
      ...definedFuncs.map(f => {

        const flatCode = f.code.flat(Infinity);

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
          locals.forEach((v, i) => v.slotId = i);
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
                    JSON.stringify(variable)}`);
              }
              reifiedCode.push(code, variable.slotId);
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

  const wasmBytes = emit(b => {
    const { CODE } = b;

    const globalA = b.newGlobal(I32);

    const puti = b.newFunc();
    puti.import = ["c", "puti"];

    const func = b.newFunc();
    {
      const localA = func.newLocal(I32);
      func.export = "main";
      func.code = [
        CODE.i32.const(777), // A = 777
        // CODE.tee(localA),
        CODE.set(globalA),
        CODE.get(globalA), // A + A
        CODE.get(globalA),
        CODE.i32.add,

        // CODE.i32.const(555),
        // CODE.i32.const(47),
        // CODE.i32.add,
        CODE.ret,
      ];
    }
  });
  WebAssembly.instantiate(wasmBytes, {
    c: {
      puti(x) {
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
})();
