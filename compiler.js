(() => {
  "use strict";
  
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
        this.type = type;
      }
    }
    class WGlobal extends WVariable {}
    class WLocal extends WVariable {}

    class WFunc {
      constructor() {
        this.parameters = /** @type {WLocal[]} */ ([]);
        this.returnType = /** @type {WValType} */ ('i32');
        this.locals = /** @type {WLocal[]} */ ([]);
        this.export = /** @type {string | null} */ (null);
        this.import = /** @type {[string, string] | null} */ (null);
      }

      /** @param {WValType} */
      newParameter(type) {
        const parameter = this.newLocal(type);
        this.parameters.push(parameter);
      }

      /** @param {WValType} */
      newLocal(type) {
        const localvar = new WLocal(type);
        this.locals.push(localvar);
        return localvar;
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

      i32: {
        const(value) {
          return [0x41, lebI32(value)];
        },
      },

      ret: 0x0F,
    });

    const wfuncs = /** @type {WFunc[]} */ ([]);

    const builder = /** @type {const} */ {
      newFunc() {
        const func = new WFunc();
        wfuncs.push(func);
        return func;
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

    const wfuncsWithIds = wfuncs.map((f, i) => [f, i]);
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

    console.log('functionSection', functionSection);

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
        const locals = emitList([
          ...f.locals.slice(f.parameters.length).map(p =>
            [lebu(1), WVAL_ENCODING_MAP[p.type]]),
        ]);
        const expr = [
          CODE.i32.const(6789),
          CODE.ret,
          0x0B,
        ];
        const func = [locals, expr].flat(Infinity);
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
      ...exportSection, // 7
      ...codeSection, // 10
    ].flat(Infinity));
  }

  const wasmBytes = emit(b => {
    const puti = b.newFunc();
    puti.import = ["c", "puti"];

    const func = b.newFunc();
    func.export = "someFunc";
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
      console.log(exports.someFunc());
    })
    .catch(e => console.log('error', e));
})();
