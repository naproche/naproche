import targetSpecificModule from './default.mjs';

var closure = null;

onmessage = function(msg) {
    if(closure !== null) {
        var cl = closure
        closure = null;
        cl(msg.data);
    } else {
        console.log("Unhandled by Naproche Worker: ");
        console.log(msg.data);
    }
};

var requestMessage = function(msg) {
    postMessage(msg);
    return new Promise((resolve, reject) => {
        closure = resolve;
    });
};

var sendMessage = function(msg) {
    postMessage(msg);
};

export default {progName: "Naproche-Web", jsffiFactory: __asterius_jsffi=>({jsffi: {__asterius_jsffi_asteriuszmpreludezuAsteriusziAeson_ac01:($1)=>{$1 = __asterius_jsffi.getJSValzh($1);return __asterius_jsffi.newJSValzh(JSON.parse($1));},__asterius_jsffi_asteriuszmpreludezuAsteriusziAeson_ac07:($1)=>{$1 = __asterius_jsffi.getJSValzh($1);return __asterius_jsffi.newJSValzh(JSON.stringify($1));},__asterius_jsffi_asteriuszmpreludezuAsteriusziUTF8_a4hj:($1,$2,$3)=>{$1 = __asterius_jsffi.getJSValzh($1);return ((new TextEncoder()).encodeInto($1, __asterius_jsffi.exposeMemory($2, $3)).written);},__asterius_jsffi_asteriuszmpreludezuAsteriusziUTF8_a4hp:($1)=>{$1 = __asterius_jsffi.getJSValzh($1);return __asterius_jsffi.newJSValzh($1.result);},__asterius_jsffi_asteriuszmpreludezuAsteriusziUTF8_a4LW:($1,$2,$3)=>{$1 = __asterius_jsffi.getJSValzh($1);return ($1.result += $1.decode(__asterius_jsffi.exposeMemory($2, $3), {stream: true}));},__asterius_jsffi_asteriuszmpreludezuAsteriusziUTF8_a4M3:()=>{return __asterius_jsffi.newJSValzh((() => {                const dec = new TextDecoder('utf-8', {fatal: true});   dec.result = '';                                       return dec;                                            })());},__asterius_jsffi_asteriuszmpreludezuAsteriusziUTF8_a4Ma:()=>{return __asterius_jsffi.newJSValzh('');},__asterius_jsffi_basezuAsteriusziTypesziJSException_a8Zfo:($1)=>{$1 = __asterius_jsffi.getJSValzh($1);return __asterius_jsffi.newJSValzh($1.stack ? $1.stack : `${$1}`);},__asterius_jsffi_basezuAsteriusziTypesziJSString_a8VRX:($1)=>{$1 = __asterius_jsffi.getJSValzh($1);return __asterius_jsffi.newJSValzh($1[0]);},__asterius_jsffi_basezuAsteriusziTypesziJSString_a8VS6:($1,$2)=>{$1 = __asterius_jsffi.getJSValzh($1);return ($1[0] += String.fromCodePoint($2));},__asterius_jsffi_basezuAsteriusziTypesziJSString_a8VSb:()=>{return __asterius_jsffi.newJSValzh(['']);},__asterius_jsffi_basezuAsteriusziTypesziJSString_a8VSi:($1)=>{$1 = __asterius_jsffi.getJSValzh($1);return ((() => { const r = $1.next(); return r.done ? 0 : (1 + r.value.codePointAt(0)); })());},__asterius_jsffi_basezuAsteriusziTypesziJSString_a8VSq:($1)=>{$1 = __asterius_jsffi.getJSValzh($1);return __asterius_jsffi.newJSValzh($1[Symbol.iterator]());},__asterius_jsffi_basezuAsteriusziTypesziJSString_a8VSD:($1)=>{$1 = __asterius_jsffi.getJSValzh($1);return ($1.length);},__asterius_jsffi_basezuAsteriusziTypesziJSVal_a8U2a:($1)=>{return (__asterius_jsffi.freeJSValzh($1));},__asterius_jsffi_async_mainzuMain_ajch:($1)=>__asterius_jsffi.returnFFIPromise((async () => {$1 = __asterius_jsffi.getJSValzh($1);return [1, await (requestMessage($1))];})()),__asterius_jsffi_mainzuMain_ajqL:($1)=>{$1 = __asterius_jsffi.getJSValzh($1);return (sendMessage($1));}}}), exportsStaticOffsets: [["main",0x0016bb10,0x0000000000000000,0x0000000000000000,true]], functionsOffsetTable: Object.freeze({}), staticsOffsetTable: Object.freeze({"MainCapability":0x0,"base_AsteriusziTypesziJSException_mkJSException_closure":0x15b8d8,"stg_IND_info":0x162c08,"stg_WHITEHOLE_info":0x162b08,"stg_raise_ret_info":0x1629d8,"base_AsteriusziTopHandler_runIO_closure":0x156038,"base_AsteriusziTopHandler_runNonIO_closure":0x156098,"stg_JSVAL_info":0x15eea0,"stg_raise_info":0x1629f0,"stg_STABLE_NAME_info":0x163450}), sptOffsetEntries: new Map([]), tableSlots: 41289, staticBytes: 1489944, yolo: false, pic: false, defaultTableBase: 0x400, defaultMemoryBase: 0x400, consoleHistory: false, gcThreshold: 0x40, targetSpecificModule: targetSpecificModule};