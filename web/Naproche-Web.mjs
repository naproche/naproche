import * as rts from "./rts.mjs";
import module from "./Naproche-Web.wasm.mjs";
import req from "./Naproche-Web.req.mjs";

var sendMessage = function(msg) {
  console.log(msg);
};
var requestMessage = function(msg) {
  console.log(msg);
};

module.then(m => rts.newAsteriusInstance(Object.assign(req, {module: m}))).then(i => {
  console.log(i);
  i.exports.main().catch(err => {if (!(err.startsWith('ExitSuccess') || err.startsWith('ExitFailure '))) i.fs.writeNonMemory(2, `Naproche-Web: ${err}
`)});
});
