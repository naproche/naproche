# Web component of Naproche

This is the [asterius](https://github.com/tweag/asterius/) interface of Naproche.
It is currently ~3x slower than GHCJS and therefore unused but since asterius is
actively maintained and GHCJS isn't I've decided to keep it in. To build this
you need to modify the steps of the official documentation somewhat because
you need to add the `sendMessage` and `requestMessage` functions to the RTS.
Thus, you need to change auto-generated the `.req.mjs` file to the one in this folder
and then run bundling manually. At the time of this writing the correct shell commands are:

```
$ podman run -it --rm -v $(pwd):/workspace -w /workspace terrorjack/asterius
# ahc-cabal new-install Naproche-Web --installdir . --overwrite-policy=always
# ahc-dist --input-exe Naproche-Web --browser --output-directory build
# cd build
# cp ../web/Naproche-Web.req.mjs .
# npx webpack --mode production --entry ./Naproche-Web.mjs --output-path . --output-filename Naproche-Web.js
# exit
```

You can then copy the `Naproche-Web.wasm` and `Naproche-Web.js` files into the public folder of the webinterface
and run the latter as a Webworker.