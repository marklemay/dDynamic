build:
	wasm32-wasi-cabal update
	wasm32-wasi-cabal build --minimize-conflict-set --allow-newer=base --allow-newer=deepseq --allow-newer=template-haskell --allow-newer=pretty --allow-newer=vector --allow-newer=vector-stream  --allow-newer=ghc-prim -optl-Wl,--export=hs_init,--export=num,--export=numNum,--export=numNum,--export=astr,--export=doublestr
