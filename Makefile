build:
	wasm32-wasi-cabal update
	wasm32-wasi-cabal build --minimize-conflict-set --allow-newer=base --allow-newer=deepseq --allow-newer=template-haskell  --allow-newer=aeson --allow-newer=pretty --allow-newer=vector --allow-newer=vector-stream  --allow-newer=ghc-prim
