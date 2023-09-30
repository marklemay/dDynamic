build:
	cabal update
	wasm32-wasi-cabal build --minimize-conflict-set --allow-newer=base --allow-newer=deepseq --allow-newer=template-haskell --allow-newer=pretty