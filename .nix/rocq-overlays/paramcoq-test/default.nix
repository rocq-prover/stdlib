{ stdlib, paramcoq, version ? null }:
(paramcoq.override { inherit version; }).overrideAttrs (o: {
  buildInputs = o.buildInputs ++ [ stdlib ];

  postBuild = ''
    make -C test-suite examples
  '';
})
