{ stdlib, dpdgraph, version ? null }:
(dpdgraph.override { inherit version; }).overrideAttrs (o: {
  buildInputs = o.buildInputs ++ [ stdlib ];

  postBuild = ''
    make test-suite
  '';
})
