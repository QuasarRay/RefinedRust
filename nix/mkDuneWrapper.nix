pkgs: drvs:

let
  fetchRocqDeps =
    drv:
    pkgs.lib.lists.unique ([ drv ] ++ pkgs.lib.flatten (map fetchRocqDeps drv.propagatedBuildInputs));
in
pkgs.symlinkJoin {
  name = "dune-wrapper";
  paths = [
    pkgs.rocqPackages.rocq-core
  ]
  ++ pkgs.rocqPackages.rocq-core.nativeBuildInputs
  ++ pkgs.lib.flatten (map fetchRocqDeps drvs);

  nativeBuildInputs = [ pkgs.makeWrapper ];
  postBuild = ''
    wrapProgram $out/bin/dune \
      --set OCAMLPATH $out/lib/ocaml/${pkgs.rocqPackages.rocq-core.ocamlPackages.ocaml.version}/site-lib \
      --set ROCQPATH $out/lib/coq/${pkgs.rocqPackages.rocq-core.rocq-version}/user-contrib
  '';
}
