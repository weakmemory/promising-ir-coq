{
  format = "1.0.0";

  attribute = "promising-ir";

  default-bundle = "8.18";

  bundles."8.15" = {
    push-branches = [ "**" ];
    coqPackages.coq.override.version = "8.15";
    coqPackages.hahn.override.version = "master";
    coqPackages.hahnExt.override.version = "main";
    coqPackages.sflib.override.version = "master";
    coqPackages.promising-lib.override.version = "master";
    coqPackages.ITree.override.version = "master";
  };
  bundles."8.16" = {
    push-branches = [ "**" ];
    coqPackages.coq.override.version = "8.16";
    coqPackages.hahn.override.version = "master";
    coqPackages.hahnExt.override.version = "main";
    coqPackages.sflib.override.version = "master";
    coqPackages.promising-lib.override.version = "master";
    coqPackages.ITree.override.version = "master";
  };
  bundles."8.17" = {
    push-branches = [ "**" ];
    coqPackages.coq.override.version = "8.17";
    coqPackages.hahn.override.version = "master";
    coqPackages.hahnExt.override.version = "main";
    coqPackages.sflib.override.version = "master";
    coqPackages.promising-lib.override.version = "master";
    coqPackages.ITree.override.version = "master";
  };
  bundles."8.18" = {
    push-branches = [ "**" ];
    coqPackages.coq.override.version = "8.18";
    coqPackages.hahn.override.version = "master";
    coqPackages.hahnExt.override.version = "main";
    coqPackages.sflib.override.version = "master";
    coqPackages.promising-lib.override.version = "master";
    coqPackages.ITree.override.version = "master";
  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  
  cachix.weakmemory.authToken = "CACHIX_AUTH_TOKEN";
}
