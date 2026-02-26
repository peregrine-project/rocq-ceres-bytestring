{
  ## DO NOT CHANGE THIS
  format = "1.0.0";

  attribute = "ceres-bs";
  no-rocq-yet = true;

  default-bundle = "9.0";

  bundles."9.0" = { coqPackages = {
      coq.override.version = "9.0";
      metarocq.job = false;
      metarocq.override.version = "1.4-9.0.1";
    }; rocqPackages = {
      rocq-core.override.version = "9.0";
    };
  };
  bundles."9.1" = { coqPackages = {
      coq.override.version = "9.1";
      metarocq.job = false;
      metarocq.override.version = "1.4.1-9.1";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
    };
  };

  bundles."9.0".push-branches = ["master"];
  bundles."9.1".push-branches = ["master"];

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metarocq = {};
  cachix.peregrine = {};
}
