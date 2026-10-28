pkgs: refinedrust:

pkgs.dockerTools.buildLayeredImage {
  name = "refinedrust-ci";
  tag = "latest";

  contents = [
    refinedrust
    pkgs.bash
    pkgs.coreutils
    pkgs.findutils
    pkgs.gitMinimal
    pkgs.gnumake
    pkgs.gnugrep
    pkgs.gnused
    pkgs.gnutar
    pkgs.gzip
    pkgs.dockerTools.caCertificates
    pkgs.dockerTools.usrBinEnv
  ];

  config = {
    Cmd = [ "/bin/bash" ];
    Env = [
      "PATH=/bin"
      "HOME=/root"
      "USER=root"
      "SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt"
      "GIT_SSL_CAINFO=/etc/ssl/certs/ca-certificates.crt"
    ];
  };
}
