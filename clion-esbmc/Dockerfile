# CLion remote docker environment (How to build docker container, run and stop it)
#
# Build and run:
#   docker build -t clion/remote-cpp-env:0.5 -f Dockerfile.remote-cpp-env .
#   docker run -d --cap-add sys_ptrace -p127.0.0.1:2222:22 --name clion_remote_env clion/remote-cpp-env:0.5
#   ssh-keygen -f "$HOME/.ssh/known_hosts" -R "[localhost]:2222"
#
# stop:
#   docker stop clion_remote_env
# 
# ssh credentials (test user):
#   user@password 

FROM ubuntu:18.04

RUN apt-get update \
  && apt-get install -y ssh \
      build-essential \
      gcc \
      g++ \
      gdb \
      clang \
      cmake \
      rsync \
      tar \
      python \
      git \
      gperf \
      libgmp-dev \
      bison \
      curl \
      flex \
      gcc-multilib \
      linux-libc-dev \
      libboost-all-dev \
      libtinfo-dev \
      ninja-build \
      python3-setuptools \
      unzip \
      wget \
  && apt-get clean

WORKDIR /deps
RUN wget https://github.com/llvm/llvm-project/releases/download/llvmorg-11.0.0/clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04.tar.xz \
  && tar xf clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04.tar.xz \
  && mv clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04 clang11 \
  && rm clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04.tar.xz

RUN git clone --depth=1 --branch=3.2.1 https://github.com/boolector/boolector && cd boolector && ./contrib/setup-lingeling.sh && ./contrib/setup-btor2tools.sh && ./configure.sh --prefix $PWD/../boolector-release && cd build && make -j9 && make install

RUN ( \
    echo 'LogLevel DEBUG2'; \
    echo 'PermitRootLogin yes'; \
    echo 'PasswordAuthentication yes'; \
    echo 'Subsystem sftp /usr/lib/openssh/sftp-server'; \
  ) > /etc/ssh/sshd_config_test_clion \
  && mkdir /run/sshd

RUN useradd -m user \
  && yes password | passwd user

CMD ["/usr/sbin/sshd", "-D", "-e", "-f", "/etc/ssh/sshd_config_test_clion"]
