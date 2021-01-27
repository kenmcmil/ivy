# we need python2 support, which was dropped after buster:
FROM debian:buster

RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update
RUN apt-get install -y apt-utils

# Install and configure locale `en_US.UTF-8`
RUN apt-get install -y locales && \
    sed -i -e "s/# $en_US.*/en_US.UTF-8 UTF-8/" /etc/locale.gen && \
    dpkg-reconfigure --frontend=noninteractive locales && \
    update-locale LANG=en_US.UTF-8
ENV LANG=en_US.UTF-8

RUN apt-get update
RUN apt-get install -y git python2 python-pip g++ cmake python-ply git python-tk tix pkg-config libssl-dev sudo python-setuptools vim zsh tmux

# create a user:
RUN useradd -ms /bin/bash user && echo 'user:user' | chpasswd && adduser user sudo
RUN echo "ALL ALL=(ALL) NOPASSWD: ALL" >> /etc/sudoers
USER user
WORKDIR /home/user

# install Ivy:
RUN git clone --recurse-submodules https://github.com/kenmcmil/ivy.git
WORKDIR /home/user/ivy/
RUN git checkout quic23
RUN python build_submodules.py # takes a while (builds z3...)
RUN mkdir -p "/home/user/python/lib/python2.7/site-packages"
ENV PYTHONPATH="/home/user/python/lib/python2.7/site-packages"
RUN python2.7 setup.py develop --prefix="/home/user/python/"
ENV PATH=$PATH:"/home/user/python/bin/"

RUN pip install pexpect chardet # additional dependencies of Ivy's test feature
RUN mkdir -p /home/user/ivy/doc/examples/quic/test/temp
RUN mkdir /home/user/ivy/doc/examples/quic/build

# build quant:
WORKDIR /home/user/
RUN git clone https://github.com/NTAP/quant.git
RUN sudo apt-get install -y libssl-dev libhttp-parser-dev libbsd-dev pkgconf
RUN sudo apt-get install -y aptitude
WORKDIR /home/user/quant
# checkout the implementation of version 23 of the spec:
RUN git checkout 23
RUN git submodule update --init --recursive
RUN mkdir Debug
WORKDIR /home/user/quant/Debug
RUN cmake .. && make

# build picotls
WORKDIR /home/user/
RUN git clone https://github.com/h2o/picotls.git
WORKDIR /home/user/picotls
RUN git checkout 549bc7c4321f7cfd426c32c375c17240b9b1258f
RUN git submodule init
RUN git submodule update
RUN cmake .
RUN make
#RUN make check

# build picoquic
WORKDIR /home/user/
RUN git clone https://github.com/private-octopus/picoquic.git
WORKDIR /home/user/picoquic
RUN git checkout 4c061c0b24e35282108d8c57eef41939a692a6c4
RUN cmake .
RUN make

# tell Ivy where the quic implementations are:
ENV QUIC_IMPL_DIR=/home/user/

COPY resources/run-test.sh /home/user/ivy/doc/examples/quic
WORKDIR /home/user/ivy/doc/examples/quic/
