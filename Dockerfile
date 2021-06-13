################
FROM ubuntu:16.04 AS vampire_base
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt install -y openssh-server iproute2 openmpi-bin openmpi-common iputils-ping \
    && mkdir /var/run/sshd \
    && sed 's@session\s*required\s*pam_loginuid.so@session optional pam_loginuid.so@g' -i /etc/pam.d/sshd \
    && setcap CAP_NET_BIND_SERVICE=+eip /usr/sbin/sshd \
    && useradd -ms /bin/bash dracula \
    && chown -R dracula /etc/ssh/ \
    && su - dracula -c \
        'ssh-keygen -q -t rsa -f ~/.ssh/id_rsa -N "" \
        && cp ~/.ssh/id_rsa.pub ~/.ssh/authorized_keys \
        && cp /etc/ssh/sshd_config ~/.ssh/sshd_config \
        && sed -i "s/UsePrivilegeSeparation yes/UsePrivilegeSeparation no/g" ~/.ssh/sshd_config \
        && printf "Host *\n\tStrictHostKeyChecking no\n" >> ~/.ssh/config'
WORKDIR /home
ENV NOTVISIBLE "in users profile"
RUN echo "export VISIBLE=now" >> /etc/profile
EXPOSE 22

################ 
FROM vampire_base  AS builder 
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt install -y apt-utils make  \
     build-essential libgmp-dev libedit-dev libsqlite3-dev bison flex libubsan0 \
     zlib1g-dev libopenmpi-dev git python3 awscli mpi

RUN wget https://cmake.org/files/v3.9/cmake-3.9.1-Linux-x86_64.tar.gz
RUN tar zxvf cmake-3.9.1-Linux-x86_64.tar.gz
RUN mv cmake-3.9.1-Linux-x86_64 /opt/cmake-3.9.1
RUN ln -sf /opt/cmake-3.9.1/bin/*  /usr/bin/ 

RUN git clone https://github.com/vprover/vampire
WORKDIR /home/vampire
RUN git submodule update --init z3
WORKDIR /home/vampire/z3/build
RUN cmake .. -DZ3_SINGLE_THREADED=ON
RUN make -j2
WORKDIR /home/vampire/build
RUN cmake ..
RUN make -j2
RUN mv bin/vampire_z3_rel_* bin/vampire

WORKDIR /home/vampire/aws
RUN chmod 755 run.sh
RUN chmod 755 run_vampire.sh
RUN chmod 755 make_combined_hostfile.py
RUN chmod 777 .
WORKDIR /home/vampire
RUN chmod 777 .
WORKDIR /home
USER dracula 
CMD ["/usr/sbin/sshd", "-D", "-f", "/home/.ssh/sshd_config"]
CMD vampire/aws/run.sh
