################
FROM ubuntu:16.04 AS vampire_base
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt install -y openssh-server iproute2 openmpi-bin openmpi-common iputils-ping \
    && mkdir /var/run/sshd \
    && sed 's@session\s*required\s*pam_loginuid.so@session optional pam_loginuid.so@g' -i /etc/pam.d/sshd \
    && setcap CAP_NET_BIND_SERVICE=+eip /usr/sbin/sshd \
    && useradd -ms /bin/bash vampire \
    && chown -R vampire /etc/ssh/ \
    && su - vampire -c \
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
    && DEBIAN_FRONTEND=noninteractive apt install -y apt-utils make cmake \
     build-essential libgmp-dev libedit-dev libsqlite3-dev bison flex libubsan0 \
     zlib1g-dev libopenmpi-dev git python3 awscli mpi

RUN git clone https://github.com/vprover/vampire
WORKDIR /vampire
RUN git submodule update --init z3
WORKDIR /vampire/z3/build
RUN cmake .. -DZ3_SINGLE_THREADED=ON
RUN make -j2
WORKDIR /vampire/build
RUN cmake ..
RUN make -j2
RUN mv bin/vampire_z3_rel_* ../vampire

WORKDIR /vampire/aws
chmod 755 run.sh
chmod 755 run_vampire.sh
chmod 755 make_combined_hostfile.py
chmod 777 .
WORKDIR  /vampire
chmod 777 .
USER vampire
CMD ["/usr/sbin/sshd", "-D", "-f", "/home/.ssh/sshd_config"]
CMD vampire/aws/run.sh
