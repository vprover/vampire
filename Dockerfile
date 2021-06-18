################
FROM ubuntu:20.04
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt install -y openssh-server iproute2 iputils-ping git cmake make g++ python3-distutils python3 awscli \
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

RUN git clone https://github.com/vprover/vampire --branch smtcomp21 --single-branch
WORKDIR /home/vampire
RUN git submodule update --init z3
WORKDIR /home/vampire/z3/build
RUN cmake .. -DZ3_SINGLE_THREADED=ON
RUN make -j2
WORKDIR /home/vampire/build
RUN cmake ..
RUN make -j2
RUN mv bin/vampire_z3_rel_* bin/vampire

WORKDIR /home
RUN chmod 777 . && chmod 777 vampire && chmod 777 vampire/aws && chmod 755 vampire/aws/run* && chmod 755 vampire/aws/make_combined_hostfile.py
USER dracula 
CMD ["/usr/sbin/sshd", "-D", "-f", "/home/.ssh/sshd_config"]
CMD vampire/aws/run_parallel.sh
