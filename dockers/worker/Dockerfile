################### Use Vampire
FROM vampire-base AS builder
USER root

################### Extract Vampire in run stage
FROM satcomp-base:worker AS vampire_liaison

#  Install required softwares
USER root
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt install -y jq 

WORKDIR /
# Copy vampire
COPY --from=builder /home/vampire/build/bin/vampire /competition
COPY --chown=ecs-user /worker /competition
COPY --chown=ecs-user /updater /competition
COPY --chown=ecs-user /worker_vampire.sh /competition
USER ecs-user
RUN chmod +x /competition/worker
RUN chmod +x /competition/worker_vampire.sh
