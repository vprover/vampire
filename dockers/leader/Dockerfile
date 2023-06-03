################### Use Vampire 
FROM vampire:common AS builder
USER root


################### Extract Vampire in run stage
FROM satcomp-infrastructure:leader AS vampire_liaison
WORKDIR /
# Copy vampire and solver scripts
COPY --from=builder /home/vampire/build/bin/vampire /competition 
COPY --chown=ecs-user /run_vampire_parallel.sh /competition
COPY --chown=ecs-user /run_vampire_cloud.sh /competition
COPY --chown=ecs-user /solver /competition
USER ecs-user
RUN chmod +x /competition/run_vampire_parallel.sh
RUN chmod +x /competition/run_vampire_cloud.sh
RUN chmod +x /competition/solver
