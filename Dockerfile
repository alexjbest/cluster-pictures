FROM sagemath/sagemath:10.2

ARG NB_USER=jovyan
ARG NB_UID=1000

USER root

# Make sure the contents of our repo are in ${HOME}
COPY . ${HOME}
RUN chown -R ${NB_UID} ${HOME}
USER sage
    
RUN sage -pip install -e .
RUN python3 -m pip install --no-cache-dir notebook jupyterlab
