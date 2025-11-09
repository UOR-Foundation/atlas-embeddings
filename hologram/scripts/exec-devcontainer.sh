#!/bin/bash

CONTAINER_ID=$(docker container ls --filter "ancestor=hologramapp_devcontainer-app" --format '{{.ID}}')    
if [ -z "$CONTAINER_ID" ]; then
    echo "No container found"
    exit 1
fi
docker exec -it $CONTAINER_ID /bin/zsh