#!/bin/zsh
docker run -it \
    --mount type=bind,source="$(pwd)"/workspace,target=/workspace \
    fstar_magda

