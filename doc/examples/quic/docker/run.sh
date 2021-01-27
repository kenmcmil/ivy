#!/bin/bash

IMAGE_NAME=galoisinc/quicmbt
IMAGE_TAG=latest

docker build -t ${IMAGE_NAME}:${IMAGE_TAG} .

TEST_NAME=quic_server_test_stream
SERVER=picoquic #quant is also an option

while getopts ":s:t:" opt; do
    case ${opt} in
        t )
            TEST_NAME=$OPTARG
            ;;
        s )
            SERVER=$OPTARG
            ;;
        * )
            show_error_and_exit "Unknown argument: " $OPTARG
            ;;
    esac
done

echo "RUNNING TEST: ${TEST_NAME}"

docker run -it --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" -v ${PWD}/results:/results -e DISPLAY=$DISPLAY ${IMAGE_NAME}:${IMAGE_TAG} ./run-test.sh ${TEST_NAME} ${SERVER} 
