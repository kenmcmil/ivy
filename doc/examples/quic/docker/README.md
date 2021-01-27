The script `run.sh` will build a Docker image, create a container, and run the specified test.
For example, `run.sh -s picoquic -t quic_server_test_stream` runs the test from file `quic_server_test_stream.ivy` against the picoquic server. The test results are copied to the `results` directory.
