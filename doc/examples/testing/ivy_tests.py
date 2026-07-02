# Regression tests for the files in this directory. See run_expects.py.

tests = [
    # ivy_check
    {'type': 'check', 'name': 'pingpong', 'args': ['trusted=true'], 'expect': 'OK'},
    {'type': 'check', 'name': 'interference', 'args': ['trusted=true'],
     'expect': 'error: Call out to right_player.intf_ping'},
    {'type': 'check', 'name': 'coveragefail', 'args': ['trusted=true'],
     'expect': 'error: assertion is not checked'},

    # specification-based test generation (ivy_to_cpp target=test)
    {'type': 'test', 'name': 'trivnet', 'expect': 'test_completed'},
    {'type': 'test', 'name': 'pingpong', 'args': ['isolate=iso_l'],
     'expect': 'test_completed'},
    {'type': 'test', 'name': 'pingpong_bad', 'args': ['isolate=iso_l'],
     'expect': 'assertion failed'},
    {'type': 'test', 'name': 'pingpong', 'args': ['isolate=iso_r'],
     'expect': 'test_completed'},
    {'type': 'test', 'name': 'leader_election_ring', 'args': ['isolate=iso_p'],
     'expect': 'test_completed'},
    {'type': 'test', 'name': 'leader_election_ring', 'args': ['isolate=iso_n'],
     'expect': 'test_completed'},
    {'type': 'test', 'name': 'leader_election_ring',
     'args': ['isolate=iso_t test_iters=5'], 'expect': 'test_completed'},
    {'type': 'test', 'name': 'token_ring', 'args': ['isolate=iso_p'],
     'expect': 'test_completed'},
    {'type': 'test', 'name': 'token_ring', 'args': ['isolate=iso_t'],
     'expect': 'test_completed'},
    {'type': 'test', 'name': 'token_ring_buggy',
     'args': ['isolate=iso_t test_runs=10'], 'expect': 'assertion failed'},
    {'type': 'test', 'name': 'token_ring', 'args': ['isolate=iso_n'],
     'expect': 'test_completed'},
    {'type': 'test', 'name': 'token_ring', 'args': ['isolate=iso_pt'],
     'expect': 'test_completed'},
]
