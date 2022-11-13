# DistSysNaive

## Running a single node from IEX


## Running as a release

Build a release and start 3 instances of it:
```
mix release
env RELEASE_NAME=aaa DSN_PORT=9000 _build/dev/rel/dss/bin/dss daemon
env RELEASE_NAME=bbb DSN_PORT=9001 _build/dev/rel/dss/bin/dss daemon
env RELEASE_NAME=ccc DSN_PORT=9002 _build/dev/rel/dss/bin/dss daemon
```

Connect the cluster (adjust the host names to your environment):
```
env RELEASE_NAME=ccc DSN_PORT=9002 _build/dev/rel/dss/bin/dss rpc 'Node.ping(:"aaa@karolis-2020")'
env RELEASE_NAME=ccc DSN_PORT=9002 _build/dev/rel/dss/bin/dss rpc 'Node.ping(:"bbb@karolis-2020")'
```

Use the cluster via REST API:
```
curl http://localhost:9000/ && echo
curl -X PUT http://localhost:9001/ -H 'Content-Type: application/json' -d '{"answer":"great"}' && echo
curl http://localhost:9000/ && echo
```

Stop the cluster:
```
env RELEASE_NAME=aaa DSN_PORT=9000 _build/dev/rel/dss/bin/dss stop
env RELEASE_NAME=bbb DSN_PORT=9001 _build/dev/rel/dss/bin/dss stop
env RELEASE_NAME=ccc DSN_PORT=9002 _build/dev/rel/dss/bin/dss stop
```
