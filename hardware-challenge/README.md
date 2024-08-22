# Hardware Task: Arbiter Circuit

## Info
An arbiter circuit controls access to some kind of resource. In this case, there are 3 requesting device. Each device makes its request by setting a signal `r[i] = 1`. When 1+ requests occur, the FSM decides which device receives a grant to use the resource and changes to a state whihc sets that device's `g[i]` signal to 1. Devices continue to hold the resource until they set their request bit low.

This circuit has a priority system: device 1 has highest priority, and device 3 has lowest priority. I.e., device 3 will only receive the grant if it is the only device making the request.

## Compiling
TBA
