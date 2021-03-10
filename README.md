# Gc-Immutable-Collections

Immutable collections which manage memory via [Gc](https://docs.rs/gc/0.3.6/gc/struct.Gc.html) pointers, thus allowing collections to cyclically include each other without leaking memory.




# Magma Wire Protocol

Assumes a reliable, ordered byte channel between two nodes. One node is the *client*, the other is the *server*.




Client messages:

- GrantCredit(u64)
- PleaseDropCredit(u64)
- CreditLimit(u64)
- Request(Request)
- Cancel(RequestId)
- IDropCredit(u64)

Server messages:

- GrantCredit(u64)
- PleaseDropCredit(u64)
- CreditLimit(u64)
- SetActiveRequest(RequestId)
- Response(Stuff)
- ConfirmCancel(RequestId)
- IDropCredit(u64)
