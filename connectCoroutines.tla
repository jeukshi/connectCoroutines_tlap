------------------------- MODULE connectCoroutines -------------------------
EXTENDS TLC, Sequences

VARIABLE t1
       , t2
       , t1mvar
       , t2mvar
       \* `ioRef` represents `State` effect in scope of both coroutines.
       , ioRef
       
-----------------------------------------------------------------------------
vars == << t1, t2, t1mvar, t2mvar, ioRef >>

ThreadStates == 
  { "Init" \* GHC runtime
  , "Run" \* Eff monad
  , "Get" \* Eff monad
  , "Put" \* Eff monad
  , "Pure" \* Eff monad / `connectCoroutines` internals
  , "Yield" \* Eff monad / `connectCoroutines` internals
  , "Await" \* Eff monad / `connectCoroutines` internals
  }

\* We don't care what data coroutines exchange.
MVarStates == { "Full", "Empty" }

IORefStates == { "t1", "t2" }

TypeOk ==
  /\ t1 \in ThreadStates
  /\ t2 \in ThreadStates
  /\ t1mvar \in MVarStates
  /\ t2mvar \in MVarStates
  /\ ioRef \in IORefStates
  
Init == 
  /\ t1 = "Init"
  /\ t2 = "Init"
  /\ t1mvar = "Empty"
  /\ t2mvar = "Empty"
  /\ ioRef = "t1"

T1Init ==
  /\ t1 = "Init"
  /\ t1' = "Run"
  /\ UNCHANGED << t2, t1mvar, t2mvar, ioRef >>

T2Init ==
  /\ t2 = "Init"
  /\ t2' = "Await"
  /\ UNCHANGED << t1, t1mvar, t2mvar, ioRef >>

T1Get ==
  /\ t1 \in { "Run", "Get", "Put" }
  /\ t1' = "Get"
  /\ UNCHANGED << t2, t1mvar, t2mvar, ioRef >>

T2Get ==
  /\ t2 \in { "Run", "Get", "Put" }
  /\ t2' = "Get"
  /\ UNCHANGED << t1, t1mvar, t2mvar, ioRef >>

T1Put ==
  /\ t1 \in { "Run", "Get", "Put" }
  /\ t1' = "Put"
  /\ ioRef' = "t1"
  /\ UNCHANGED << t2, t1mvar, t2mvar >>
  
T2Put ==
  /\ t2 \in { "Run", "Get", "Put" }
  /\ t2' = "Put"
  /\ ioRef' = "t2"
  /\ UNCHANGED << t1, t1mvar, t2mvar >>

T1Pure ==
  /\ t1 \in { "Run", "Get", "Put" }
  /\ t1' = "Pure"
  \* We modify `ioRef`, just to make sure that no further modifications
  \* are allowed by the model *after* the coroutine ends..
  /\ ioRef' = "t1"
  /\ UNCHANGED << t2, t1mvar, t2mvar >>
  
T2Pure ==
  /\ t2 \in { "Run", "Get", "Put" }
  /\ t2' = "Pure"
  /\ ioRef' = "t2"
  /\ UNCHANGED << t1, t1mvar, t2mvar >>
  
T1Yield ==
  /\ t1 \in { "Run", "Get", "Put" }
  /\ t1' = "Yield"
  /\ UNCHANGED << t2, t1mvar, t2mvar, ioRef >>
 
T2Yield ==
  /\ t2 \in { "Run", "Get", "Put" }
  /\ t2' = "Yield"
  /\ UNCHANGED << t1, t1mvar, t2mvar, ioRef >>

T1YieldSuccess ==
  /\ t1 = "Yield"
  /\ t1mvar = "Empty"
  /\ t1' = "Await"
  /\ t1mvar' = "Full"
  /\ UNCHANGED << t2, t2mvar, ioRef >>

T2YieldSuccess ==
  /\ t2 = "Yield"
  /\ t2mvar = "Empty"
  /\ t2' = "Await"
  /\ t2mvar' = "Full"
  /\ UNCHANGED << t1, t1mvar, ioRef >>
  
T1AwaitSuccess ==
  /\ t1 = "Await"
  /\ t2mvar = "Full"
  /\ t1' = "Run"
  /\ t2mvar' = "Empty"
  /\ UNCHANGED << t2, t1mvar, ioRef >>

T2AwaitSuccess ==
  /\ t2 = "Await"
  /\ t1mvar = "Full"
  /\ t2' = "Run"
  /\ t1mvar' = "Empty"
  /\ UNCHANGED << t1, t2mvar, ioRef >>

Next ==
  \/ T1Init
  \/ T2Init
  \/ T1Get
  \/ T2Get
  \/ T1Put
  \/ T2Put
  \/ T1Pure
  \/ T2Pure
  \/ T1Yield
  \/ T2Yield
  \/ T1YieldSuccess
  \/ T2YieldSuccess
  \/ T1AwaitSuccess
  \/ T2AwaitSuccess
  \* `connectCoroutines` is done, but the world goes on...
  \/ ((t1 = "Pure" \/ t2 = "Pure") /\ UNCHANGED vars)

Fairness ==
  \* This is based on the assumption that GHC runtime will eventually start
  \* our threads and wake our threads for `MVar` operations.
  \* It's a fair assumption.
  /\ WF_t1(T1Init)
  /\ WF_t2(T2Init)
  /\ WF_t1(T1YieldSuccess)
  /\ WF_t2(T2YieldSuccess)
  /\ WF_t1(T1AwaitSuccess)
  /\ WF_t2(T2AwaitSuccess)
  \* There is no reason to demand that our coroutines terminate, but it makes 
  \* our `Liveness` condition simpler. Terminating coroutines are also just more 
  \* interesting, as they modify `ioRef` state.
  \* It's a strong fairness, because `TxPure` action is not enabled continuously.
  /\ SF_t1(T1Pure)
  /\ SF_t2(T2Pure)
 
Spec == Init /\ [][Next]_<<vars>> /\ Fairness

Liveness ==
  \/ <>[](t1 = "Pure" /\ ioRef = "t1")
  \/ <>[](t2 = "Pure" /\ ioRef = "t2")

\* Allowed state transitions.
ModelOk ==
  /\ [][t1 = "Init" => t1' = "Run"]_t1
  /\ [][t2 = "Init" => t2' = "Await"]_t2
  /\ [][(t1 \in {"Run", "Get", "Put"}) => (t1' \in {"Run", "Get", "Put", "Pure", "Yield"})]_t1
  /\ [][(t2 \in {"Run", "Get", "Put"}) => (t2' \in {"Run", "Get", "Put", "Pure", "Yield"})]_t2
  /\ [][t1 = "Yield" => t1' = "Await"]_t1
  /\ [][t2 = "Yield" => t2' = "Await"]_t2  
  /\ [][t1 = "Await" => t1' = "Run"]_t1
  /\ [][t2 = "Await" => t2' = "Run"]_t2
  /\ [][t1 /= t1' => t1' /= "Init"]_t1  
  /\ [][t2 /= t2' => t2' /= "Init"]_t2
  
\* put s x
\* y <- get s
\* x == y
RaceFree ==
  /\ [][(t1 = "Put" /\ t1' = "Get") => ioRef' = "t1"]_<<t1, ioRef>>
  /\ [][(t2 = "Put" /\ t2' = "Get") => ioRef' = "t2"]_<<t2, ioRef>>

\* There is some concurrency here since we are launching threads,
\* but after `Init`, it is no longer the case. Whenever `t1` changes, it's
\* state, `t2` can only be `Await` and vice versa. Our condition is based on
\* `t2` state, since its initial execution is trivial, it can only `Await`,
\* while `t1` can start computations immediately.
AlmostConcurrentFree ==
  /\ [][(t1 /= t1' /\ t2 /= "Init") => (t2 = "Await" /\ t2' = "Await")]_<<t1,t2>>
  /\ [][(t2 /= t2' /\ t2 /= "Init") => (t1 = "Await" /\ t1' = "Await")]_<<t1,t2>>
  
=============================================================================
