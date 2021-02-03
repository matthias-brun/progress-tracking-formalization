This repository contains an Isabelle formalization of [Timely
Dataflow](https://github.com/timelydataflow/timely-dataflow)'s progress tracking
protocol presented in the paper draft

Verified Progress Tracking for Timely Dataflow
  
by Matthias Brun, Sára Decova, Andrea Lattuada, and Dmitriy Traytel. The repository also
contains the extended version of the paper that provides proof sketches for the safety
properties and additional details on the formalization (`rep.pdf`).

The formalization has been processed with Isabelle2020 which is available here:

[http://isabelle.in.tum.de/website-Isabelle2020](http://isabelle.in.tum.de/website-Isabelle2020)

The Isabelle theories are in the directory `thys` and correspond to the paper in
the following way:

* `Exchange_Abadi.thy` contains the protocol described in section 3
* `Exchange.thy` contains the protocol described in section 4
* `Propagate.thy` contains the algorithm described in section 5
* `Combined.thy` contains the protocol described in section 6
* The other theories contain various auxiliary constructs and lemmas

The Isabelle theories rely on an existing Archive of Formal Proofs (AFP) installation. To process them, Isabelle must be invoked as follows:

```isabelle jedit -d '<path/to/afp-2020>/thys' -d 'thys'```

where the first path points to the thys directory in the AFP installation and the second points to the thys directory of this repository.

The formalization can also be browsed without a running Isabelle instance in the
html format (`Progress_Tracking/index.html`).
