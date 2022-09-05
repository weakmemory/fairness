This code contains Coq proofs supplementing the _Making Weak Memory Models Fair_ paper.
More on the artifact constructed from the code (including a VM image and installation guidelines) are stated in [ARTIFACT.md](ARTIFACT.md).

### Project dependencies
* [Coq 8.15.1](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn) (`coq-hahn`). This library provides useful definitions and proofs of various relations and sets properties, as well as a general trace definition used throughout the development.

## List of paper claims and definitions supported by the artifact
	
The overall structure of Coq development in `src` folder is as follows:	

- `basic` folder contains general definitions.
- `equivalence` folder contains proofs of operational and declarative definitions' equivalence placed in corresponding subfolders. The file `equivalence/Equivalence.v` presents these results in a uniform fashion. 
- `lib` folder contains auxiliary proofs and definitions not directly related to memory models. 
- `termination` folder contains proofs of deadlock freedom for three lock implementations.
- `robustness` folder contains the formalization and proof of infinite robustness property. 

### (§2) What is a Fair Operational Semantics?
- To formalize the LTS, the `HahnTrace.LTS` definition from the `hahn` library is used. 
- Both traces and runs of LTS are formalized as `HahnTrace.trace` which is a finite or infinite enumeration of labels of arbitrary type. Note that we often refer both to traces and runs as to "traces" in Coq development because of the implementation type. 
- The definition of event labels (Def. 2.1) is formalized as `Lab` in `src/basic/Labels.v`.
- As the paper notes, we don't specify a program under consideration explicitly but rather assume that its behaviors are expressed using a set of possible traces of LTS. That means that we cannot tell whether a given behavior is thread-fair since there is no sequential program to check if the corresponding thread has terminated. For this reason, we don't formalize Def. 2.8. See a comment for Section 4 for the explanation of why this is valid. 
- We define operational behavior as sets of events corresponding to a run: see `src/equivalence/Equivalence.v`, variable `trace_events`. The notion of being a behavior of a specific program (Prop. 2.10) is instead replaced with the notion of correspondence to a particular trace (`src/equivalence/Equivalence.v`, proposition `op_decl_def_equiv`). 
- For operational definitions of memory models see:
	- For SC (§2) - `src/equivalence/SC.v` (`sc_lts`).
	- For TSO (§2.1) -  `src/equivalence/tso/TSO.v` (`TSO_lts`).
	- For RA (§2.2) -  `src/equivalence/ra/RAop.v` (`ra_lts`).
	- For StrongCOH (§2.3) - `src/equivalence/strong_coh/SCOHop.v` (`scoh_lts`). 
	Note that LTS for RA and StrongCOH are defined for labels that contain data besides thread and event label; this is a purely technical solution that doesn't affect reasoning. 
- Operational memory fairness (Def. 2.12) predicates are specified by the values of a `run_fair` variable in `src/equivalence/Equivalence.v` in memory model-specific theorems (e.g. TSO fairness is formalized by the `TSO_fair` predicate, as specified in the `TSO_equiv` theorem). 
 
### (§3) Preliminaries on Declarative Semantics	
- The definition of graph events (Def. 3.1) is given in `src/basic/Events.v` (`Event` type). 
- Events extracted from a trace (Def. 3.3) are defined by `trace_events` function mentioned above. This set of events also represents the declarative counterpart of the operational notion of behavior in `src/equivalence/Equivalence.v`, proposition `op_decl_def_equiv`. 
- The definition of a well-formed set of events (Def. 3.4) is included in the graph well-formedness predicate (`Wf` in `src/basic/Execution.v`):
    - `Init <= E` condition is formalized in `wf_initE`
	- Requirement for `tid` being defined for non-initializing events is formalized in `wf_tid_init` with `0` used as `⊥`. The second part of the requirement regarding `sn` is not formalized as the definition of `ThreadEvent` (a non-initializing event) explicitly contains the `index` field (formalization of `sn`). 
	- Uniqueness of `tid` and `sn` pairs is specified in the `wf_index`. 	
	- We do not formalize the last condition requiring that a thread's serial numbers are placed densely since it serves merely presentational purposes and doesn't affect Coq development. 
	
  The `Wf` predicate also specifies well-formedness conditions for graph relations. 
- The execution graph definition (Def. 3.5) is given in `src/basic/Execution.v` (`execution` type). Note that there are some differences in notation:

    - The set `E` of graph events is formalized as `acts_set` field of `execution`.
    - The program order (`G.po` in the paper) is formalized as `sb` ("sequenced-before") relation.
    - The modification order (`G.mo` in the paper) is formalized as `co` ("coherence order") field of `execution`.
- As for operational semantics, we do not formalize thread fairness and the notion of being a specific program's behavior (Def. 3.7) explicitly. See a comment for Section 4 for the explanation of why this is valid. 
- For declarative definitions of memory models see:
    - For SC (§3.1) - `src/equivalence/SC.v` (`sc_consistent`).
	- For TSO (§3.2) - `src/equivalence/tso/TSO.v` (`TSO_consistent`).
	- For RA (§3.3) - `src/equivalence/AltDefs.v` (`ra_consistent_alt`).
	- For StrongCOH (§3.4) - `src/equivalence/AltDefs.v` (`scoh_consistent_alt`).

	Note that for RA and StrongCOH throughout the most part of the development we use other definitions - `ra_consistent` in `src/equivalence/ra/RAop.v` and `scoh_consistent` in  `src/equivalence/strong_coh/SCOHop.v` correspondingly. The equivalence between these and their paper counterparts (`..._alt` definitions) is proved in theorems `ra_consistent_defs_equivalence` and `scoh_consistent_defs_equiv` in `src/equivalence/AltDefs.v`.
	
	Also, note that we formalize the irreflexivity of the `G.sc_loc` relation in the `SCpL` predicate. 
	
### (§4) Making Declarative Semantics Fair	
- The prefix-finiteness (Def. 4.1) is formalized as `fsupp` predicate from `hahn` library. 
- The declarative definition of memory fairness (Def 4.2) is given in `src/basic/Execution.v` (`mem_fair` predicate). 
- The main result of the paper stating the equivalence of operational and declarative fair definitions (Theorem 4.5) is presented in `src/equivalence/Equivalence.v` by `SC_equiv`, `TSO_equiv`, `RA_equiv` and `SCOH_equiv` theorems which are instances of a general `op_decl_def_equiv` proposition. 
- For equivalence proofs of individual models see: 
	- For SC (Lemmas B.1 and B.2) - `SC_op_implies_decl` and `SC_decl_implies_op` in `src/equivalence/SC.v`. 
	- For TSO (Lemmas B.8 and B.22) - `TSO_op_implies_decl` in  `src/equivalence/tso/TSO_op_decl.v` and `TSO_decl_implies_op` in `src/equivalence/tso/TSO_decl_op.v`.
	- For RA (Lemmas B.3 and B.4) - `RA_op_implies_decl` in `src/equivalence/ra/RAopToDecl.v` and `RA_decl_implies_op` in `src/equivalence/ra/RAdeclToOp.v`. 
	- For StrongCOH (Lemmas B.6 and B.7) - `SCOH_op_implies_decl` in `src/equivalence/strong_coh/SCOHopToDecl.v` and `SCOH_decl_implies_op` in `src/equivalence/strong_coh/SCOHdeclToOp.v`. 
- Definitions and proofs related to robustness (Section 4.4) are located in `src/robustness/Robustness.v`. 
    - The property of being a po|rf prefix (Def. 4.12) is formalized in `porf_prefix` definition.
	- The SC compactness (Prop. 4.13) is proved in `sc_compactness`. 
	- Definitions of finite and strong execution-graph robustness (Def. 4.14) are given in `finitely_robust` and `strongly_robust` correspondingly. 
	- The lifting of robustness onto the infinite execution (Theorem 4.15) is proved in `finitely2strongly`. 
	- The infinite robustness property for memory models considered in the paper (Corollary 4.16, excluding RC11) is proved in `program_robustness_models`. 
- We do not formalize the notion of thread fairness neither in an operational nor declarative sense. Instead, our `op_decl_def_equiv` proposition applies to any behavior (formalized as a set of events) without binding to a concrete program. The difference between a non-thread-fair and a thread-fair behavior of the same program in our presentation is simply that the former would lack some events presented in the latter. 
	
### (§5) Proving Deadlock Freedom for Locks
- The proof of Theorem 5.3 stating a sufficient condition for loop termination is given in `src/termination/TerminationDecl.v`, lemma `inf_reads_latest`. 
- For proofs of lock algorithms termination (progress for ticket lock) see:
  - For spinlock (Theorem 5.4) - `src/termination/SpinlockTermination.v`, theorem `spinlock_client_terminates`.
  - For ticket lock (Theorem 5.5) - `src/termination/TicketlockProgress.v`, theorem `ticketlock_client_progress`.
  - For MCS lock (Theorem 5.6, except for RC11) - `src/termination/HMCSTermination.v`, theorem `hmcs_client_terminates`.

### Used axioms

Our development relies on non-constructive axioms. Namely, we use excluded middle, functional extensionality and functional/relational choice which [can be safely added to Coq logic](https://github.com/coq/coq/wiki/The-Logic-of-Coq#what-axioms-can-be-safely-added-to-coq). 

To list axioms used to prove a theorem `Thm` execute the file with `Thm` in any proof editor, then execute `Print Assumptions Thm`. 

During the proof compilation assumptions used to prove main statements are recorded in `axioms_*.out` files. Run `print_axioms.sh` script to view their content. This script filters out irrelevant output and only prints axioms. 

## Paper claims not presented in artifact

We do not provide Coq formalization of claims from §4.3. Also, the formal proofs of Corollary 4.16 and Theorem 5.6 don't consider the RC11 case. 

# Recommendations for further extensions

If you'd like to enhance the development, there are two immediate directions. 

## Adding new memory models

To extend our results to another memory model you'll need to:

1. define its operational LTS along with the operational fairness condition;
2. set its declarative consistency predicate;
3. state and prove a theorem in `src/equivalence/Equivalence.v` similar to existing ones. You'll also need to provide few auxiliary functions to create an instance of the general `op_decl_def_equiv` definition. 

## Proving liveness properties of new algorithms

To verify some algorithm's liveness properties you'll need to do the following.

1. Formalize an algorithm's execution graph as its threads' traces properties (e.g. see `src/termination/SpinlockTermination.v`, definition `spinlock_client_execution`). Note that an under-approximation may suffice (like in the spinlock formalization). 
2. To state that the algorithm terminates you may require that its execution graph is finite. For expressing more complicated properties see e.g. the proof of ticket lock progress in `src/termination/TicketlockProgress.v`, theorem `ticketlock_client_progress`. 
3. In our framework liveness properties are proved by contradiction: assuming that some thread's execution is infinite eventually allows us to apply `inf_reads_latest` lemma and show that the graph is either not consistent or not fair. 


