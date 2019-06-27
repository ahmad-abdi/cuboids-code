#lang racket

;This is a code for the paper "Cuboids, a class of clutters" by
;  Ahmad Abdi, Gerard Cornuejols, Natalia Guricanova, Dabeen Lee (2019)
;  In particular, it gives a proof for Theorem 6.8 of the paper.
;  The proof of Theorem 6.8 is explained in "proof/proof.rkt". However,
;  this document should be read first.
;
;Corresponding author: Ahmad Abdi (abdi.ut@gmail.com)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;OUTLINE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;1. INTRODUCTION
;2. HOW DOES THE CODE WORK?
;3. EXAMPLES
;  3.1 all strictly non-polar sets of dimension 3 and degree =< 3
;  3.2 all critically non-polar sets of dimension 3 and degree =< 3
;  3.3 all minimally non-polar sets of dimension 4 and degree =< 3
;  3.4 all strictly non-polar sets of dimension 3 and degree =0
;  3.5 all strictly non-polar sets of dimension 3 and degree =0 with parallelization
;  3.6 all half-dense 2-regular strictly non-polar sets of dimension 5         
;  3.7 all half-dense 2-regular strictly non-polar sets of dimension 5 with parallelization    
;4. OUTLINE AND PROOF-READING THE CODE

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;1. INTRODUCTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;This code has the capability to generate all strictly non-polar sets
;  of a fixed dimension and bounded degree. It also has the capability 
;  to generate all half-dense d-regular strictly non-polar sets of a 
;  fixed dimension. In both cases, it has the ability to filter out the 
;  outputs that are not minimally or critically non-polar. The code is
;  customizable and parallelizable, so the output of the code can be
;  controlled at the wish of the user.
;
;Here we will describe how the code works, and how the user can make
;  the code run.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;2. HOW DOES THE CODE WORK?
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;An algorithm, describing the methodology of the code has been provided
;  in Section 6.2 of the paper. The actual code however is more intricate.
;  We need three definitions:
;
;DEFINITION: A *seed* is a strictly polar set.
;DEFINITION: An *embedded seed* is a partial set whose decided points
;               are contained in a restriction forming a seed.
;DEFINITION: Given partial set P, and dergee d, its *closure* is
;            obtained by repeatedly applying the following operations:
;
;      i.   if P has antipodal feasible points, set P must be PRUNED
;      ii.  if P has an infeasible point with >deg infeasible neighbors,
;              then P must be PRUNED
;      iii. if a point is feasible and its antipodal point is undecided,
;              make the undecided point infeasible; GOTO i
;      iv.  if an infeasible point has =deg infeasible neighbors, make 
;              all of its undecided neighbors feasible; GOTO i
;
;
;DESCRIPTION: To generate all non-isomorphic strictly non-polar sets of 
;  dimension n and degree =< d for n>=d, the code first
;
;    1. generates all non-isomorphic seeds of a fixed dimension, where the
;          dimension is =< min{n-1,d}, and then embeds them in dimension n.
;          
;  This gives a list of parial sets, call it *p-sets*.
;
;    2. while there's a partial set in p-sets with an undecided point,
;          pick an undecided point of p-set and branch on the point. Once 
;          an undecided point is decided, the closure is taken, and then
;          an attempt to PRUNE the partial set takes place:
;
;       2.1 if the closure operator has asked to PRUNE, the partial set is
;           PRUNED (closure pruner)
;       2.1 if there's an unavoidable proper intersecting (=non-polar) 
;           restriction regardless of how the partial set is completed, 
;           then the partial set is PRUNED (intersecting pruner)
;       2.3 if the feasible points would agree on a coordinate regardless of
;           how the set is completed, then the set is PRUNED (cover pruner)
;       2.4 if we want the strictly non-polar set to be minimally non-polar
;           as well, and no matter how the partial is completed, for some
;           coordinate i, one of the two single restrictions over coordinate i
;           will not have antipodal feasible points, then the partial set
;           is PRUNED (minimal pruner)
;       2.5 if we want the strictly non-polar set to be critically non-polar
;           as well, and no matter how the partial is completed some single
;           restriction will not have antipodal feasible points, then the
;           partial set is PRUNED (critical pruner)
;
;    3. every partial set has now been fully decided. print only one from
;       every isomorphic class.
;
;A FEW NOTES:
;
;    a.  if the objective is to generate all strictly non-polar sets of
;          dimension n and degree exactly d, where n>d, we may start with
;          d-dimensional seeds of degree exactly d
;
;    b. the computations on different seeds can be done independently of
;          and in parallel with one another. If this is done, however, the
;          outputs from different seeds may be isomorphic to one another, so
;          one last isomorphism test needs to be run.
;
;    c. the seeds are generated in a very similar manner, starting from
;          smaller seeds (some of the pruners are either not needed or
;          slightly modified), and the closure operator is different
;
;    d. the half-dense d-regular strictly non-polar sets are generated in
;         a similar manner, the main difference being the closure operator.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;3. EXAMPLES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;To generate all strictly non-polar sets of dimension =dim and degree
;  =< deg, the user first needs to decide on seeds of what dimension and
;  what degree to generate. 
; 
;The code to generate seeds resides in "seeds/generator.rkt" and is called
;
; (seeds d n)
;
;This generates all seeds of dimension n and =< d. The seeds then need
;  to be embedded in dimension =dim. So parallelization can take place later
;  on, the embedded seeds are stamped with a unique ID. The embedder and
;  stamper reside in "seeds/embed.rkt":
;
;  (stamp-embed deg n dim (seeds d n))
;
;  The stamped embedded seeds can then be divided into a number of batches
;  so parallel computation can take place.
;
;Now to generate all strictly non-polar sets of dimension =dim and degree
;   =< deg, we will run the following code in "master/generator.rkt":
;
;  (generate batch-number deg dim commands stamped-embedded-seeds)
;
;  where "batch-number" is an integer between 1 and the total number of batches,
;  and "commands" indicates whether we want the outputs to be minimally or
;  critically non-polar or not.
;
;To generate all half-dense deg-regular strictly non-polar sets of dimension =dim,
;  we will run the following code in "master/hdr_generator.rkt":
;
;  (hdr/generate batch-number deg dim commands stamped-embedded-seeds)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;3.1 Example: all strictly non-polar sets of dimension 3 and degree =< 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(require "master/generator.rkt"
;         "seeds/generator.rkt"
;         "seeds/embed.rkt")

;(generate 1 3 3 (set) (stamp-embed 2 2 3 (seeds 2 2)))

;Once run, three text files titled

;G1DIM3DEG3-output
;G1DIM3DEG3-pruners
;G1DIM3DEG3-time

;are generated.
;
;The first text file contains the output, containing 3 sets.
;The second text file indicates how many times each pruner was used.
;The third text file indicates the time spent on completing each of
;   6 seeds.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;3.2 Example: all critically non-polar sets of dimension 3 and degree =< 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(require "master/generator.rkt"
;         "seeds/generator.rkt"
;         "seeds/embed.rkt")

;(generate 1 3 3 (set "cnp") (stamp-embed 2 2 3 (seeds 2 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;3.3 Example: all minimally non-polar sets of dimension 4 and degree =< 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(require "master/generator.rkt"
;         "seeds/generator.rkt"
;         "seeds/embed.rkt")

;(generate 1 3 4 (set "mnp") (stamp-embed 2 2 4 (seeds 2 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;3.4 Example: all strictly non-polar sets of dimension 3 and degree =0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(require "master/generator.rkt"
;         "seeds/generator.rkt"
;         "seeds/embed.rkt")

;(generate 1 0 3 (set) (stamp-embed 0 2 3 (seeds 0 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;3.5 Example: all strictly non-polar sets of dimension 3 and degree =0
;                 with parallelization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;The 3 seeds are divided into a batch of size 2 and a batch of
;  size 1.

;(require "master/generator.rkt"
;         "seeds/generator.rkt"
;         "seeds/embed.rkt")

;(generate 1 0 3 (set) (take (stamp-embed 0 2 3 (seeds 0 2)) 2))
;(generate 2 0 3 (set) (drop (stamp-embed 0 2 3 (seeds 0 2)) 2))

;The first batch gives 1 set while the second batch gives 0 sets.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;3.6 Example: all half-dense 2-regular strictly non-polar sets of 
;               dimension 5
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(require "master/hdr_generator.rkt"
;         "seeds/generator.rkt"
;         "seeds/embed.rkt")

;By Theorem 1.20 (3), we may activate the critical pruner without
;  loss of generality.

;(hdr/generate 1 2 5 (set "cnp") (stamp-embed 2 3 5 (seeds 2 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;3.7 Example: all half-dense 2-regular strictly non-polar sets of 
;               dimension 5 with parallelization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(require "master/hdr_generator.rkt"
;         "seeds/generator.rkt"
;         "seeds/embed.rkt"
;         "base/isomorphism.rkt")

;The 14 seeds are divided into a batch of size 4 and a batch of size 10.

;(hdr/generate 1 2 5 (set "cnp") (take (stamp-embed 2 3 5 (seeds 2 3)) 4))
;(hdr/generate 2 2 5 (set "cnp") (drop (stamp-embed 2 3 5 (seeds 2 3)) 4))

;The first batch gives the following set
;
; ("00000" "00100" "11000" "11100" "00001" "01011" "01111" "10011" "10111"
;  "11101" "11010" "00110" "01001" "01110" "10101" "10010")
;
;while the second batch gives the following set
;
; ("00000" "00100" "01000" "10100" "00011" "00111" "01111" "10011" "11110"
;  "11101" "11001" "11010" "01001" "01110" "10101" "10010")
;
;At this point, we call a code from "base/isomorphism.rkt" to filter
; out the isomorphic sets among these two sets:

;(filter-isomorphic-sets
; '(("00000" "00100" "11000" "11100" "00001" "01011" "01111" "10011" "10111"
;  "11101" "11010" "00110" "01001" "01110" "10101" "10010")
;   ("00000" "00100" "01000" "10100" "00011" "00111" "01111" "10011" "11110"
;  "11101" "11001" "11010" "01001" "01110" "10101" "10010")))

;We see that only one set is outputted, that is, the two sets are isomorphic.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;4. OUTLINE AND PROOF-READING THE CODE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;The code has 3 main components:
;
; A. BASE (contains supporting functions for the entire code)
;    1. isomorphism.rkt 
;    2. intersecting.rkt
;    3. partial_sets.rkt
;
; B. SEEDS (contains the seeds generator)
;    1. generator.rkt
;      1.1. helper_closure.rkt
;      1.2. helper_printer.rkt
;    2. embed.rkt
;
; C. MASTER (contains the strictly non-polar sets generator)
;    1. generator.rkt
;      1.1. helper_closure.rkt
;    2. hdr_generator.rkt
;      2.1. hdr_helper_closure.rkt
;    3. helper_printer.rkt
;
; where
;
; C1 calls C1.1, C3, A1, A2, A3
;    C1.1 calls A1, A2
; C2 calls C2.1, C3, A1, A2, A3
;    C2.1 calls A2, A3
; C3 is self-contained
;
; B1 calls B1.1, B1.2, A1, A2, A3
;    B1.1 calls A3
;    B1.2 is self-contained
; B2 calls A3
;
; A1 calls A3
; A2 calls A3
; A3 is self-contained
;
;NOTE: To proof-read the code for generating strictly non-polar sets of
;       of fixed dimension and bounded degree, we recommend
;       starting from C1 and then moving to C1.1
; 
;NOTE: To proof-read the code for generating half-dense deg-regular strictly
;        non-polar sets, we recommend starting from C2 and then moving to C2.1
;
;NOTE: To proof-read the code for generating seeds, we recommend starting
;        from B1 and then moving to B1.1
;
;NOTE: Every .rkt file is fully commentated and explained, and hopefully should
;         be readable.