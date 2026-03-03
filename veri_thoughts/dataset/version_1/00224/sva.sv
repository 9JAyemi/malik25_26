// SVA for sky130_fd_sc_lp__a211oi (Y = ~((A1 & A2) | B1 | C1))
module sky130_fd_sc_lp__a211oi_sva (
  input logic A1, A2, B1, C1, Y,
  input logic and0_out, nor0_out_Y
);

  // Sample on any relevant signal activity
  // Functional equivalence (4-state accurate)
  assert property (@(A1 or A2 or B1 or C1 or Y)
                   Y === ~((A1 & A2) | B1 | C1))
    else $error("a211oi: func mismatch");

  // Internal gate consistency
  assert property (@(A1 or A2 or and0_out)
                   and0_out === (A1 & A2))
    else $error("a211oi: and0_out mismatch");

  assert property (@(and0_out or B1 or C1 or nor0_out_Y)
                   nor0_out_Y === ~(and0_out | B1 | C1))
    else $error("a211oi: nor0_out_Y mismatch");

  assert property (@(nor0_out_Y or Y)
                   Y === nor0_out_Y)
    else $error("a211oi: buf mismatch");

  // Determinism when inputs are known
  assert property (@(A1 or A2 or B1 or C1 or Y)
                   (!$isunknown({A1,A2,B1,C1})) |-> (! $isunknown(Y) &&
                   (Y == ~((A1 & A2) | B1 | C1))))
    else $error("a211oi: deterministic eval failed");

  // Dominating inputs
  assert property (@(B1 or Y) (B1===1'b1) |-> (Y===1'b0))
    else $error("a211oi: B1 dominance failed");
  assert property (@(C1 or Y) (C1===1'b1) |-> (Y===1'b0))
    else $error("a211oi: C1 dominance failed");

  // AND-path resolution when B1=C1=0
  assert property (@(A1 or A2 or B1 or C1 or Y)
                   (B1===1'b0 && C1===1'b0 && A1===1'b1 && A2===1'b1) |-> (Y===1'b0))
    else $error("a211oi: AND path 11->0 failed");

  assert property (@(A1 or A2 or B1 or C1 or Y)
                   (B1===1'b0 && C1===1'b0 && (A1===1'b0 || A2===1'b0)) |-> (Y===1'b1))
    else $error("a211oi: AND path 0x->1 failed");

  // Minimal functional coverage
  cover property (@(A1 or A2 or B1 or C1 or Y)
                  !$isunknown({A1,A2,B1,C1}) && Y===1'b1); // Y high case
  cover property (@(B1 or Y) B1===1'b1 && Y===1'b0);       // B1 dominates
  cover property (@(C1 or Y) C1===1'b1 && Y===1'b0);       // C1 dominates
  cover property (@(A1 or A2 or B1 or C1 or Y)
                  B1===1'b0 && C1===1'b0 && A1===1'b1 && A2===1'b1 && Y===1'b0); // AND=1 path
endmodule

// Bind into the DUT (accesses internal nets and0_out, nor0_out_Y)
bind sky130_fd_sc_lp__a211oi sky130_fd_sc_lp__a211oi_sva
  (.A1(A1), .A2(A2), .B1(B1), .C1(C1), .Y(Y),
   .and0_out(and0_out), .nor0_out_Y(nor0_out_Y));