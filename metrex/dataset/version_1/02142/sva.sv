// SVA checkers and binds for the given DUTs.
// Concise, high-quality assertions with essential coverage.

`ifndef THREE_INPUT_AND_GATE_SVA_SV
`define THREE_INPUT_AND_GATE_SVA_SV

module three_input_and_gate_sva (
  input logic A1, A2, A3,
  input logic X
);
  // Functional equivalence (4-state), sampled after delta on any activity
  assert property (@(A1 or A2 or A3 or X) 1 |-> ##0 (X === (A1 & A2 & A3)))
    else $error("three_input_and_gate: X != A1&A2&A3");

  // Zero dominance
  assert property (@(A1 or A2 or A3 or X)
                   ((A1===1'b0)||(A2===1'b0)||(A3===1'b0)) |-> ##0 (X===1'b0))
    else $error("three_input_and_gate: zero dominance violated");

  // All-ones implies X=1
  assert property (@(A1 or A2 or A3 or X)
                   ((A1===1'b1)&&(A2===1'b1)&&(A3===1'b1)) |-> ##0 (X===1'b1))
    else $error("three_input_and_gate: all-ones should yield X=1");

  // X must not change unless some input changed
  assert property (@(A1 or A2 or A3 or X) $changed(X) |-> $changed({A1,A2,A3}))
    else $error("three_input_and_gate: X changed without input change");

  // X-propagation: if no input is 0 and some input unknown, X must be unknown
  assert property (@(A1 or A2 or A3 or X)
                   (!((A1===1'b0)||(A2===1'b0)||(A3===1'b0)) && $isunknown({A1,A2,A3}))
                   |-> ##0 $isunknown(X))
    else $error("three_input_and_gate: X-prop violated for AND");

  // Coverage: demonstrate each input controls X when others are 1
  cover property (@(posedge A1) (A2===1 && A3===1) ##0 (X===1));
  cover property (@(posedge A2) (A1===1 && A3===1) ##0 (X===1));
  cover property (@(posedge A3) (A1===1 && A2===1) ##0 (X===1));

  cover property (@(negedge A1) (A2===1 && A3===1) ##0 (X===0));
  cover property (@(negedge A2) (A1===1 && A3===1) ##0 (X===0));
  cover property (@(negedge A3) (A1===1 && A2===1) ##0 (X===0));

  // Output toggles observed
  cover property (@(A1 or A2 or A3 or X) $rose(X));
  cover property (@(A1 or A2 or A3 or X) $fell(X));
endmodule

bind three_input_and_gate three_input_and_gate_sva i_three_input_and_gate_sva (
  .A1(A1), .A2(A2), .A3(A3), .X(X)
);

`endif


`ifndef SKY130_FD_SC_LP__A311O_0_SVA_SV
`define SKY130_FD_SC_LP__A311O_0_SVA_SV

module sky130_fd_sc_lp__a311o_0_sva (
  input logic A1, A2, A3, B1, C1,
  input logic X
);
  // Functional equivalence (5-input AND), sampled after delta on any activity
  assert property (@(A1 or A2 or A3 or B1 or C1 or X)
                   1 |-> ##0 (X === (A1 & A2 & A3 & B1 & C1)))
    else $error("a311o_0: X != A1&A2&A3&B1&C1");

  // Zero dominance
  assert property (@(A1 or A2 or A3 or B1 or C1 or X)
                   ((A1===0)||(A2===0)||(A3===0)||(B1===0)||(C1===0)) |-> ##0 (X===0))
    else $error("a311o_0: zero dominance violated");

  // All-ones implies X=1
  assert property (@(A1 or A2 or A3 or B1 or C1 or X)
                   ((A1===1)&&(A2===1)&&(A3===1)&&(B1===1)&&(C1===1)) |-> ##0 (X===1))
    else $error("a311o_0: all-ones should yield X=1");

  // X must not change unless some input changed
  assert property (@(A1 or A2 or A3 or B1 or C1 or X)
                   $changed(X) |-> $changed({A1,A2,A3,B1,C1}))
    else $error("a311o_0: X changed without input change");

  // X-propagation: if no input is 0 and some input unknown, X must be unknown
  assert property (@(A1 or A2 or A3 or B1 or C1 or X)
                   (!((A1===0)||(A2===0)||(A3===0)||(B1===0)||(C1===0))
                    && $isunknown({A1,A2,A3,B1,C1}))
                   |-> ##0 $isunknown(X))
    else $error("a311o_0: X-prop violated for AND");

  // Coverage: each input’s control of X with others high
  cover property (@(posedge A1) (A2===1 && A3===1 && B1===1 && C1===1) ##0 (X===1));
  cover property (@(posedge A2) (A1===1 && A3===1 && B1===1 && C1===1) ##0 (X===1));
  cover property (@(posedge A3) (A1===1 && A2===1 && B1===1 && C1===1) ##0 (X===1));
  cover property (@(posedge B1) (A1===1 && A2===1 && A3===1 && C1===1) ##0 (X===1));
  cover property (@(posedge C1) (A1===1 && A2===1 && A3===1 && B1===1) ##0 (X===1));

  cover property (@(negedge A1) (A2===1 && A3===1 && B1===1 && C1===1) ##0 (X===0));
  cover property (@(negedge A2) (A1===1 && A3===1 && B1===1 && C1===1) ##0 (X===0));
  cover property (@(negedge A3) (A1===1 && A2===1 && B1===1 && C1===1) ##0 (X===0));
  cover property (@(negedge B1) (A1===1 && A2===1 && A3===1 && C1===1) ##0 (X===0));
  cover property (@(negedge C1) (A1===1 && A2===1 && A3===1 && B1===1) ##0 (X===0));

  // Output toggles observed
  cover property (@(A1 or A2 or A3 or B1 or C1 or X) $changed(X));
endmodule

bind sky130_fd_sc_lp__a311o_0 sky130_fd_sc_lp__a311o_0_sva i_sky130_fd_sc_lp__a311o_0_sva (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .C1(C1), .X(X)
);

`endif