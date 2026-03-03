// SVA for and3 — concise, high-quality checks and coverage
// Bind these assertions to the DUT to verify functionality and internal nets.

module and3_sva (
  input logic A, B, C,
  input logic X,
  input logic AB, ABC
);

  // Sample on any input edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C
  ); endclocking

  // Basic sanity: no X/Z on any nets
  a_no_x_inputs:  assert property (!$isunknown({A,B,C}));
  a_no_x_internals_outputs: assert property (!$isunknown({AB,ABC,X}));

  // Functional correctness (including internal wires)
  a_ab:  assert property (AB  === (A & B));
  a_abc: assert property (ABC === (AB & C));
  a_x:   assert property (X   === (A & B & C));

  // Output changes must be caused by an input change (no spontaneous glitches)
  a_x_change_has_cause: assert property (@(posedge X or negedge X) $changed({A,B,C}));

  // Functional coverage: all 8 input combinations observed with correct X
  c_000: cover property (A==0 && B==0 && C==0 && X==0);
  c_001: cover property (A==0 && B==0 && C==1 && X==0);
  c_010: cover property (A==0 && B==1 && C==0 && X==0);
  c_011: cover property (A==0 && B==1 && C==1 && X==0);
  c_100: cover property (A==1 && B==0 && C==0 && X==0);
  c_101: cover property (A==1 && B==0 && C==1 && X==0);
  c_110: cover property (A==1 && B==1 && C==0 && X==0);
  c_111: cover property (A==1 && B==1 && C==1 && X==1);

  // Output transition coverage
  cx_rise: cover property (@(posedge X) 1);
  cx_fall: cover property (@(negedge X) 1);

endmodule

// Bind to the DUT (internal nets AB, ABC are connected by name in the DUT scope)
bind and3 and3_sva u_and3_sva (.A(A), .B(B), .C(C), .X(X), .AB(AB), .ABC(ABC));