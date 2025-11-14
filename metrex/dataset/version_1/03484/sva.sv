// SVA for comparator(A,B,Z)
// Bind these assertions to the DUT.

module comparator_sva (input logic [1:0] A,
                       input logic [1:0] B,
                       input logic       Z);

  // Combinational sampling event
  event comb_ev;
  always @* -> comb_ev;

  // 4-state functional equivalence
  property p_func_4state;
    @(comb_ev) Z === ((A > B) | (A == B));
  endproperty
  assert property (p_func_4state)
    else $error("Z must equal (A > B) | (A == B) in 4-state semantics");

  // Deterministic behavior when inputs are known (no X/Z)
  property p_no_x_deterministic;
    @(comb_ev) !($isunknown(A) || $isunknown(B)) |-> (Z == (A >= B));
  endproperty
  assert property (p_no_x_deterministic)
    else $error("Z must equal (A >= B) when A and B are known");

  // X-propagation: any X/Z on inputs propagates to Z
  property p_x_propagation;
    @(comb_ev) $isunknown({A,B}) |-> $isunknown(Z);
  endproperty
  assert property (p_x_propagation)
    else $error("Z should be X when any bit of A or B is X/Z");

  // Targeted correctness (redundant to p_no_x_deterministic but gives pinpointed failures)
  assert property (@(comb_ev) !($isunknown({A,B})) && (A == B) |-> (Z == 1'b1))
    else $error("Z must be 1 when A == B");
  assert property (@(comb_ev) !($isunknown({A,B})) && (A > B)  |-> (Z == 1'b1))
    else $error("Z must be 1 when A > B");
  assert property (@(comb_ev) !($isunknown({A,B})) && (A < B)  |-> (Z == 1'b0))
    else $error("Z must be 0 when A < B");

  // Functional coverage
  cover property (@(comb_ev) !($isunknown({A,B})) && (A == B) && (Z == 1'b1));
  cover property (@(comb_ev) !($isunknown({A,B})) && (A >  B) && (Z == 1'b1));
  cover property (@(comb_ev) !($isunknown({A,B})) && (A <  B) && (Z == 1'b0));

  // Corner coverage
  cover property (@(comb_ev) !($isunknown({A,B})) && (A==2'b00) && (B==2'b11) && (Z==1'b0));
  cover property (@(comb_ev) !($isunknown({A,B})) && (A==2'b11) && (B==2'b00) && (Z==1'b1));
  cover property (@(comb_ev) !($isunknown({A,B})) && (A==2'b00) && (B==2'b00) && (Z==1'b1));
  cover property (@(comb_ev) !($isunknown({A,B})) && (A==2'b11) && (B==2'b11) && (Z==1'b1));

endmodule

bind comparator comparator_sva u_comparator_sva (.A(A), .B(B), .Z(Z));