// SVA for and_gate_with_control
// Checks functional equivalence, X-prop, and covers full truth table.

module and_gate_with_control_sva (
  input logic A1,
  input logic A2,
  input logic C1,
  input logic Y
);

  // Functional equivalence (sample on any relevant edge, including Y to catch glitches)
  property p_func;
    @(posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge C1 or negedge C1 or
      posedge Y  or negedge Y)
      Y === ((~C1) & (A1 & A2));
  endproperty
  assert property (p_func);

  // If inputs are known, output must be known
  property p_known_out_if_known_in;
    @(posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge C1 or negedge C1)
      !$isunknown({A1,A2,C1}) |-> !$isunknown(Y);
  endproperty
  assert property (p_known_out_if_known_in);

  // Truth-table coverage (all input combos with expected Y)
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge C1 or negedge C1)
                  (C1==0 && A1==0 && A2==0 && Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge C1 or negedge C1)
                  (C1==0 && A1==0 && A2==1 && Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge C1 or negedge C1)
                  (C1==0 && A1==1 && A2==0 && Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge C1 or negedge C1)
                  (C1==0 && A1==1 && A2==1 && Y==1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge C1 or negedge C1)
                  (C1==1 && A1==0 && A2==0 && Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge C1 or negedge C1)
                  (C1==1 && A1==0 && A2==1 && Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge C1 or negedge C1)
                  (C1==1 && A1==1 && A2==0 && Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge C1 or negedge C1)
                  (C1==1 && A1==1 && A2==1 && Y==0));

endmodule

// Bind into DUT
bind and_gate_with_control and_gate_with_control_sva sva_i (.A1(A1), .A2(A2), .C1(C1), .Y(Y));