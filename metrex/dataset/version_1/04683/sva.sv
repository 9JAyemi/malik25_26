// SVA for and_gate
module and_gate_sva (
  input logic A,
  input logic B,
  input logic Y
);

  // Functional correctness with zero-delay propagation allowance
  property p_and_func;
    @(posedge A or negedge A or posedge B or negedge B)
      ##0 (Y === (A & B));
  endproperty
  a_and_func: assert property (p_and_func)
    else $error("and_gate: Y != (A & B)");

  // Optional X/Z guard on interface (comment out if X/Z expected)
  a_no_xz_io: assert property (
      @(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
      !($isunknown({A,B,Y}))
    ) else $error("and_gate: X/Z detected on A/B/Y");

  // Truth-table coverage (complete functional space)
  c_tt_00: cover property (@(posedge A or negedge A or posedge B or negedge B) ##0 (A==0 && B==0 && Y==0));
  c_tt_01: cover property (@(posedge A or negedge A or posedge B or negedge B) ##0 (A==0 && B==1 && Y==0));
  c_tt_10: cover property (@(posedge A or negedge A or posedge B or negedge B) ##0 (A==1 && B==0 && Y==0));
  c_tt_11: cover property (@(posedge A or negedge A or posedge B or negedge B) ##0 (A==1 && B==1 && Y==1));

  // Transition coverage: observe Y rise/fall due to each input
  c_y_rise_on_A: cover property (@(posedge A) (B==1) ##0 (Y==1));
  c_y_rise_on_B: cover property (@(posedge B) (A==1) ##0 (Y==1));
  c_y_fall_on_A: cover property (@(negedge A) (B==1) ##0 (Y==0));
  c_y_fall_on_B: cover property (@(negedge B) (A==1) ##0 (Y==0));

endmodule

bind and_gate and_gate_sva sva_i (.A(A), .B(B), .Y(Y));