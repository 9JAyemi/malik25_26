// SVA for and_module
module and_module_sva (
  input logic A,
  input logic B,
  input logic CLK,
  input logic X
);

  default clocking cb @(posedge CLK); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  // Core functional check: registered AND (1-cycle latency)
  a_reg_and: assert property (past_valid |-> X == $past(A & B));

  // No X on X when prior inputs were known
  a_no_x_out_when_inputs_known: assert property (
    past_valid && !$isunknown($past({A,B})) |-> !$isunknown(X)
  );

  // X stable between clock rising edges
  a_stable_between_clks: assert property (@(negedge CLK) $stable(X) until_with $rose(CLK));

  // Input changes must not glitch X before next rising CLK
  a_no_async_glitch_on_ab: assert property (
    @(posedge A or negedge A or posedge B or negedge B)
      $stable(X) until_with $rose(CLK)
  );

  // Functional coverage: all input combos at sampling edge
  c_ab_00: cover property (A==0 && B==0);
  c_ab_01: cover property (A==0 && B==1);
  c_ab_10: cover property (A==1 && B==0);
  c_ab_11: cover property (A==1 && B==1);

  // Coverage: output toggles
  c_x_rise: cover property (past_valid && $past(X)==0 && X==1);
  c_x_fall: cover property (past_valid && $past(X)==1 && X==0);

  // Coverage: input→output relation across the register
  c_ab11_to_x1:  cover property (past_valid && $past(A & B)==1 && X==1);
  c_abne11_to_x0: cover property (past_valid && $past(A & B)==0 && X==0);

endmodule

bind and_module and_module_sva u_and_module_sva (
  .A(A),
  .B(B),
  .CLK(CLK),
  .X(X)
);