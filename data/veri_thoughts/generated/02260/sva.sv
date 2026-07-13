module logic_gate_sva (
  input logic clk,
  input logic A,
  input logic B,
  input logic C,
  input logic D,
  input logic Y
);
  // Y must equal (A & ~B & C) | D.
  check_functional_equivalence: assert property (
    @(posedge clk) Y == ((A & (~B) & C) | D)
  );

  // D high forces Y high.
  check_D_high_forces_Y_high: assert property (
    @(posedge clk) D |-> (Y == 1'b1)
  );

  // When D is low and A=1,B=0,C=1, Y must be high.
  check_and_true_sets_Y_when_D_low: assert property (
    @(posedge clk) (!D && A && !B && C) |-> (Y == 1'b1)
  );

  // When D is low and B is high, Y must be low.
  check_B_high_blocks_when_D_low: assert property (
    @(posedge clk) (!D && B) |-> (Y == 1'b0)
  );

  // When D is low and A is low, Y must be low.
  check_A_low_blocks_when_D_low: assert property (
    @(posedge clk) (!D && !A) |-> (Y == 1'b0)
  );

  // When D is low and C is low, Y must be low.
  check_C_low_blocks_when_D_low: assert property (
    @(posedge clk) (!D && !C) |-> (Y == 1'b0)
  );

  // If Y is high while D is low, A=1,B=0,C=1 must hold.
  check_Y_high_requires_inputs_when_D_low: assert property (
    @(posedge clk) (Y && !D) |-> (A && !B && C)
  );

  // If Y is low while D is low, at least one of A=0, B=1, or C=0 holds.
  check_Y_low_implies_one_input_blocks_when_D_low: assert property (
    @(posedge clk) (!Y && !D) |-> ((!A) || B || (!C))
  );
endmodule