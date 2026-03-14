module add_sub_4bit_sva (
  input logic clk,                 // sampling clock (DUT has no clock)
  input signed [3:0] A,
  input signed [3:0] B,
  input logic mode,
  input signed [3:0] result
);
  // No reset in RTL; pure combinational logic; assertions are sampled on clk.
  // Behavior: mode=1 -> result=A+B; mode=0 -> result=A+(~B+1) == A-B.

  // In add mode, result equals A + B (4-bit signed wrap-around).
  check_add_mode_is_sum: assert property (
    @(posedge clk) mode |-> (result == $signed(A + B))
  );

  // In sub mode, result equals A + two's complement of B (4-bit).
  check_sub_mode_is_A_plus_twoscompB: assert property (
    @(posedge clk) !mode |-> (result == $signed(A + ((~B) + 4'd1)))
  );

  // In sub mode, result equals A - B (equivalent form).
  check_sub_mode_is_difference: assert property (
    @(posedge clk) !mode |-> (result == $signed(A - B))
  );

  // If B is zero, result passes A in both modes.
  check_B_zero_passthrough: assert property (
    @(posedge clk) (B == 4'sd0) |-> (result == A)
  );

  // In add mode with A=0, result equals B.
  check_add_mode_A_zero: assert property (
    @(posedge clk) (mode && (A == 4'sd0)) |-> (result == B)
  );

  // In sub mode with A=0, result equals -B (two's complement).
  check_sub_mode_A_zero: assert property (
    @(posedge clk) (!mode && (A == 4'sd0)) |-> (result == $signed(-B))
  );

  // In sub mode with A==B, result is zero.
  check_sub_mode_equal_operands_zero: assert property (
    @(posedge clk) (!mode && (A == B)) |-> (result == 4'sd0)
  );

  // In add mode with B == -A, result is zero.
  check_add_mode_negated_operands_zero: assert property (
    @(posedge clk) (mode && (B == $signed(-A))) |-> (result == 4'sd0)
  );

  // If A, B, and mode are stable, result must be stable (pure combinational function).
  check_stable_inputs_imply_stable_output: assert property (
    @(posedge clk) ($stable(A) && $stable(B) && $stable(mode)) |-> $stable(result)
  );

  // In add mode, result - A equals B (mod-16 arithmetic).
  check_add_mode_invertibility: assert property (
    @(posedge clk) mode |-> ($signed(result - A) == B)
  );

endmodule