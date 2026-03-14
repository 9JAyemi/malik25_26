module LCD_driver_sva #(
  parameter int n = 8,
  parameter int m = 3
)(
  input logic clk,
  input logic [n-1:0] data,
  input logic [m-1:0] ctrl
);

  ///// Functional equivalence /////
  // ctrl[0] equals data[0] AND data[1].
  check_ctrl0_and_function: assert property (
    @(posedge clk) ctrl[0] == (data[0] & data[1])
  );

  // ctrl[1] equals data[2] OR data[3].
  check_ctrl1_or_function: assert property (
    @(posedge clk) ctrl[1] == (data[2] | data[3])
  );

  // ctrl[2] equals data[4] XOR data[5].
  check_ctrl2_xor_function: assert property (
    @(posedge clk) ctrl[2] == (data[4] ^ data[5])
  );

  ///// Stability with stable inputs /////
  // If data[1:0] are stable, ctrl[0] must be stable.
  check_ctrl0_stable_when_inputs_stable: assert property (
    @(posedge clk) $stable(data[1:0]) |-> $stable(ctrl[0])
  );

  // If data[3:2] are stable, ctrl[1] must be stable.
  check_ctrl1_stable_when_inputs_stable: assert property (
    @(posedge clk) $stable(data[3:2]) |-> $stable(ctrl[1])
  );

  // If data[5:4] are stable, ctrl[2] must be stable.
  check_ctrl2_stable_when_inputs_stable: assert property (
    @(posedge clk) $stable(data[5:4]) |-> $stable(ctrl[2])
  );

  ///// Logical implications (derived from definitions) /////
  // ctrl[0]==1 implies both data[0] and data[1]==1.
  check_ctrl0_high_implies_data01_high: assert property (
    @(posedge clk) ctrl[0] |-> (data[0] && data[1])
  );

  // ctrl[1]==0 implies both data[2] and data[3]==0.
  check_ctrl1_low_implies_data23_low: assert property (
    @(posedge clk) !ctrl[1] |-> (!data[2] && !data[3])
  );

  // ctrl[2]==1 implies data[4] and data[5] differ.
  check_ctrl2_high_implies_data45_neq: assert property (
    @(posedge clk) ctrl[2] |-> (data[4] != data[5])
  );

  // ctrl[2]==0 implies data[4] and data[5] are equal.
  check_ctrl2_low_implies_data45_eq: assert property (
    @(posedge clk) !ctrl[2] |-> (data[4] == data[5])
  );

endmodule