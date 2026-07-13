module highest_16_bits_sva (
  input logic clk,               // Assertion clock (RTL has no clock/reset)
  input logic [31:0] in,
  input logic [3:0] control,
  input logic [15:0] out
);
  // Analysis: combinational case logic; control=1 -> in[31:16], control=2 -> in[15:0], others -> 0.

  // Out matches the exact combinational mapping for all control values.
  check_functional_mapping_exact: assert property (
    @(posedge clk) out == (control == 4'd1 ? in[31+:16] :
                           control == 4'd2 ? in[0+:16]  :
                           16'b0)
  );

  // control==0 drives zero.
  check_control0_zero: assert property (
    @(posedge clk) (control == 4'd0) |-> (out == 16'b0)
  );

  // control==1 selects upper 16 bits.
  check_control1_upper: assert property (
    @(posedge clk) (control == 4'd1) |-> (out == in[31:16])
  );

  // control==2 selects lower 16 bits.
  check_control2_lower: assert property (
    @(posedge clk) (control == 4'd2) |-> (out == in[15:0])
  );

  // control==3 drives zero (shift of 16 by 16 is zero).
  check_control3_zero: assert property (
    @(posedge clk) (control == 4'd3) |-> (out == 16'b0)
  );

  // control==4 drives zero (shift of 16 by 16 is zero).
  check_control4_zero: assert property (
    @(posedge clk) (control == 4'd4) |-> (out == 16'b0)
  );

  // control==5 drives zero (shift of 16 by 16 is zero).
  check_control5_zero: assert property (
    @(posedge clk) (control == 4'd5) |-> (out == 16'b0)
  );

  // control==6 drives zero (shift of 16 by 16 is zero).
  check_control6_zero: assert property (
    @(posedge clk) (control == 4'd6) |-> (out == 16'b0)
  );

  // control in 7..15 hits default and drives zero.
  check_default_zero_range: assert property (
    @(posedge clk) (control inside {[4'd7:4'd15]}) |-> (out == 16'b0)
  );

  // If inputs are stable, output remains stable (combinational behavior).
  check_stability_when_inputs_stable: assert property (
    @(posedge clk) $stable({in, control}) |-> $stable(out)
  );

endmodule