module comparator_sva #(
  parameter n = 4,
  parameter s = 0
)(
  input logic clk,
  input logic [n-1:0] in1,
  input logic [n-1:0] in2,
  input logic out
);

  // RTL is combinational; sample its behavior on an external clock.
  // Output must match the RTL expression on every sample.
  check_output_matches_rtl: assert property (
    @(posedge clk)
    out == ((s == 1) ? ((in1[n-1] ^ in2[n-1]) ? in1[n-1] : (in1 > in2)) : (in1 > in2))
  );

  generate
    if (s == 1) begin : gen_signed
      // Different sign bits make the output follow in1's sign bit.
      check_signed_diff_sign_behavior: assert property (
        @(posedge clk)
        (in1[n-1] ^ in2[n-1]) |-> (out == in1[n-1])
      );

      // Matching sign bits use the vector greater-than result.
      check_signed_same_sign_behavior: assert property (
        @(posedge clk)
        !(in1[n-1] ^ in2[n-1]) |-> (out == (in1 > in2))
      );

      // Sign pattern 10 forces the output high.
      check_signed_10_high: assert property (
        @(posedge clk)
        (in1[n-1] && !in2[n-1]) |-> out
      );

      // Sign pattern 01 forces the output low.
      check_signed_01_low: assert property (
        @(posedge clk)
        (!in1[n-1] && in2[n-1]) |-> !out
      );

      // Equal inputs never assert the output.
      check_signed_equal_inputs_low: assert property (
        @(posedge clk)
        (in1 == in2) |-> !out
      );
    end else begin : gen_unsigned
      // A larger in1 must assert the output.
      check_unsigned_gt_high: assert property (
        @(posedge clk)
        (in1 > in2) |-> out
      );

      // A smaller in1 must deassert the output.
      check_unsigned_lt_low: assert property (
        @(posedge clk)
        (in1 < in2) |-> !out
      );

      // Equal inputs never assert the output.
      check_unsigned_equal_inputs_low: assert property (
        @(posedge clk)
        (in1 == in2) |-> !out
      );
    end
  endgenerate

endmodule