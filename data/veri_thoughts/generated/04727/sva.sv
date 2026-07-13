module EchoCancellation_sva #(
  parameter n = 16
) (
  input logic clk,
  input logic signed [n-1:0] s,
  input logic signed [n-1:0] e,
  input logic signed [n-1:0] f
);

  // f must always equal s minus e.
  check_subtract_relation: assert property (
    @(posedge clk) f == (s - e)
  );

  // Adding e back to f must reconstruct s.
  check_reconstruct_source: assert property (
    @(posedge clk) (f + e) == s
  );

  // When e is zero, f must match s.
  check_passthrough_when_e_zero: assert property (
    @(posedge clk) (e == '0) |-> (f == s)
  );

  // When s equals e, the subtraction result must be zero.
  check_zero_output_when_inputs_equal: assert property (
    @(posedge clk) (s == e) |-> (f == '0)
  );

  // When s is zero, f must be the negation of e.
  check_negated_e_when_s_zero: assert property (
    @(posedge clk) (s == '0) |-> (f == -e)
  );

  // If s and e stay stable across samples, f must also stay stable.
  check_output_stable_when_inputs_stable: assert property (
    @(posedge clk) ($stable(s) && $stable(e)) |-> $stable(f)
  );

endmodule