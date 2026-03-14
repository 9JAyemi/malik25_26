module accumulator_sva (
  input logic clk,
  input logic rst,
  input logic [7:0] data_in,
  input logic [7:0] out
);

  // Reset drives out to zero on the next clock.
  reset_clears_out_on_next: assert property (
    @(posedge clk) rst |=> (out == 8'h00)
  );

  // When not in reset, next out equals previous out plus previous data_in (mod 256).
  accumulate_updates: assert property (
    @(posedge clk) disable iff (rst) 1 |=> (out == $past(out) + $past(data_in))
  );

  // With zero input, out holds its value across the next clock.
  hold_when_data_zero: assert property (
    @(posedge clk) disable iff (rst) (data_in == 8'h00) |=> (out == $past(out))
  );

  // With input 1, out increments by one on the next clock (mod 256).
  inc_by_one_when_data_one: assert property (
    @(posedge clk) disable iff (rst) (data_in == 8'h01) |=> (out == $past(out) + 8'h01)
  );

  // With input 0xFF, out decrements by one on the next clock (mod 256).
  dec_by_one_when_data_ff: assert property (
    @(posedge clk) disable iff (rst) (data_in == 8'hFF) |=> (out == $past(out) + 8'hFF)
  );

  // Explicit wrap: 0xFF plus 1 wraps to 0 on the next clock.
  wrap_ff_plus_one_to_zero: assert property (
    @(posedge clk) disable iff (rst) (out == 8'hFF && data_in == 8'h01) |=> (out == 8'h00)
  );

endmodule