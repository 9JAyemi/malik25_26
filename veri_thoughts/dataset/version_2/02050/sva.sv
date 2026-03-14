module data_converter_sva (
  input logic clk,
  input logic reset,         // active-high synchronous reset
  input logic [7:0] in,
  input logic select,
  input logic [15:0] out
);
  // Clock: clk (posedge). Reset: reset (active-high). Logic: sequential (registered out).
  // Behavior: on each clk, out <= select ? {8'h00,in} : {in,8'h00}; reset clears out to 0.

  // Out is zero on the cycle after reset is asserted.
  check_reset_clears_next: assert property (
    @(posedge clk) reset |=> (out == 16'h0000)
  );

  // While reset is held HIGH for 2+ cycles, out is zero.
  check_reset_holds_zero: assert property (
    @(posedge clk) (reset && $past(reset)) |-> (out == 16'h0000)
  );

  // With select=1 in the previous cycle (and not in reset), out = {8'h00, previous in}.
  check_update_sel1: assert property (
    @(posedge clk) disable iff (reset)
      ($past(reset) == 1'b0) && ($past(select) == 1'b1) |-> (out == {8'h00, $past(in)})
  );

  // With select=0 in the previous cycle (and not in reset), out = {previous in, 8'h00}.
  check_update_sel0: assert property (
    @(posedge clk) disable iff (reset)
      ($past(reset) == 1'b0) && ($past(select) == 1'b0) |-> (out == {$past(in), 8'h00})
  );

  // On any non-reset cycle, out matches selected concatenation of previous in.
  check_functional_update: assert property (
    @(posedge clk) disable iff (reset)
      ($past(reset) == 1'b0) |-> (out == ($past(select) ? {8'h00, $past(in)} : {$past(in), 8'h00}))
  );

  // If select stays 1 and in is stable across cycles (no reset), out holds its value.
  check_hold_when_sel1_and_in_stable: assert property (
    @(posedge clk) disable iff (reset)
      ($past(reset) == 1'b0) && ($past(select) == 1'b1) && (select == 1'b1) && ($past(in) == in) |-> (out == $past(out))
  );

  // If select stays 0 and in is stable across cycles (no reset), out holds its value.
  check_hold_when_sel0_and_in_stable: assert property (
    @(posedge clk) disable iff (reset)
      ($past(reset) == 1'b0) && ($past(select) == 1'b0) && (select == 1'b0) && ($past(in) == in) |-> (out == $past(out))
  );

endmodule