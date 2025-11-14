// SVA for synchronous_counter
module synchronous_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [3:0]  count_out
);

  // Async reset must drive 0 immediately on its posedge
  always @(posedge reset) begin
    assert (count_out == 4'd0)
      else $error("count_out not 0 on posedge reset");
  end

  // If reset is high at a clock edge, output must be 0 that cycle
  assert property (@(posedge clk) reset |-> (count_out == 4'd0));

  // Count must always be in 0..9 (ignore during reset)
  assert property (@(posedge clk) disable iff (reset)
                   (count_out <= 4'd9));

  // Hold when disabled
  assert property (@(posedge clk) disable iff (reset)
                   !$past(enable,1,reset) |-> (count_out == $past(count_out,1,reset)));

  // Increment when enabled and not at 9
  assert property (@(posedge clk) disable iff (reset)
                   $past(enable,1,reset) && ($past(count_out,1,reset) != 4'd9)
                   |-> (count_out == $past(count_out,1,reset) + 4'd1));

  // Wrap 9 -> 0 when enabled
  assert property (@(posedge clk) disable iff (reset)
                   $past(enable,1,reset) && ($past(count_out,1,reset) == 4'd9)
                   |-> (count_out == 4'd0));

  // No X/Z on output when not in reset
  assert property (@(posedge clk) disable iff (reset)
                   !$isunknown(count_out));

  // After reset deassertion, output is 0 on that clock
  assert property (@(posedge clk) $fell(reset) |-> (count_out == 4'd0));

  // Coverage
  cover property (@(posedge clk) $rose(reset)); // reset seen
  cover property (@(posedge clk) disable iff (reset)
                  $past(enable,1,reset) && ($past(count_out,1,reset) inside {[4'd0:4'd8]})
                  && (count_out == $past(count_out,1,reset) + 4'd1)); // increment seen
  cover property (@(posedge clk) disable iff (reset)
                  $past(enable,1,reset) && ($past(count_out,1,reset) == 4'd9)
                  && (count_out == 4'd0)); // wrap seen
  cover property (@(posedge clk) disable iff (reset)
                  !$past(enable,1,reset) && (count_out == $past(count_out,1,reset))); // hold seen

endmodule

bind synchronous_counter synchronous_counter_sva sva_inst (
  .clk(clk), .reset(reset), .enable(enable), .count_out(count_out)
);