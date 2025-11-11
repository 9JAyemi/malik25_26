// SVA for lfsr_counter
// Bindable checker that verifies reset behavior, shift/feedback, and output timing.

module lfsr_counter_sva #(parameter int unsigned SIZE = 4)
(
  input  logic                     clk,
  input  logic                     reset,
  input  logic [SIZE-1:0]          out,
  input  logic [SIZE-1:0]          state
);

  // Elaboration-time sanity
  initial begin
    if (SIZE < 2) begin
      $error("lfsr_counter: SIZE must be >= 2");
      $fatal;
    end
  end

  // Async reset immediately clears both regs
  assert property (@(posedge reset) (state == '0 && out == '0));

  // While reset is held, both remain 0
  assert property (@(posedge clk) reset |-> (state == '0 && out == '0));

  // On first clock after reset deasserts, state becomes ...0001 and out is 0
  assert property (@(posedge clk) (!reset && $past(reset)) |-> (state == {{(SIZE-1){1'b0}},1'b1} && out == '0));

  // Shift correctness (upper bits)
  assert property (@(posedge clk) !reset |-> (state[SIZE-1:1] == $past(state[SIZE-2:0])));

  // Feedback bit correctness (LSB)
  assert property (@(posedge clk) !reset |-> (state[0] == ($past(state[SIZE-1]) ^ $past(state[SIZE-2]) ^ 1'b1)));

  // Output lags state by one cycle when not in reset
  assert property (@(posedge clk) !reset |-> (out == $past(state)));

  // Coverage: reset release observed
  cover property (@(posedge clk) (!reset && $past(reset) && state == {{(SIZE-1){1'b0}},1'b1}));

  // Coverage: both feedback XOR parities seen
  cover property (@(posedge clk) (!reset && $past(!reset) && ($past(state[SIZE-1] ^ state[SIZE-2]) == 1'b0)));
  cover property (@(posedge clk) (!reset && $past(!reset) && ($past(state[SIZE-1] ^ state[SIZE-2]) == 1'b1)));

endmodule

// Bind into the DUT (example)
// bind lfsr_counter lfsr_counter_sva #(.SIZE(SIZE)) u_lfsr_counter_sva ( .clk(clk), .reset(reset), .out(out), .state(state) );