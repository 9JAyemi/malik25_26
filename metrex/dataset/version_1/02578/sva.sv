module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [3:0]  count_out
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid = 1'b0;
  logic seen_reset = 1'b0;
  always @(posedge clk) begin
    past_valid <= 1'b1;
    if (reset) seen_reset <= 1'b1;
  end

  // Basic X checks
  assert property (past_valid |-> !$isunknown({reset, enable}));
  assert property (seen_reset |-> !$isunknown(count_out));

  // Reset behavior
  assert property (reset |=> (count_out == 4'h0));
  assert property (past_valid && $past(reset) |-> (count_out == 4'h0));

  // Functional next-state
  assert property (past_valid && !$past(reset) &&  $past(enable) |-> count_out == ($past(count_out) + 4'h1));
  assert property (past_valid && !$past(reset) && !$past(enable) |-> count_out ==  $past(count_out));

  // Only change when enabled
  assert property (past_valid && !$past(reset) && (count_out != $past(count_out)) |-> $past(enable));

  // Explicit wrap
  assert property (past_valid && !$past(reset) && $past(enable) && ($past(count_out) == 4'hF) |-> (count_out == 4'h0));

  // Coverage
  cover property (past_valid && !$past(reset) && $past(enable) && ($past(count_out) == 4'hF) ##1 (count_out == 4'h0)); // wrap
  cover property (past_valid && !$past(reset) && !$past(enable) ##1 (count_out == $past(count_out)));                 // hold
  cover property (!reset && (count_out != 4'h0) ##1 reset ##1 (count_out == 4'h0));                                   // reset from non-zero

endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .count_out(count_out)
);