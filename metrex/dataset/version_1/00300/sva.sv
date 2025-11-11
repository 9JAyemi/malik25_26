// SVA for transition_counter
// Binds into the DUT and checks functional intent concisely.

module transition_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [31:0] in,
  input  logic [3:0]  count,
  input  logic [31:0] prev_in,
  input  logic [3:0]  transition_count
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  property p_reset_clears_regs;
    reset |-> (prev_in == 32'h0 && transition_count == 4'h0);
  endproperty
  assert property (p_reset_clears_regs);

  // Count not driven in reset, so it must hold its value while reset==1
  assert property (reset |-> $stable(count));

  // prev_in tracks in every non-reset cycle
  assert property (!$past(reset) && !reset |-> prev_in == $past(in));

  // After reset deasserts, prev_in loads current in immediately
  assert property ($past(reset) && !reset |-> prev_in == in);

  // Transition counter behavior (only bit 0 rising edge counts)
  assert property (!$past(reset) && !reset && $rose(in[0])
                   |-> transition_count == $past(transition_count) + 4'd1);

  assert property (!$past(reset) && !reset && !$rose(in[0])
                   |-> transition_count == $past(transition_count));

  // Output count mirrors transition_count, except it lags by 1 cycle on a rising edge
  assert property (!$past(reset) && !reset && $rose(in[0])
                   |-> count == $past(transition_count));

  assert property (!$past(reset) && !reset && !$rose(in[0])
                   |-> count == transition_count);

  // First non-reset cycle: transition_count reflects in[0], count still 0
  assert property ($past(reset) && !reset |-> transition_count == (in[0] ? 4'd1 : 4'd0) && count == 4'd0);

  // Coverage

  // See at least one counted 0->1 transition
  cover property (!$past(reset) && !reset && $rose(in[0]));

  // See wrap-around from 15->0 on a counted transition
  cover property (!$past(reset) && !reset && $past(transition_count)==4'hF && $rose(in[0]) &&
                  transition_count==4'h0 && count==$past(transition_count));
endmodule

bind transition_counter transition_counter_sva sva_i (
  .clk(clk),
  .reset(reset),
  .in(in),
  .count(count),
  .prev_in(prev_in),
  .transition_count(transition_count)
);