// SVA checker for binary_counter
module binary_counter_sva (
    input  logic        clk,
    input  logic        reset,
    input  logic [3:0]  count,
    input  logic [3:0]  curr_count,
    input  logic [3:0]  next_count
);
  // track $past() validity
  bit past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  // Core pipeline relations
  // count is always 1-cycle delayed curr_count
  assert property (@(posedge clk)
    past_valid |-> count == $past(curr_count)
  );

  // When not in reset: curr_count follows previous next_count
  assert property (@(posedge clk)
    past_valid && !reset |-> curr_count == $past(next_count)
  );

  // When not in reset: next_count = previous curr_count + 1 (mod-16)
  assert property (@(posedge clk)
    past_valid && !reset |-> next_count == $past(curr_count) + 4'd1
  );

  // In steady run (no reset for 2 cycles): curr_count increments every 2 cycles
  assert property (@(posedge clk)
    past_valid && $past(past_valid) && !reset && $past(!reset) |-> curr_count == $past(curr_count,2) + 4'd1
  );

  // Reset behavior
  // Asserting reset drives curr_count to 0 on the next cycle
  assert property (@(posedge clk)
    reset |=> curr_count == 4'd0
  );

  // Holding reset for 2+ cycles forces count to 0
  assert property (@(posedge clk)
    past_valid && reset && $past(reset) |-> count == 4'd0
  );

  // While reset is held, next_count is stable (no assignment in RTL reset branch)
  assert property (@(posedge clk)
    past_valid && reset && $past(reset) |-> next_count == $past(next_count)
  );

  // Sanity: once out of reset for 2 cycles, no X on state/outputs
  assert property (@(posedge clk)
    past_valid && $past(past_valid) && !reset && $past(!reset) |-> !$isunknown({count, curr_count, next_count})
  );

  // Coverage
  // Observe wrap-around on curr_count (increment happens every 2 cycles)
  cover property (@(posedge clk)
    past_valid && $past(past_valid) && !reset && $past(!reset) && (curr_count == 4'hF) ##2 (curr_count == 4'h0)
  );

  // Basic reset sequence: hold reset 2 cycles then run for a few cycles
  cover property (@(posedge clk)
    reset [*2] ##1 !reset [*4]
  );
endmodule

// Bind into the DUT to access internals
bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk        (clk),
  .reset      (reset),
  .count      (count),
  .curr_count (curr_count),
  .next_count (next_count)
);