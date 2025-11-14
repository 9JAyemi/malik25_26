// SVA for counter. Bind this to the DUT.
// Focused, concise checks with essential coverage.

module counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  count,
  input  logic        p,
  input  logic        q
);

  // Async reset drives count to 0 in the same timestep
  a_reset_clears_count_now: assert property (@(posedge reset) ##0 (count == 4'h0));

  // While reset is asserted, count stays 0 on every clk edge
  a_count_zero_while_reset: assert property (@(posedge clk) reset |-> (count == 4'h0));

  // After a cycle not in reset, count increments by 1 modulo 16
  a_count_increments: assert property (@(posedge clk)
                                       !$past(reset) |-> (count == ($past(count) + 4'd1)));

  // Functional correctness of p and q (after count and combinational update settle)
  a_p_func: assert property (@(posedge clk or posedge reset) ##0 (p == ^count));
  a_q_func: assert property (@(posedge clk or posedge reset) ##0 (q == &count));

  // Outputs and state free of X/Z after update points
  a_no_xz:   assert property (@(posedge clk or posedge reset) ##0
                              (!$isunknown(count) && !$isunknown(p) && !$isunknown(q)));

  // Optional: ensure p/q follow count immediately on count change (delta-cycle accuracy)
  a_pq_follow_count: assert property (@(count) ##0 (p == ^count && q == &count));

  // Coverage
  // - Hit all 16 states (when not in reset)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_STATES
      c_state: cover property (@(posedge clk) disable iff (reset) (count == i[3:0]));
    end
  endgenerate

  // - See wrap-around from 0xF to 0x0
  c_wrap: cover property (@(posedge clk) disable iff (reset)
                          ($past(!reset) && $past(count) == 4'hF && count == 4'h0));

  // - See q asserted (all ones) and p asserted at least once
  c_q_high: cover property (@(posedge clk) disable iff (reset) (q && count == 4'hF));
  c_p_high: cover property (@(posedge clk) disable iff (reset) p);

endmodule

// Bind into DUT
bind counter counter_sva u_counter_sva (
  .clk   (clk),
  .reset (reset),
  .count (count),
  .p     (p),
  .q     (q)
);