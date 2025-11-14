// SVA for binary_counter (bindable). Focused, high-quality checks and key covers.
module binary_counter_sva
  (input  logic        clk,
   input  logic        reset,       // DUT implements active-LOW async reset
   input  logic        load,
   input  logic [3:0]  load_value,
   input  logic [3:0]  q,
   input  logic        carry_out,
   input  logic        led);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset); // disable assertions when reset is asserted low

  // Async reset behavior (active-low)
  // Immediate effect on negedge reset and hold while low
  ap_async_reset_immediate: assert property (@(negedge reset) 1 |-> (q == 4'b0101));
  ap_reset_hold_value:      assert property (@(posedge clk) (!reset) |-> (q == 4'b0101));

  // First cycle after reset release (with no load): 5 -> 6
  ap_first_after_release: assert property (reset && $past(!reset) && !load |-> q == 4'h6);

  // Load has priority; on load, q takes load_value at that edge
  ap_load_priority: assert property (load |-> (q == $past(load_value)));

  // Count up by 1 when not loading, with wrap at 15->0
  ap_count_increment: assert property (reset && $past(reset) && !load && $past(!load)
                                       |-> q == (($past(q)==4'hF) ? 4'h0 : $past(q)+4'h1));

  // Output equivalences
  ap_carry_def: assert property (carry_out == (q == 4'hF));
  ap_led_def:   assert property (led == carry_out);

  // No X/Z on outputs during normal operation
  ap_no_x: assert property (!$isunknown({q, carry_out, led}));

  // Key covers
  // Wrap sequence 14->15->0 without load
  cp_wrap: cover property (reset && !load && q==4'hE ##1 reset && !load && q==4'hF ##1 reset && !load && q==4'h0);

  // Load any value and observe it on q
  cp_load_any: cover property (reset && load ##1 q == $past(load_value));

  // Load 15 specifically and see carry_out/led high
  cp_load_15: cover property (reset && (load_value==4'hF) && load ##1 (q==4'hF && carry_out && led));

  // Simultaneous q==15 with load asserted: load must win (no wrap)
  cp_load_over_wrap: cover property (reset && q==4'hF && load ##1 q == $past(load_value));

endmodule

// Bind into DUT (adjust instance pathing as needed)
bind binary_counter binary_counter_sva
  (.clk(clk),
   .reset(reset),
   .load(load),
   .load_value(load_value),
   .q(q),
   .carry_out(carry_out),
   .led(led));