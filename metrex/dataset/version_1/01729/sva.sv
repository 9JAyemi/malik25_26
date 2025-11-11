// SVA checker for VGA_Control
// Bind this file to the DUT: bind VGA_Control VGA_Control_sva sva_i(.*);

module VGA_Control_sva (
  input  logic        clock,
  input  logic        reset,
  input  logic        h_sync,
  input  logic        v_sync,
  input  logic [9:0]  actual_x,
  input  logic [8:0]  actual_y,
  input  logic [9:0]  hcounter,
  input  logic [9:0]  vcounter
);

  default clocking cb @(posedge clock); endclocking

  // No X/Z on outputs when not in reset
  assert property (disable iff (reset) !$isunknown({h_sync, v_sync, actual_x, actual_y}));

  // Async reset holds counters at 0 on clock edges while reset is high
  assert property (reset |-> (hcounter==10'd0 && vcounter==10'd0));

  // Counter ranges
  assert property (disable iff (reset) hcounter <= 10'd800);
  assert property (disable iff (reset) vcounter <= 10'd521);

  // Horizontal counter stepping and rollover
  assert property (disable iff (reset) $past(!reset) && $past(hcounter)!=10'd800 |-> hcounter == $past(hcounter)+10'd1);
  assert property (disable iff (reset) $past(!reset) && $past(hcounter)==10'd800 |-> hcounter == 10'd0);

  // Vertical counter behavior
  // Increment on horizontal rollover unless already at max
  assert property (disable iff (reset) $past(!reset) && $past(hcounter)==10'd800 && $past(vcounter)!=10'd521 |-> vcounter == $past(vcounter)+10'd1);
  // Reset at max on next clock (wins even if hcounter==800)
  assert property (disable iff (reset) $past(vcounter)==10'd521 |-> vcounter == 10'd0);
  // Stable otherwise
  assert property (disable iff (reset) $past(!reset) && $past(hcounter)!=10'd800 && $past(vcounter)!=10'd521 |-> vcounter == $past(vcounter));

  // Sync generation matches counters
  assert property (disable iff (reset) h_sync == ~ (hcounter inside {[10'd1:10'd96]}));
  assert property (disable iff (reset) v_sync == ~ (vcounter inside {[10'd1:10'd2]}));

  // Output coordinate mapping
  assert property (disable iff (reset) actual_x == (hcounter - 10'd144));
  assert property (disable iff (reset) actual_y == (vcounter - 10'd31)[8:0]);

  // Coverage: hsync pulse width and vsync pulse width
  cover  property (disable iff (reset) hcounter==10'd1  && !h_sync ##96 hcounter==10'd97 && h_sync);
  cover  property (disable iff (reset) vcounter==10'd1 && !v_sync ##[1:$] vcounter==10'd3 && v_sync);

  // Coverage: active video edges
  cover  property (disable iff (reset) hcounter==10'd144 && actual_x==10'd0);
  cover  property (disable iff (reset) hcounter==10'd783 && actual_x==10'd639);
  cover  property (disable iff (reset) vcounter==10'd31  && actual_y==9'd0);
  cover  property (disable iff (reset) vcounter==10'd510 && actual_y==9'd479);

  // Coverage: line and frame rollovers
  cover  property (disable iff (reset) hcounter==10'd800 ##1 hcounter==10'd0);
  cover  property (disable iff (reset) vcounter==10'd521 ##1 vcounter==10'd0);
  cover  property (disable iff (reset) hcounter==10'd0 && vcounter==10'd0 ##[1:$] hcounter==10'd0 && vcounter==10'd0);

endmodule

// Bind to DUT (example):
// bind VGA_Control VGA_Control_sva sva_i(.*);