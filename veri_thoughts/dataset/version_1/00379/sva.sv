// SVA for dff2: concise, high-quality checks and coverage
module dff2_sva(input logic clk, clrn, input logic [1:0] d, q);

  default clocking cb @(posedge clk); endclocking

  // Disallow coincident posedge clk and negedge clrn (race-prone)
  assert property (@(posedge clk) !$fell(clrn));
  assert property (@(negedge clrn) !$rose(clk));

  // Async reset forces/holds zero (checked at both events)
  assert property (@(posedge clk or negedge clrn) !clrn |-> (q === 2'b00));

  // Synchronous D capture when not in reset (1-cycle latency)
  assert property (disable iff (!clrn) q == $past(d));

  // Knownness: if D known for a full cycle, Q is known next cycle
  assert property (disable iff (!clrn) !$isunknown($past(d)) |-> !$isunknown(q));

  // Basic sanity: clrn not X at sampling edges
  assert property (@(posedge clk) !$isunknown(clrn));

  // Coverage
  // Reset pulse seen and released
  cover property (@(negedge clrn) !clrn ##[1:$] $rose(clrn));
  // Normal capture observed
  cover property (disable iff (!clrn) q == $past(d));
  // Bit-level toggles captured
  cover property (disable iff (!clrn) $rose(q[0]));
  cover property (disable iff (!clrn) $fell(q[0]));
  cover property (disable iff (!clrn) $rose(q[1]));
  cover property (disable iff (!clrn) $fell(q[1]));
  // All output values observed
  cover property (disable iff (!clrn) q == 2'b00);
  cover property (disable iff (!clrn) q == 2'b01);
  cover property (disable iff (!clrn) q == 2'b10);
  cover property (disable iff (!clrn) q == 2'b11);

endmodule

// Bind to DUT
bind dff2 dff2_sva u_dff2_sva (.clk(clk), .clrn(clrn), .d(d), .q(q));