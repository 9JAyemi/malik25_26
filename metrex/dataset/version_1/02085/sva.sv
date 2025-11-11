// SVA for clk_generator: concise, high-quality checks + useful coverage.
// Bind this module to the DUT instance.

module clk_generator_sva (
  input logic clk_i,
  input logic clk_core,
  input logic clk_bus
);

  // Track when $past() is valid on clk_i domain
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk_i) past_valid <= 1'b1;

  // Optional: ensure input clock edges are not X/Z
  assert property (@(posedge clk_i or negedge clk_i) !$isunknown(clk_i))
    else $error("clk_i has X/Z on an edge");

  // clk_bus must mirror clk_i (combinational connect)
  assert property (@(posedge clk_i or negedge clk_i) clk_bus === clk_i)
    else $error("clk_bus != clk_i");

  // No X/Z on outputs after first valid sample
  assert property (@(posedge clk_i) past_valid |-> !$isunknown({clk_core, clk_bus}))
    else $error("Output has X/Z");

  // clk_core toggles on every posedge of clk_i
  assert property (@(posedge clk_i) past_valid |-> clk_core == ~$past(clk_core))
    else $error("clk_core failed to toggle");

  // clk_core does not change at negedge of clk_i (i.e., only updates on posedge NBA)
  assert property (@(negedge clk_i) $stable(clk_core))
    else $error("clk_core changed away from clk_i posedge");

  // Update timing: at clk_i posedge, clk_core changes in the same time unit (post-NBA)
  assert property (@(posedge clk_i) past_valid |-> ##0 $changed(clk_core))
    else $error("clk_core did not update after clk_i posedge");

  // Initial condition: clk_core must start low (matches DUT's initial block)
  initial assert (clk_core === 1'b0)
    else $error("clk_core not initialized to 0");

  // Coverage
  cover property (@(posedge clk_i) past_valid && $rose(clk_core)); // 0->1
  cover property (@(posedge clk_i) past_valid && $fell(clk_core)); // 1->0
  cover property (@(posedge clk_i) past_valid && $changed(clk_core)[*4]); // 4 consecutive toggles
  cover property (@(posedge clk_i or negedge clk_i) $changed(clk_bus)); // bus activity

endmodule

// Bind example (place in a package or a separate sv file):
// bind clk_generator clk_generator_sva u_clk_generator_sva (.*);