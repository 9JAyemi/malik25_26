// SVA for counter
module counter_sva (input logic clk, input logic rst, input logic [3:0] out);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Sanity: no X/Z on controls/outputs (guard out after first edge)
  assert property (!$isunknown(rst));
  assert property (past_valid |-> !$isunknown(out));

  // Reset behavior
  assert property (rst |-> out == 4'd0);

  // Count-up by +1 when not in reset (mod-16 by width)
  assert property (past_valid && !rst |-> out == $past(out) + 4'd1);

  // Explicit wrap from 15 -> 0 when not in reset
  assert property (past_valid && !rst && $past(out)==4'hF |-> out==4'h0);

  // No mid-cycle glitches: out only changes on posedge clk
  assert property (@(negedge clk) $stable(out));

  // Useful covers
  cover property (rst ##1 !rst ##1 out==4'd1);                 // reset release leads to 1
  cover property (past_valid && !rst && $past(out)==4'hF |-> out==4'h0); // wrap observed
  cover property (!rst && out==4'd0 ##1 out==4'd1 ##1 out==4'd2 ##1 out==4'd3); // counting seen
  cover property (rst[*2]);                                     // reset held multiple cycles
endmodule

// Bind into DUT
bind counter counter_sva counter_sva_i (.clk(clk), .rst(rst), .out(out));