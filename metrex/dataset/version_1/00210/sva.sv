// SVA for top_module
// Bind this to the DUT to check divide-by-2, counter mod-16, and 50% duty out

module top_module_sva (
  input  logic       clk,
  input  logic       reset,
  input  logic       clk_divided,
  input  logic       out,
  input  logic [3:0] count
);

  // clk_divided: toggles every posedge clk (clean divide-by-2)
  assert property (@(posedge clk) $changed(clk_divided))
    else $error("clk_divided must toggle on every clk posedge");

  // Counter: async reset to 0 occurs immediately on reset edge (NBA => use ##0)
  assert property (@(posedge reset) 1'b1 |-> ##0 (count == 4'h0))
    else $error("count must go 0 on reset edge");

  // While reset is high, count holds at 0
  assert property (@(posedge clk_divided) reset |-> (count == 4'h0))
    else $error("count must remain 0 while reset is high");

  // Counter increments mod-16 on each clk_divided edge when not in reset
  assert property (@(posedge clk_divided)
                   disable iff (reset)
                   count == (($past(count)==4'hF) ? 4'h0 : ($past(count)+4'h1)))
    else $error("count must increment modulo-16");

  // out: async reset to 0 occurs immediately on reset edge
  assert property (@(posedge reset) 1'b1 |-> ##0 (out == 1'b0))
    else $error("out must go 0 on reset edge");

  // While reset is high, out holds at 0
  assert property (@(posedge clk_divided) reset |-> (out == 1'b0))
    else $error("out must remain 0 while reset is high");

  // out is 0 for count<8 and 1 for count>=8 (based on pre-edge count)
  assert property (@(posedge clk_divided)
                   disable iff (reset)
                   out == (($past(count) < 4'd8) ? 1'b0 : 1'b1))
    else $error("out must reflect previous count[3] (8-low/8-high)");

  // out toggles only at the half-period boundaries (prev count==7 or 15)
  assert property (@(posedge clk_divided)
                   disable iff (reset)
                   ($changed(out)) <-> (($past(count)==4'd7) || ($past(count)==4'd15)))
    else $error("out may only toggle at count boundaries 7->8 or 15->0");

  // Basic X-checks after reset is deasserted
  assert property (@(posedge clk_divided)
                   disable iff (reset)
                   !$isunknown(count) && !$isunknown(out) && !$isunknown(clk_divided))
    else $error("No X/Z allowed on key signals after reset");

  // Coverage
  cover property (@(posedge clk_divided) disable iff (reset)
                  ($past(count)==4'hF) && (count==4'h0));             // wrap
  cover property (@(posedge clk_divided) disable iff (reset) $rose(out));
  cover property (@(posedge clk_divided) disable iff (reset) $fell(out));
  cover property (@(posedge clk_divided) disable iff (reset)
                  (out==1'b0)[*8] ##1 (out==1'b1)[*8]);              // 50% duty observed
endmodule

// Bind into DUT (assumes identical internal signal names)
bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .clk_divided(clk_divided),
  .out(out),
  .count(count)
);