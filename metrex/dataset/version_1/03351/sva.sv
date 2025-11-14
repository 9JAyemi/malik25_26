// SVA for binary_counter
module binary_counter_sva (
  input logic       clk,
  input logic       rst,
  input logic [3:0] count,
  input logic       max_reached
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset clears immediately
  assert property (@(posedge rst) (count==4'h0 && max_reached==1'b0))
    else $error("Async reset did not clear outputs immediately");

  // While reset is high on clk, outputs must hold cleared values
  assert property (rst |-> (count==4'h0 && max_reached==1'b0))
    else $error("Outputs not held cleared during reset");

  // No X/Z on observable outputs
  assert property (!$isunknown({count,max_reached}))
    else $error("X/Z detected on outputs");

  // Normal increment when not wrapping
  assert property (disable iff (rst)
                   ($past(!rst) && $past(count)!=4'hF)
                   |-> (count==$past(count)+4'd1 && max_reached==1'b0))
    else $error("Bad increment or stray max_reached");

  // Wrap behavior at 0xF
  assert property (disable iff (rst)
                   ($past(!rst) && $past(count)==4'hF)
                   |-> (count==4'h0 && max_reached==1'b1))
    else $error("Bad wrap behavior");

  // max_reached only on wrap and for one cycle
  assert property (disable iff (rst)
                   max_reached |-> (count==4'h0 && $past(!rst) && $past(count)==4'hF))
    else $error("max_reached asserted outside wrap");
  assert property (disable iff (rst)
                   max_reached |-> ##1 !max_reached)
    else $error("max_reached not a 1-cycle pulse");

  // Post-reset first active cycle increments from 0->1 with no pulse
  assert property (($past(rst) && !rst) |-> ($past(count)==4'h0 && count==4'd1 && max_reached==1'b0))
    else $error("Bad behavior on reset deassert");

  // Coverage
  cover property (disable iff (rst)
                  ($past(count)==4'hF && count==4'h0 && max_reached))
    ; // observed a wrap pulse
  cover property ($rose(rst)); // reset asserted
  cover property ($fell(rst)); // reset deasserted
  cover property (disable iff (rst)
                  (count==4'hE) ##1 (count==4'hF) ##1 (count==4'h0 && max_reached))
    ; // near-wrap sequence including pulse

endmodule

bind binary_counter binary_counter_sva sva_i (.*);