// SVA for two_bit_counter
// Bind into the DUT to access internals (count)
module two_bit_counter_sva;
  // In bound scope, these names resolve to DUT signals
  // dclk, rst, control, count

  default clocking cb @(posedge dclk); endclocking

  // Basic X/Z checks at clock edges
  assert property ( !$isunknown(rst) ) else $error("rst X/Z");
  assert property ( !$isunknown(control) ) else $error("control X/Z");

  // control must always mirror count
  assert property ( control == count );

  // Asynchronous reset takes immediate effect (same timestep)
  assert property ( @(posedge rst) ##0 (count==2'b00 && control==2'b00) )
    else $error("Immediate async reset to 0 failed");

  // While reset is asserted at a clock edge, outputs are 0
  assert property ( rst |-> (count==2'b00 && control==2'b00) )
    else $error("Values not 0 while in reset");

  // If reset stays asserted across cycles, count must be stable at 0
  assert property ( rst && $past(rst) |-> $stable(count) )
    else $error("Count changed while reset held");

  // On any observed rising reset (between last and this clk), count is 0
  assert property ( $rose(rst) |-> count==2'b00 )
    else $error("Count not cleared after reset rose");

  // Free-running increment by 1 (mod-4) each clk when not in reset
  // Guard first-cycle with !$isunknown($past(count))
  assert property ( disable iff (rst)
                    !$isunknown($past(count)) |-> count == $past(count)+2'b01 )
    else $error("Bad increment when not in reset");

  // Coverage: see full 0->1->2->3->0 sequence without reset
  cover property ( disable iff (rst)
                   count==2'b00 ##1 count==2'b01 ##1 count==2'b10 ##1 count==2'b11 ##1 count==2'b00 );

  // Coverage: async reset clears a non-zero count
  cover property ( $past(!rst) && $past(count)!=2'b00 && rst && count==2'b00 );
endmodule

bind two_bit_counter two_bit_counter_sva tbc_sva();