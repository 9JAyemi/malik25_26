// SVA for binary_counter
module binary_counter_sva (
  input clk,
  input rst,     // active-low
  input en,
  input [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Async reset behavior
  assert property (@(negedge rst) count == 4'h0) else $error("count must clear on async reset");
  assert property ( !rst |-> count == 4'h0 ) else $error("count must hold 0 while rst=0");

  // No X/Z when out of reset
  assert property ( rst |-> (!$isunknown(count) && !$isunknown(en)) ) else $error("X/Z detected when rst=1");

  // Next-state function (when previously out of reset)
  assert property ( disable iff (!rst) $past(rst) && !$past(en) |-> count == $past(count) )
    else $error("count changed while en=0");
  assert property ( disable iff (!rst) $past(rst) && $past(en) && ($past(count) != 4'hF) |-> count == $past(count) + 1 )
    else $error("increment failed");
  assert property ( disable iff (!rst) $past(rst) && $past(en) && ($past(count) == 4'hF) |-> count == 4'h0 )
    else $error("wrap failed at 0xF");

  // First cycle after reset deassert
  assert property ( $rose(rst) && en  |=> count == 4'h1 ) else $error("post-reset increment wrong");
  assert property ( $rose(rst) && !en |=> count == 4'h0 ) else $error("post-reset hold wrong");

  // Coverage
  cover property ( $fell(rst) );                                  // saw async reset assert
  cover property ( $rose(rst) ##1 count == 4'h0 );                // clean release
  cover property ( disable iff (!rst) $past(rst) && !$past(en) && count == $past(count) );               // hold
  cover property ( disable iff (!rst) $past(rst) && $past(en) && ($past(count) < 4'hF) && count == $past(count)+1 ); // inc
  cover property ( disable iff (!rst) $past(rst) && $past(en) && ($past(count) == 4'hF) && count == 4'h0 );          // wrap
endmodule

// Bind to DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (.clk(clk), .rst(rst), .en(en), .count(count));