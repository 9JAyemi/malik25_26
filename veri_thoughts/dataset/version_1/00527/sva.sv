module dff_async_reset_sva (
  input logic clk,
  input logic d,
  input logic rst,   // active-low async reset
  input logic q
);

  // Async reset drives q low immediately on negedge rst
  assert property (@(negedge rst) ##0 (q == 1'b0))
    else $error("q not driven low immediately on async reset");

  // While reset is asserted low, q must be 0 on any clk edge
  assert property (@(posedge clk) (!rst) |-> ##0 (q == 1'b0))
    else $error("q not held low while reset is asserted");

  // After reset deasserts (rst rises), q must remain 0 until the next clk edge
  assert property (@(posedge rst) (q == 1'b0) until_with (posedge clk))
    else $error("q changed before first clk after reset deassert");

  // Functional DFF capture: on each clk edge with reset deasserted, q takes d
  // Immediate (same-cycle) check
  assert property (@(posedge clk) rst |-> ##0 (q == d))
    else $error("q did not capture d on clk");

  // One-cycle-retention check (helps avoid NBA sampling issues)
  assert property (@(posedge clk) (rst && $past(rst)) |=> (q == $past(d)))
    else $error("q not equal to previous d when reset deasserted");

  // X/unknown checks around updates
  assert property (@(posedge clk) rst |-> (!$isunknown(d) && ##0 !$isunknown(q)))
    else $error("X detected on d or q during capture");
  assert property (@(negedge rst) ##0 !$isunknown(q))
    else $error("X detected on q after async reset");

  // Coverage
  //  - Observe async reset assertion
  cover property (@(negedge rst) ##0 (q == 1'b0));
  //  - Observe reset deassert followed by first clk capturing 1
  cover property (@(posedge rst) ##[1:$] (posedge clk && rst && d) ##0 (q == 1'b1));
  //  - Observe a capture of 0 as well
  cover property (@(posedge clk) (rst && !d) ##0 (q == 1'b0));
  //  - See multiple clock edges while in reset
  cover property (@(posedge clk) (!rst)[*2]);

endmodule

// Bind into DUT
bind dff_async_reset dff_async_reset_sva u_dff_async_reset_sva (
  .clk(clk),
  .d(d),
  .rst(rst),
  .q(q)
);