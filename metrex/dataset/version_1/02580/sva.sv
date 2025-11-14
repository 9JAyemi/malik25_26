// SVA for clock_divider
module clock_divider_sva #(int unsigned TERMINAL = 26'd25000000)
(
  input  logic        clk,
  input  logic        rst,
  input  logic        clk_out,
  input  logic [25:0] counter
);

  default clocking cb @(posedge clk); endclocking

  // No X/Z on key signals
  assert property ( !$isunknown({rst, clk_out, counter}) )
    else $error("X/Z detected on rst/clk_out/counter");

  // Reset behavior (async assert, sync sample): hold reset values while rst=1
  assert property ( rst |-> (counter==26'd0 && clk_out==1'b1) )
    else $error("Reset values not held while rst=1");

  // After reset deassertion, still at reset values that cycle
  assert property ( $fell(rst) |-> (counter==26'd0 && clk_out==1'b1) )
    else $error("Not at reset values on rst deassert cycle");

  // Counter never exceeds terminal
  assert property ( disable iff (rst) counter <= TERMINAL )
    else $error("Counter exceeded terminal value");

  // Monotonic + clk_out stable while counting
  assert property ( disable iff (rst)
                    (counter < TERMINAL) |=> (counter == $past(counter)+1 && $stable(clk_out)) )
    else $error("Counter increment or clk_out stability violated while counting");

  // On terminal count: counter resets to 0 and clk_out toggles
  assert property ( disable iff (rst)
                    (counter == TERMINAL) |=> (counter==26'd0 && $changed(clk_out)) )
    else $error("Terminal action (reset/toggle) violated");

  // clk_out toggles only as a result of terminal count (exclude reset-induced change)
  assert property ( disable iff (rst)
                    ($changed(clk_out) && $past(!rst)) |-> ($past(counter) == TERMINAL) )
    else $error("clk_out toggled without terminal count");

  // Exact interval between successive toggles = TERMINAL+1 cycles
  assert property ( disable iff (rst)
                    $changed(clk_out) |=> ##(TERMINAL) $changed(clk_out) )
    else $error("Toggle interval not equal to TERMINAL+1 cycles");

  // Coverage
  cover property ( disable iff (rst) $changed(clk_out) );                 // see a toggle
  cover property ( disable iff (rst) $changed(clk_out) |=> ##(TERMINAL) $changed(clk_out) ); // full half-period
  cover property ( $rose(rst) );
  cover property ( $fell(rst) );

endmodule

// Bind into DUT (access internal counter)
bind clock_divider clock_divider_sva #(.TERMINAL(26'd25000000))
  clock_divider_sva_i (.clk(clk), .rst(rst), .clk_out(clk_out), .counter(counter));