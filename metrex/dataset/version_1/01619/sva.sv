// SVA for clock_divider
// Bindable checker that verifies counter behavior, output toggles, and locked semantics.

module clock_divider_sva
(
  input  logic        clk,
  input  logic        reset,
  input  logic        locked,
  input  logic        clk_out1,
  input  logic        clk_out2,
  input  logic        clk_out3,
  input  logic [23:0] count,
  input  logic [23:0] limit1,
  input  logic [23:0] limit2,
  input  logic [23:0] limit3
);

  localparam logic [23:0] MAX = 24'hFFFFFF;

  // Default sampling and gating
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic sanity: limits are static, ordered, and within range
  assert property ($stable(limit1) && $stable(limit2) && $stable(limit3))
    else $error("clock_divider: limits changed at runtime");

  assert property (limit1 != 0 && limit2 != 0 && limit3 != 0 &&
                   limit3 < limit2 && limit2 < limit1 && limit1 <= MAX)
    else $error("clock_divider: invalid limit values/order");

  // Asynchronous reset effect observed at next clock edge
  assert property (@(posedge clk) reset |-> (count==24'd0 && clk_out1==1'b0 && locked==1'b0))
    else $error("clock_divider: reset values incorrect");

  // No X/Z in normal operation
  assert property (!$isunknown({clk_out1, clk_out2, clk_out3, locked}))
    else $error("clock_divider: X/Z detected on outputs/locked");

  // Counter increments by 1, wraps at MAX
  assert property (count == $past(count)+24'd1 ||
                   ($past(count)==MAX && count==24'd0))
    else $error("clock_divider: counter increment/wrap violation");

  // Output toggles occur iff previous count hit corresponding limit, and they truly toggle
  // clk_out1
  assert property ($changed(clk_out1) |-> $past(count)==limit1)
    else $error("clock_divider: clk_out1 changed at wrong time");
  assert property ($past(count)==limit1 |-> clk_out1 == ~$past(clk_out1))
    else $error("clock_divider: clk_out1 did not toggle at limit1");

  // clk_out2
  assert property ($changed(clk_out2) |-> $past(count)==limit2)
    else $error("clock_divider: clk_out2 changed at wrong time");
  assert property ($past(count)==limit2 |-> clk_out2 == ~$past(clk_out2))
    else $error("clock_divider: clk_out2 did not toggle at limit2");

  // clk_out3
  assert property ($changed(clk_out3) |-> $past(count)==limit3)
    else $error("clock_divider: clk_out3 changed at wrong time");
  assert property ($past(count)==limit3 |-> clk_out3 == ~$past(clk_out3))
    else $error("clock_divider: clk_out3 did not toggle at limit3");

  // locked updates only at 0 and half-limits
  assert property ($changed(locked) |->
                   ($past(count)==24'd0 ||
                    $past(count)==(limit1>>1) ||
                    $past(count)==(limit2>>1) ||
                    $past(count)==(limit3>>1)))
    else $error("clock_divider: locked changed at illegal time");

  // Correct locked values when they update
  assert property ($past(count)==24'd0 |-> locked==1'b1)
    else $error("clock_divider: locked not set at count==0");

  assert property ($past(count)==(limit1>>1) |-> locked == ($past(clk_out1)==$past(clk)))
    else $error("clock_divider: locked value wrong at limit1/2");

  assert property ($past(count)==(limit2>>1) |-> locked == ($past(clk_out2)==$past(clk)))
    else $error("clock_divider: locked value wrong at limit2/2");

  assert property ($past(count)==(limit3>>1) |-> locked == ($past(clk_out3)==$past(clk)))
    else $error("clock_divider: locked value wrong at limit3/2");

  // Coverage: observe at least one toggle for each output, a wrap, and locked updates
  cover property ($past(count)==limit1 && $changed(clk_out1));
  cover property ($past(count)==limit2 && $changed(clk_out2));
  cover property ($past(count)==limit3 && $changed(clk_out3));
  cover property ($past(count)==MAX && count==24'd0);
  cover property ($past(count)==(limit1>>1));
  cover property ($past(count)==(limit2>>1));
  cover property ($past(count)==(limit3>>1));
  cover property ($past(count)==24'd0 && locked==1'b1);

endmodule

// Example bind (place in a testbench or a package included by TB)
// bind clock_divider clock_divider_sva sva_i (.*);