// SVA for glitch_filter
// Bind into the DUT to access internal delay_line
module glitch_filter_sva (
  input logic clk,
  input logic in,
  input logic out,
  input logic delay_line
);
  default clocking cb @(posedge clk); endclocking

  // Out must be the 1-cycle registered value of in
  assert property (disable iff ($isunknown($past(in))) out === $past(in));

  // Out must equal the internal flop at all times (combinational equivalence)
  assert property (@(*) out === delay_line);

  // Out can only change coincident with a rising clock edge
  assert property (@(posedge out or negedge out) $rose(clk));

  // Internal flop may only change on rising edge
  assert property (@(posedge delay_line or negedge delay_line) $rose(clk));

  // If sampled input is known, output must be known
  assert property (disable iff ($isunknown($past(in))) !$isunknown(out));

  // Coverage: observe both output transitions
  cover property ($rose(out));
  cover property ($fell(out));

  // Coverage: see an input glitch (two toggles) between clock edges while out holds
  cover property (@(negedge clk) $changed(in) ##[1:$] $changed(in) ##0 $stable(out));
endmodule

bind glitch_filter glitch_filter_sva u_glitch_filter_sva (
  .clk(clk),
  .in(in),
  .out(out),
  .delay_line(delay_line)
);