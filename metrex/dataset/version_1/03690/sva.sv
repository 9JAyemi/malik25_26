// SVA for slow_clk: concise, high-quality checks and coverage
// Bind this to the DUT to access internals (count, sig_reg).

module slow_clk_sva #(parameter int unsigned TICKS = 27'd49_999_999)
(
  input  logic              clk,
  input  logic              slow_clk,
  input  logic [31:0]       count,
  input  logic              sig_reg
);
  localparam int unsigned T32 = TICKS;

  default clocking cb @(posedge clk); endclocking

  // Sanity / structural
  assert property (disable iff ($initstate) !$isunknown({slow_clk, sig_reg, count}));
  assert property (slow_clk == sig_reg);               // continuous assign holds each cycle
  assert property (count <= T32);                      // counter never exceeds terminal count

  // Counter behavior
  assert property (disable iff ($initstate) ($past(count) <  T32) |-> (count == $past(count)+1));
  assert property (disable iff ($initstate) ($past(count) == T32) |-> (count == 0));
  assert property (disable iff ($initstate) (count == 0)          |->  $past(count) == T32); // zero only after wrap

  // Output behavior: only toggles on wrap and must invert
  assert property (disable iff ($initstate) ($past(count) != T32) |-> (slow_clk == $past(slow_clk)));
  assert property (disable iff ($initstate) ($past(count) == T32) |-> (slow_clk == ~$past(slow_clk)));

  // Exact half-period: next toggle occurs after TICKS+1 cycles, with no earlier changes
  assert property ($changed(slow_clk) |=> !$changed(slow_clk)[*T32] ##1 $changed(slow_clk));

  // Coverage
  cover  property ($changed(slow_clk)); // see any toggle
  cover  property (disable iff ($initstate) ($past(count) == T32 && count == 0 && $changed(slow_clk))); // wrap event
  cover  property ($changed(slow_clk) ##(T32+1) $changed(slow_clk)); // observe expected half-period
endmodule

// Example bind (place in a package or a separate file included in simulation/formal)
// Assumes the DUT instance is of type 'slow_clk' and internal names match.
bind slow_clk slow_clk_sva #(.TICKS(TICKS)) slow_clk_sva_i (
  .clk     (clk),
  .slow_clk(slow_clk),
  .count   (count),
  .sig_reg (sig_reg)
);