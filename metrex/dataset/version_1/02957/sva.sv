// SVA for clock_divider. Bind this to the DUT.
// Quality-focused, concise checks and coverage.

module clock_divider_sva #(parameter int CLKDIV = 2) (
  input  logic        clkin,
  input  logic        reset,     // active-low async
  input  logic        clkoutp,
  input  logic        clkoutn,
  input  logic        clkbase,   // internal
  input  logic [6:0]  clkcnt     // internal
);

  // Parameter sanity relative to 7-bit counter
  initial begin
    assert (CLKDIV >= 1 && CLKDIV <= 128)
      else $error("clkdiv out of supported range for 7-bit counter: %0d", CLKDIV);
  end

  // Async reset immediately clears state
  property p_async_reset_clears;
    @(negedge reset) 1 |-> ##0 (clkcnt == 0 && clkbase == 0);
  endproperty
  assert property (p_async_reset_clears);

  // Outputs are well-formed and complementary
  property p_out_is_base_compl;
    @(posedge clkin or negedge reset)
      (clkoutp == ~clkbase) && (clkoutn == clkbase) && (clkoutp == ~clkoutn);
  endproperty
  assert property (p_out_is_base_compl);

  // No X/Z on key signals when not in reset
  assert property (@(posedge clkin) reset |-> !$isunknown({clkbase, clkcnt, clkoutp, clkoutn}));

  // Counter stays within 0 .. CLKDIV-1 when running
  assert property (@(posedge clkin) disable iff (!reset) clkcnt < CLKDIV);

  // Normal counting: increment when not at terminal count; clkbase holds
  assert property (@(posedge clkin) disable iff (!reset)
                     $past(reset) && ($past(clkcnt) != (CLKDIV-1))
                   |-> (clkcnt == $past(clkcnt)+1) && (clkbase == $past(clkbase)));

  // Rollover: when terminal count seen, next cycle cnt->0 and base toggles
  assert property (@(posedge clkin) disable iff (!reset)
                     $past(reset) && ($past(clkcnt) == (CLKDIV-1))
                   |-> (clkcnt == 0) && (clkbase != $past(clkbase)));

  // Toggle occurs only on rollover
  assert property (@(posedge clkin) disable iff (!reset)
                     $changed(clkbase) |-> $past(clkcnt) == (CLKDIV-1));

  // Divide ratio: after any toggle, hold for exactly (CLKDIV-1) cycles, then toggle
  assert property (@(posedge clkin) disable iff (!reset)
                     $changed(clkbase) |-> !$changed(clkbase)[*(CLKDIV-1)] ##1 $changed(clkbase));

  // Coverage: see rollover, and two consecutive toggles at correct spacing
  cover property (@(posedge clkin) disable iff (!reset)
                    (clkcnt == (CLKDIV-1)) ##1 (clkcnt == 0));

  cover property (@(posedge clkin) disable iff (!reset)
                    $changed(clkbase) ##1 !$changed(clkbase)[*(CLKDIV-1)] ##1 $changed(clkbase));

endmodule

// Example bind (tool-dependent). Place in a package or a separate SV file:
// bind clock_divider clock_divider_sva #(.CLKDIV(clkdiv)) u_clock_divider_sva (
//   .clkin   (clkin),
//   .reset   (reset),
//   .clkoutp (clkoutp),
//   .clkoutn (clkoutn),
//   .clkbase (clkbase),
//   .clkcnt  (clkcnt)
// );