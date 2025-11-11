// SVA checker for PLL divider
module PLL_SVA #(parameter int DIV_FACTOR = 2)
(
  input  logic        inclk0,
  input  logic        c0,
  input  logic [31:0] counter,
  input  logic        clk_out
);

  // Start checking after first observed toggle to avoid X/initialization artifacts
  logic init_done;
  always @(posedge inclk0) init_done <= init_done || (c0 != $past(c0));

  default clocking cb @(posedge inclk0); endclocking
  default disable iff (!init_done);

  // Parameter sanity
  initial begin
    assert (DIV_FACTOR >= 1)
      else $error("PLL_SVA: DIV_FACTOR must be >= 1");
    assert ((DIV_FACTOR-1) <= 32'hFFFF_FFFF)
      else $error("PLL_SVA: DIV_FACTOR does not fit 32-bit counter");
  end

  // X checks (after init_done)
  assert property (!$isunknown({c0, clk_out, counter})));

  // Output is assigned from clk_out
  assert property (c0 == clk_out);

  // Counter range
  assert property (counter < DIV_FACTOR);

  // Non-terminal: counter increments by 1, output stable
  assert property ((counter != DIV_FACTOR-1) |=> (counter == $past(counter)+1) && $stable(c0));

  // Terminal: on DIV_FACTOR-1, next cycle counter resets to 0 and output toggles
  assert property ((counter == DIV_FACTOR-1) |=> (counter == 0) && (c0 != $past(c0)));

  // Toggles only occur when previous cycle was terminal
  assert property ((c0 != $past(c0)) |-> $past(counter) == DIV_FACTOR-1);

  // Spacing: consecutive toggles are exactly DIV_FACTOR input cycles apart, with none in between
  sequence toggle; c0 != $past(c0); endsequence
  assert property (toggle |=> (!toggle)[*(DIV_FACTOR-1)] ##1 toggle);

  // Coverage
  cover property (toggle);                                   // saw a toggle
  cover property (toggle ##(DIV_FACTOR) toggle);             // correct spacing between toggles
  cover property ((counter == DIV_FACTOR-1) ##1 (counter == 0) and (c0 != $past(c0))); // terminal event

endmodule

// Bind into DUT (accesses internal signals counter and clk_out)
bind PLL PLL_SVA #(.DIV_FACTOR(DIV_FACTOR)) pll_sva_i (
  .inclk0(inclk0),
  .c0(c0),
  .counter(counter),
  .clk_out(clk_out)
);