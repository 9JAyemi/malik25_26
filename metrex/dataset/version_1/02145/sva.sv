// SVA for counter. Bind this module to the DUT.
// Focus: async reset behavior, next-state function, and key coverage.

module counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  modulus,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Async reset clears immediately
  assert property (@(posedge reset) count == 4'h0)
    else $error("count must clear to 0 on async reset");

  // While reset is asserted, count is 0 on every clk edge
  assert property (reset |-> count == 4'h0)
    else $error("count must be 0 while reset is high");

  // Next-state: not at modulus -> increment by 1 with 4-bit wrap
  property p_next_inc;
    bit [3:0] c, m;
    disable iff (reset)
      ( (c = count, m = modulus, c != m) )
      |=> ( (c == 4'hF) ? (count == 4'h0) : (count == c + 4'd1) );
  endproperty
  assert property (p_next_inc)
    else $error("Illegal increment transition");

  // Next-state: at modulus -> wrap to 0
  property p_next_wrap;
    bit [3:0] c, m;
    disable iff (reset)
      ( (c = count, m = modulus, c == m) )
      |=> (count == 4'h0);
  endproperty
  assert property (p_next_wrap)
    else $error("Must wrap to 0 when count == modulus");

  // --------------------
  // Functional coverage
  // --------------------

  // Observe async reset event
  cover property (@(posedge reset) 1'b1);

  // Normal increment (not at modulus, not at 4'hF)
  property cov_inc;
    bit [3:0] c, m;
    disable iff (reset)
      ( (c = count, m = modulus, c != m && c != 4'hF) )
      |=> (count == c + 4'd1);
  endproperty
  cover property (cov_inc);

  // Increment wrap: 4'hF -> 0 when not at modulus
  property cov_inc_wrap;
    bit [3:0] c, m;
    disable iff (reset)
      ( (c = count, m = modulus, c != m && c == 4'hF) )
      |=> (count == 4'h0);
  endproperty
  cover property (cov_inc_wrap);

  // Equality wrap: count == modulus -> 0 (any modulus)
  property cov_eq_wrap;
    bit [3:0] c, m;
    disable iff (reset)
      ( (c = count, m = modulus, c == m) )
      |=> (count == 4'h0);
  endproperty
  cover property (cov_eq_wrap);

  // Modulus = 0 hold at 0 once reached
  cover property (disable iff (reset) (count == 4'h0 && modulus == 4'h0) |=> (count == 4'h0));

  // Modulus = 15 wrap behavior
  cover property (disable iff (reset) (count == 4'hF && modulus == 4'hF) |=> (count == 4'h0));

  // Startup step: 0 -> 1 when modulus > 0
  cover property (disable iff (reset) (count == 4'h0 && modulus != 4'h0) |=> (count == 4'h1));

endmodule

// Example bind (place in a package or a separate file compiled with the DUT)
// bind counter counter_sva u_counter_sva(.clk(clk), .reset(reset), .modulus(modulus), .count(count));