// SVA for calculator
// Bind this checker to the DUT instance
module calculator_sva (
  input  logic        reset_n,
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic [31:0] add,
  input  logic [31:0] sub,
  input  logic [31:0] mul,
  input  logic [31:0] div
);

  // Sample on any input activity; use ##0 to evaluate after NBA updates
  default clocking cb @(a or b or reset_n); endclocking

  // Reset behavior
  property p_reset_zero;
    1 ##0 (!reset_n) |-> (add===32'h0 && sub===32'h0 && mul===32'h0 && div===32'h0);
  endproperty
  assert property (p_reset_zero);

  // Functional correctness when out of reset (truncated arithmetic)
  property p_functional_combo;
    1 ##0 (reset_n) |-> (
      add == (a + b)[31:0] &&
      sub == (a - b)[31:0] &&
      mul == (a * b)[31:0] &&
      div == ((b!=32'h0) ? (a / b) : 32'h0)
    );
  endproperty
  assert property (p_functional_combo);

  // Outputs must be known when inputs are known and out of reset
  property p_no_x_when_inputs_known;
    1 ##0 (reset_n && !$isunknown({a,b})) |-> !$isunknown({add,sub,mul,div});
  endproperty
  assert property (p_no_x_when_inputs_known);

  // Guard against spurious output changes: any output change must coincide with input/reset change and still be functionally correct
  property p_no_spurious_output_change;
    @(add or sub or mul or div)
      1 ##0 (reset_n) |-> (
        $changed({a,b,reset_n}) &&
        add == (a + b)[31:0] &&
        sub == (a - b)[31:0] &&
        mul == (a * b)[31:0] &&
        div == ((b!=32'h0) ? (a / b) : 32'h0)
      );
  endproperty
  assert property (p_no_spurious_output_change);

  // Coverage: reset edges
  cover property (@(reset_n) $fell(reset_n));
  cover property (@(reset_n) $rose(reset_n));

  // Coverage: division by zero and non-zero cases
  cover property (1 ##0 (reset_n && (b==32'h0)));
  cover property (1 ##0 (reset_n && (b!=32'h0)));

  // Coverage: add carry-out, sub borrow, mul overflow
  cover property (1 ##0 (reset_n && ( (a + b) > 32'hFFFF_FFFF )));         // add carry (implicit via 33-bit add)
  cover property (1 ##0 (reset_n && ( a < b )));                            // sub borrow condition
  cover property (1 ##0 (reset_n && |((a * b)[63:32])));                    // mul overflow in upper 32 bits

endmodule

bind calculator calculator_sva calc_sva_i (
  .reset_n(reset_n),
  .a(a),
  .b(b),
  .add(add),
  .sub(sub),
  .mul(mul),
  .div(div)
);