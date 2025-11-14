// SVA for adder4 — concise, high-quality checks and meaningful coverage

module adder4_sva (
  input  logic [3:0] wireA,
  input  logic [3:0] wireB,
  input  logic       carry_in,
  input  logic [3:0] sum,
  input  logic       carry_out
);
  logic [4:0] exp;

  always_comb begin
    // No X/Z on interface
    assert (!$isunknown({wireA, wireB, carry_in}))
      else $error("adder4: X/Z on inputs");
    assert (!$isunknown({sum, carry_out}))
      else $error("adder4: X/Z on outputs");

    // Functional correctness (full 5-bit result)
    exp = {1'b0, wireA} + {1'b0, wireB} + carry_in;
    assert ({carry_out, sum} == exp)
      else $error("adder4: result mismatch. expected=%0h got=%0h",
                  exp, {carry_out, sum});

    // Minimal but meaningful coverage
    // Carry behavior across both carry_in values
    cover (carry_in == 0 && carry_out == 0);
    cover (carry_in == 0 && carry_out == 1);
    cover (carry_in == 1 && carry_out == 0);
    cover (carry_in == 1 && carry_out == 1);

    // Extremes of modulo sum with/without overflow
    cover (sum == 4'h0 && carry_out == 0);
    cover (sum == 4'h0 && carry_out == 1);
    cover (sum == 4'hF && carry_out == 0);
    cover (sum == 4'hF && carry_out == 1);

    // Representative operand corners and carry generate/propagate cases
    cover (wireA == 4'h0 && wireB == 4'h0 && carry_in == 0);
    cover (wireA == 4'hF && wireB == 4'hF && carry_in == 0); // large generate
    cover (wireA == 4'hF && wireB == 4'h0 && carry_in == 1); // full propagate
    cover (wireA == 4'h8 && wireB == 4'h8 && carry_in == 0); // MSB generate
  end
endmodule

bind adder4 adder4_sva adder4_sva_i (
  .wireA(wireA),
  .wireB(wireB),
  .carry_in(carry_in),
  .sum(sum),
  .carry_out(carry_out)
);