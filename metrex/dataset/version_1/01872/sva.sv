// SVA checker for modulo_operator
// Quality-focused, concise, full functional checks and targeted coverage
// Place in a separate file and bind to the DUT.

`ifndef MODULO_OPERATOR_SVA_SV
`define MODULO_OPERATOR_SVA_SV

module modulo_operator_sva #(parameter int W = 32)
(
  input logic [W-1:0] dividend,
  input logic [W-1:0] divisor,
  input logic [W-1:0] remainder
);
  // synthesis translate_off

  // Immediate assertions for combinational DUT; checks evaluate when signals change.
  always_comb begin
    // No X/Z on interface
    assert (!$isunknown(dividend) && !$isunknown(divisor) && !$isunknown(remainder))
      else $error("modulo_operator SVA: X/Z detected: dividend=%h divisor=%h remainder=%h",
                  dividend, divisor, remainder);

    if (divisor == '0) begin
      // Divide-by-zero behavior
      assert (remainder == '0)
        else $error("modulo_operator SVA: divisor==0 => remainder must be 0. dividend=%h remainder=%h",
                    dividend, remainder);
    end
    else begin
      // Functional correctness
      assert (remainder == (dividend % divisor))
        else $error("modulo_operator SVA: remainder mismatch. dividend=%h divisor=%h remainder=%h exp=%h",
                    dividend, divisor, remainder, (dividend % divisor));
      // Range invariant for modulo
      assert (remainder < divisor)
        else $error("modulo_operator SVA: remainder must be < divisor. remainder=%h divisor=%h",
                    remainder, divisor);
    end

    // Targeted coverage (immediate cover)
    cover (divisor == 0);
    cover (divisor != 0);
    cover (divisor != 0 && (dividend % divisor) == 0 && remainder == 0);          // exact division
    cover (divisor != 0 && dividend < divisor && remainder == dividend);          // remainder equals dividend
    cover (divisor != 0 && dividend == divisor && remainder == 0);                // equal operands
    cover (dividend == 0 && remainder == 0);                                      // zero dividend
    cover (divisor == 1 && remainder == 0);                                       // mod by 1
    cover (divisor == {W{1'b1}} && dividend == {W{1'b1}});                        // max values
  end

  // synthesis translate_on
endmodule


// Bind into the DUT
bind modulo_operator modulo_operator_sva #(.W(32)) u_modulo_operator_sva (
  .dividend(dividend),
  .divisor (divisor),
  .remainder(remainder)
);

`endif // MODULO_OPERATOR_SVA_SV