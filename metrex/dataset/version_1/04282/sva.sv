// SVA checker for modulo_operator
module modulo_operator_sva (
  input logic [31:0] div,
  input logic [31:0] divisor,
  input logic [31:0] rem
);

  // Combinational, clockless immediate assertions and coverage
  always_comb begin
    // Known-in -> known-out
    if (!$isunknown({div, divisor})) begin
      assert (!$isunknown(rem)) else $error("rem has X/Z with known inputs");
    end

    if (divisor == 32'd0) begin
      assert (rem == 32'd0) else $error("divisor==0: rem must be 0");
    end else begin
      logic [31:0] q, prod, mat_rem;
      q       = div / divisor;
      prod    = q * divisor;
      mat_rem = div - prod;

      // Core correctness
      assert (rem == mat_rem) else $error("rem != div - (div/divisor)*divisor");
      assert (rem <  divisor) else $error("rem must be < divisor");
      assert (rem <= div)     else $error("rem must be <= div");

      // Corner cases
      if (div <  divisor) assert (rem == div) else $error("div<divisor: rem!=div");
      if (div == divisor) assert (rem == 0)   else $error("div==divisor: rem!=0");
      if (divisor == 32'd1) assert (rem == 0) else $error("divisor==1: rem!=0");

      // Power-of-two divisor
      if ((divisor & (divisor - 1)) == 0) begin
        assert (rem == (div & (divisor - 1))) else $error("pow2 divisor: rem!=div&(divisor-1)");
      end
    end

    // Functional coverage
    cover (divisor == 0);
    cover (divisor == 1);
    cover (div == 0 && divisor != 0);
    cover (div <  divisor && divisor != 0);
    cover (div == divisor && divisor != 0);
    cover (div >  divisor && divisor != 0);
    cover ((divisor != 0) && ((divisor & (divisor - 1)) == 0)); // power-of-two
    cover (rem == 0 && divisor != 0);
    cover (rem == div && divisor != 0 && div < divisor);
  end

endmodule

// Bind to DUT
bind modulo_operator modulo_operator_sva i_modulo_operator_sva (
  .div(div),
  .divisor(divisor),
  .rem(rem)
);