// SVA for divider. Bind this to the DUT.
// Focus: mathematical identity, X-prop on divide-by-zero, sign/magnitude rules, and essential coverage.

module divider_sva #(
  parameter int n = 8,
  parameter int SIGNED_DIV = 1
)(
  input  signed [n-1:0] dividend,
  input  signed [n-1:0] divisor,
  input  signed [n-1:0] quotient,
  input  signed [n-1:0] remainder
);

  function automatic signed [n-1:0] abs_s (input signed [n-1:0] x);
    abs_s = (x < 0) ? -x : x;
  endfunction

  localparam signed [n-1:0] MIN_NEG = {1'b1,{(n-1){1'b0}}};

  // Combinational immediate assertions
  always @* begin
    // Divide-by-zero must generate X on outputs; otherwise no X allowed
    if (!$isunknown(divisor) && (divisor == 0)) begin
      assert ($isunknown(quotient)) else $error("divider: quotient must be X on divide-by-zero");
      assert ($isunknown(remainder)) else $error("divider: remainder must be X on divide-by-zero");
    end

    if (!$isunknown(divisor) && (divisor != 0)) begin
      assert (!$isunknown(quotient) && !$isunknown(remainder))
        else $error("divider: outputs must not be X when divisor!=0");

      // Basic identity (widened to 2n to avoid overflow)
      automatic logic signed [2*n-1:0] A = $signed(dividend);
      automatic logic signed [2*n-1:0] B = $signed(divisor);
      automatic logic signed [2*n-1:0] Q = $signed(quotient);
      automatic logic signed [2*n-1:0] R = $signed(remainder);
      assert (A == Q*B + R)
        else $error("divider: identity A==Q*B+R violated (A=%0d,B=%0d,Q=%0d,R=%0d)", A,B,Q,R);

      // Remainder magnitude bound
      assert (abs_s(remainder) < abs_s(divisor))
        else $error("divider: |remainder| must be < |divisor|");

      // Zero dividend -> zero quotient and remainder
      if (dividend == '0) begin
        assert (quotient == '0 && remainder == '0)
          else $error("divider: dividend==0 => quotient==0 and remainder==0");
      end

      // Divisor == +1 -> quotient==dividend, remainder==0 (both modes)
      if (divisor == $signed(1)) begin
        assert (quotient == dividend && remainder == '0)
          else $error("divider: divisor==+1 => quotient==dividend, remainder==0");
      end

      if (SIGNED_DIV) begin
        // Signed mode: remainder sign follows dividend (or zero)
        assert ((remainder == '0) || (remainder[n-1] == dividend[n-1]))
          else $error("divider(signed): remainder sign must match dividend sign");
        // Signed mode: quotient sign = sign(dividend) XOR sign(divisor), except 0
        assert ((quotient == '0) || (quotient[n-1] == (dividend[n-1] ^ divisor[n-1])))
          else $error("divider(signed): quotient sign incorrect");
      end
      else begin
        // Unsigned mode: require non-negative inputs (environment assumption)
        assume (dividend[n-1] == 0 && divisor[n-1] == 0);
        // Unsigned mode: outputs non-negative and remainder < divisor
        assert (quotient[n-1] == 0 && remainder[n-1] == 0)
          else $error("divider(unsigned): outputs must be non-negative");
        assert ($unsigned(remainder) < $unsigned(divisor))
          else $error("divider(unsigned): remainder < divisor violated");
      end
    end
  end

  // Lightweight functional coverage
  always @* begin
    cover (!$isunknown(divisor) && divisor == 0);
    cover (!$isunknown(divisor) && divisor != 0 && SIGNED_DIV && dividend[n-1]==0 && divisor[n-1]==0); // +/+
    cover (!$isunknown(divisor) && divisor != 0 && SIGNED_DIV && dividend[n-1]==1 && divisor[n-1]==0); // -/+
    cover (!$isunknown(divisor) && divisor != 0 && SIGNED_DIV && dividend[n-1]==0 && divisor[n-1]==1); // +/-
    cover (!$isunknown(divisor) && divisor != 0 && SIGNED_DIV && dividend[n-1]==1 && divisor[n-1]==1); // -/-
    cover (!$isunknown(divisor) && divisor != 0 && remainder == 0); // exact division
    cover (!$isunknown(divisor) && divisor != 0 && (divisor == 1 || divisor == -1));
    cover (!$isunknown(divisor) && divisor != 0 && (dividend == MIN_NEG || divisor == MIN_NEG));
  end

endmodule

// Bind into the DUT (assumes tool supports passing bound parameter values)
bind divider divider_sva #(.n(n), .SIGNED_DIV(signed_div))
  divider_sva_i (
    .dividend(dividend),
    .divisor(divisor),
    .quotient(quotient),
    .remainder(remainder)
  );