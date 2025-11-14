// SVA checker for simple_calculator
// Bind this to the DUT instance(s).
module simple_calculator_sva (simple_calculator dut);

  // Local mirrors with same arithmetic semantics
  logic signed [31:0] op1_s, op2_s, exp32;
  logic signed [63:0] prod64;

  always_comb begin
    op1_s = dut.operands[31:0];
    op2_s = dut.operands[63:32];

    // Golden expected (match DUT truncation/sign rules)
    unique case (dut.operation)
      2'b00: exp32 = op1_s + op2_s;                       // add (wrap/trunc to 32)
      2'b01: exp32 = op1_s - op2_s;                       // sub (wrap/trunc to 32)
      2'b10: exp32 = op1_s * op2_s;                       // mul (lower 32 of 64)
      2'b11: exp32 = (op2_s == 0) ? 'x : (op1_s / op2_s); // div; X on /0
      default: exp32 = 'x;
    endcase

    // Functional equivalence (4-state compare to allow X checking for /0)
    assert (dut.result === exp32)
      else $error("simple_calculator: result mismatch. op=%b op1=%0d op2=%0d got=%0d exp=%0d",
                  dut.operation, op1_s, op2_s, dut.result, exp32);

    // Known-result when inputs known and not div-by-zero
    if (!$isunknown(dut.operation) && !$isunknown(dut.operands) &&
        !(dut.operation == 2'b11 && op2_s == 0)) begin
      assert (!$isunknown(dut.result))
        else $error("simple_calculator: unexpected X/Z on result for known inputs");
    end

    // Division-by-zero must yield unknown result
    if (dut.operation == 2'b11 && op2_s == 0) begin
      assert ($isunknown(dut.result))
        else $error("simple_calculator: division by zero should produce X result");
    end
  end

  // Lightweight functional coverage
  always_comb begin
    cover (dut.operation == 2'b00);
    cover (dut.operation == 2'b01);
    cover (dut.operation == 2'b10);
    cover (dut.operation == 2'b11);
    cover (dut.operation == 2'b11 && op2_s == 0);               // div by zero
    cover (dut.operation == 2'b11 && op2_s != 0 &&
           ((op1_s < 0) ^ (op2_s < 0)));                        // signed div with sign change

    // Signed add/sub overflow scenarios
    cover (dut.operation == 2'b00 &&
           (op1_s[31] == op2_s[31]) && (dut.result[31] != op1_s[31]));
    cover (dut.operation == 2'b01 &&
           (op1_s[31] != op2_s[31]) && (dut.result[31] != op1_s[31]));

    // Multiply truncation overflow (upper bits not sign-extension of bit31)
    prod64 = op1_s * op2_s;
    cover (dut.operation == 2'b10 &&
           (prod64[63:32] != {32{prod64[31]}}));
  end

endmodule

// Bind to all instances of simple_calculator
bind simple_calculator simple_calculator_sva u_simple_calculator_sva(.dut(this));