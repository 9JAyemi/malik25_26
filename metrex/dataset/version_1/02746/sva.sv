// SVA for calculator
// Bind these assertions to the DUT
bind calculator calculator_sva u_calculator_sva(.a(a), .b(b), .op(op), .result(result));

// Assertion module
module calculator_sva (
  input  signed [7:0] a,
  input  signed [7:0] b,
  input        [1:0] op,
  input  signed [7:0] result
);
  // Helper expressions (match Verilog arithmetic widths)
  logic signed [8:0]  add9, sub9;
  logic signed [15:0] mul16;
  logic signed [7:0]  div8;

  assign add9  = $signed({a[7],a}) + $signed({b[7],b});
  assign sub9  = $signed({a[7],a}) - $signed({b[7],b});
  assign mul16 = $signed(a) * $signed(b);
  assign div8  = (b != 0) ? ($signed(a) / $signed(b)) : 'x;

  // Combinational, immediate SVA checks and coverage
  always @* begin
    // No X/Z on IOs
    assert (!$isunknown({a,b,op})) else $error("calculator: X/Z on inputs");
    assert (!$isunknown(result))    else $error("calculator: X/Z on result");

    // Functional correctness per op (bit-accurate, including truncation)
    unique case (op)
      2'b00: assert (result === add9[7:0]) else $error("ADD mismatch exp=%0d got=%0d", $signed(add9[7:0]), result);
      2'b01: assert (result === sub9[7:0]) else $error("SUB mismatch exp=%0d got=%0d", $signed(sub9[7:0]), result);
      2'b10: assert (result === mul16[7:0]) else $error("MUL mismatch exp=%0d got=%0d", $signed(mul16[7:0]), result);
      2'b11: begin
        if (b == 0)
          assert (result === 8'hFF) else $error("DIV0 mismatch exp=0xFF got=%0h", result);
        else
          assert (result === div8) else $error("DIV mismatch exp=%0d got=%0d", div8, result);
      end
    endcase

    // Purely combinational: output changes only when inputs change
    if ($stable({a,b,op})) assert ($stable(result)) else $error("Result changed without input change");

    // Basic op coverage
    cover (op == 2'b00);
    cover (op == 2'b01);
    cover (op == 2'b10);
    cover (op == 2'b11);

    // Corner-case coverage
    cover (op == 2'b11 && b == 0);  // division by zero path
    cover (op == 2'b10 && (mul16 != {{8{mul16[7]}}, mul16[7:0]})); // mul truncation occurred
    cover (op == 2'b00 && (add9[8] != add9[7])); // add overflow (signed)
    cover (op == 2'b01 && (sub9[8] != sub9[7])); // sub overflow (signed)
    cover (op == 2'b11 && b != 0 && (a[7] ^ b[7]) == 0); // div same signs
    cover (op == 2'b11 && b != 0 && (a[7] ^ b[7]) == 1); // div opposite signs
  end
endmodule