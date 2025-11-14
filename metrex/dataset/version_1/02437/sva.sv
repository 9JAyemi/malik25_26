// SVA checker for calculator. Bind this to the DUT.
module calculator_sva #(parameter int W=4) (
  input logic [W-1:0] A,
  input logic [W-1:0] B,
  input logic [1:0]   opcode,
  input logic [W-1:0] result
);

  // Functional correctness and X-propagation
  always_comb begin
    // opcode must be known (no X/Z)
    assert (!$isunknown(opcode)) else $error("opcode has X/Z: %b", opcode);

    unique case (opcode)
      2'b00: assert (result === (A + B)[W-1:0])
                else $error("ADD mismatch: A=%0h B=%0h exp=%0h got=%0h",
                            A,B,(A+B)[W-1:0],result);

      2'b01: assert (result === (A - B)[W-1:0])
                else $error("SUB mismatch: A=%0h B=%0h exp=%0h got=%0h",
                            A,B,(A-B)[W-1:0],result);

      2'b10: assert (result === (A * B)[W-1:0])
                else $error("MUL mismatch: A=%0h B=%0h exp=%0h got=%0h",
                            A,B,(A*B)[W-1:0],result);

      2'b11: begin
        if (B == '0) begin
          // Division by zero should produce Xs
          assert ($isunknown(result)) else
            $error("DIV by zero: result should be X, got %0h (A=%0h B=%0h)", result, A, B);
        end else begin
          assert (result === (A / B)[W-1:0])
                  else $error("DIV mismatch: A=%0h B=%0h exp=%0h got=%0h",
                              A,B,(A/B)[W-1:0],result);
        end
      end
    endcase

    // If all inputs are known and not div-by-zero, result must be known
    if (!$isunknown({A,B,opcode}) && !(opcode==2'b11 && B=='0))
      assert (!$isunknown(result)) else
        $error("Unexpected X/Z on result with known inputs: A=%0h B=%0h op=%b result=%0h",
               A,B,opcode,result);
  end

  // Concise functional coverage (immediate cover)
  always_comb begin
    // Opcode usage
    cover (opcode==2'b00);
    cover (opcode==2'b01);
    cover (opcode==2'b10);
    cover (opcode==2'b11);

    // Corner cases
    cover ((opcode==2'b00) && ( (A+B)[W] ));                       // add overflow (carry-out)
    cover ((opcode==2'b01) && (A < B));                            // sub borrow
    cover ((opcode==2'b10) && ( |((A*B)[2*W-1:W]) ));              // mul overflow (upper bits non-zero)
    cover ((opcode==2'b11) && (B!=0) && ((A % B) != 0));           // div with remainder
    cover ((opcode==2'b11) && (B==0));                             // div-by-zero attempted
  end

  // Optional: forbid divide-by-zero (enable if design intent requires)
  // always_comb assert (!(opcode==2'b11 && B=='0))
  //   else $error("Illegal: DIV by zero");

endmodule

// Bind to the DUT
bind calculator calculator_sva #(.W(4)) calc_sva_bind (
  .A(A), .B(B), .opcode(opcode), .result(result)
);