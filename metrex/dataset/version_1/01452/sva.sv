// SVA checker for calculator. Bind this to the DUT.
module calculator_sva (
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [1:0] op,
  input  logic [7:0] result
);

  // Use input changes as a sampling event for cover properties
  default clocking cb @(a or b or op); endclocking

  // Immediate assertions avoid race with combinational updates
  always_comb begin
    // op must be known to avoid latchy behavior from case without default
    assert (!$isunknown(op)) else $error("calculator: op contains X/Z");

    // If all inputs known, check function and X-propagation
    if (!$isunknown({a,b,op})) begin
      // Disallow divide-by-zero
      if (op == 2'b11) assert (b != 8'd0) else $error("calculator: divide-by-zero");

      unique case (op)
        2'b00: assert (result == ((a + b) & 8'hFF)) else
               $error("calculator: add mismatch exp=%0d got=%0d", (a+b)&8'hFF, result);
        2'b01: assert (result == ((a - b) & 8'hFF)) else
               $error("calculator: sub mismatch exp=%0d got=%0d", (a-b)&8'hFF, result);
        2'b10: assert (result == ((a * b) & 8'hFF)) else
               $error("calculator: mul mismatch exp=%0d got=%0d", (a*b)&8'hFF, result);
        2'b11: if (b != 0) assert (result == (a / b)) else
               $error("calculator: div mismatch exp=%0d got=%0d", (b==0)?'x:(a/b), result);
      endcase

      // With known, legal inputs, result must be known
      if (!(op == 2'b11 && b == 0))
        assert (!$isunknown(result)) else $error("calculator: result has X/Z");
    end
  end

  // Functional coverage
  cover property (op == 2'b00);
  cover property (op == 2'b01);
  cover property (op == 2'b10);
  cover property (op == 2'b11);

  // Interesting corner cases
  cover property (op == 2'b00 && ({1'b0,a} + {1'b0,b}) > 9'h0FF); // add overflow
  cover property (op == 2'b01 && a < b);                          // sub underflow
  cover property (op == 2'b10 && (a * b) > 16'(8'hFF));           // mul overflow
  cover property (op == 2'b11 && b != 0 && (a % b) != 0);         // div with remainder
  cover property (op == 2'b11 && b != 0 && (a % b) == 0);         // exact division
  cover property (op == 2'b11 && b == 0);                         // divide-by-zero attempt

endmodule

// Bind into the DUT
bind calculator calculator_sva i_calculator_sva (
  .a(a), .b(b), .op(op), .result(result)
);