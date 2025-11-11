// SVA for calculator
// Bindable checker with immediate assertions (no clock required)
module calculator_sva(input logic [7:0] a, b,
                      input logic [2:0] op,
                      input logic [15:0] res);

  // Functional correctness (match Verilog sizing semantics)
  always_comb begin
    // ADD: 9-bit result zero-extended to 16
    assert (!(op==3'b000) || (res == {7'b0, (a + b)})) else $error("ADD mismatch");
    // SUB: 9-bit result zero-extended to 16
    assert (!(op==3'b001) || (res == {7'b0, (a - b)})) else $error("SUB mismatch");
    // MUL: 16-bit result
    assert (!(op==3'b010) || (res == (a * b))) else $error("MUL mismatch");
    // DIV: 8-bit result zero-extended to 16 (only when b!=0)
    assert (!((op==3'b011) && (b!=8'b0)) || (res == {8'b0, (a / b)})) else $error("DIV mismatch");
    // DEFAULT or unknown op -> res == 0
    assert (!((op inside {[3'b100:3'b111]}) || $isunknown(op)) || (res == 16'b0)) else $error("DEFAULT mismatch");

    // Illegal/robustness checks
    assert (!(op==3'b011) || (b!=8'b0)) else $error("Divide-by-zero illegal");
    assert ((op==3'b011 && b==8'b0) || !$isunknown(res)) else $error("Unexpected X/Z on res");
  end

  // Functional coverage (key scenarios)
  always_comb begin
    cover (op==3'b000);                             // add
    cover (op==3'b001);                             // sub
    cover (op==3'b010);                             // mul
    cover (op==3'b011 && b!=0);                     // div legal
    cover (op inside {[3'b100:3'b111]});            // default
    cover (op==3'b000 && ((a + b) > 8'hFF));        // add carry-out
    cover (op==3'b001 && (a < b));                  // sub borrow
    cover (op==3'b010 && a==8'hFF && b==8'hFF);     // mul max*max
    cover (op==3'b011 && b==8'h00);                 // div-by-zero attempt
  end

endmodule

// Bind into the DUT
bind calculator calculator_sva u_calculator_sva(.a(a), .b(b), .op(op), .res(res));