// SVA checker for simple_arithmetic
module simple_arithmetic_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] out
);

  // Golden model (8-bit truncation inherent in return type)
  function automatic logic [7:0] exp_out(input logic [7:0] a, b, input logic [1:0] op_i);
    case (op_i)
      2'b00: exp_out = a + b;
      2'b01: exp_out = a - b;
      2'b10: exp_out = a & b;
      default: exp_out = a | b; // 2'b11
    endcase
  endfunction

  // Inputs must be known; out must be known when inputs are known
  assert property (@(*) !$isunknown({A,B,op}));
  assert property (@(*) (!$isunknown({A,B,op})) |-> !$isunknown(out));

  // Functional correctness (single golden check covers all ops)
  assert property (@(*) out == exp_out(A,B,op))
    else $error("simple_arithmetic: out mismatch. A=%0h B=%0h op=%0b out=%0h exp=%0h",
                A, B, op, out, exp_out(A,B,op));

  // Purely combinational: if inputs stable, output stays stable
  assert property (@(*) $stable({A,B,op}) |-> $stable(out));

  // Op coverage
  cover property (@(*) op == 2'b00);
  cover property (@(*) op == 2'b01);
  cover property (@(*) op == 2'b10);
  cover property (@(*) op == 2'b11);

  // Corner-case coverage
  // Add overflow (carry out)
  cover property (@(*) (op==2'b00) && (({1'b0,A}+{1'b0,B})[8]));
  // Sub underflow (borrow)
  cover property (@(*) (op==2'b01) && (A < B));
  // AND yields zero
  cover property (@(*) (op==2'b10) && (out == 8'h00));
  // OR yields all ones
  cover property (@(*) (op==2'b11) && (out == 8'hFF));

endmodule

// Bind into the DUT
bind simple_arithmetic simple_arithmetic_sva sva_inst(.A(A), .B(B), .op(op), .out(out));