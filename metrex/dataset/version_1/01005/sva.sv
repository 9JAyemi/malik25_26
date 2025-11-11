// SVA for alu: concise, high-quality checks + coverage
module alu_sva
  #(parameter WIDTH = 8)
  ( input  wire [WIDTH-1:0] in_a,
    input  wire [WIDTH-1:0] in_b,
    input  wire [2:0]       opcode,
    input  wire [WIDTH-1:0] alu_out,
    input  wire             a_is_zero );

  // Golden model for combinational result
  function automatic [WIDTH-1:0] exp_out
    (input [WIDTH-1:0] a, input [WIDTH-1:0] b, input [2:0] op);
    case (op)
      3'b010: exp_out = a + b; // ADD
      3'b011: exp_out = a & b; // AND
      3'b100: exp_out = a ^ b; // XOR
      3'b101: exp_out = b;     // MOV B
      default: exp_out = a;    // MOV A (000,001,110,111,others)
    endcase
  endfunction

  // Combinational immediate assertions; #0 avoids delta-races
  always @* begin
    assert #0 (alu_out === exp_out(in_a,in_b,opcode))
      else $error("ALU mismatch: op=%0b a=%0h b=%0h out=%0h exp=%0h",
                  opcode, in_a, in_b, alu_out, exp_out(in_a,in_b,opcode));

    assert #0 (a_is_zero === (in_a == '0))
      else $error("a_is_zero mismatch: a=%0h a_is_zero=%b", in_a, a_is_zero);

    // No X/Z on outputs when inputs are known
    assert #0 ( $isunknown({in_a,in_b,opcode}) || !$isunknown({alu_out,a_is_zero}) )
      else $error("X/Z on outputs with known inputs: a=%0h b=%0h op=%0b out=%0h z=%b",
                  in_a, in_b, opcode, alu_out, a_is_zero);
  end

  // Lightweight functional coverage
  always @* begin
    // Hit every opcode
    cover (opcode == 3'b000);
    cover (opcode == 3'b001);
    cover (opcode == 3'b010);
    cover (opcode == 3'b011);
    cover (opcode == 3'b100);
    cover (opcode == 3'b101);
    cover (opcode == 3'b110);
    cover (opcode == 3'b111);

    // Exercise a_is_zero both ways
    cover (in_a == '0);
    cover (in_a != '0);

    // ADD overflow/wraparound (unsigned)
    cover (opcode == 3'b010 && (in_a + in_b) < in_a);
  end
endmodule

// Bind into DUT
bind alu alu_sva #(.WIDTH(WIDTH)) alu_sva_i (.*);