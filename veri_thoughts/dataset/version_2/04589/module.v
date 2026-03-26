
module bitwise_operations (
  input [31:0] a,
  input [31:0] b,
  input [1:0] operation_select,
  input [4:0] shift_amount,
  output [31:0] result
);

  wire [31:0] and_output;
  wire [31:0] or_output;
  wire [31:0] xor_output;
  wire [31:0] shifted_a;
  
  and_module and_inst(
    .a(a),
    .b(b),
    .result(and_output)
  );
  
  or_module or_inst(
    .a(a),
    .b(b),
    .result(or_output)
  );
  
  xor_module xor_inst(
    .a(a),
    .b(b),
    .result(xor_output)
  );
  
  assign shifted_a = a << shift_amount;
  
  reg [31:0] temp;
  
  always @(*) begin
    case(operation_select)
      2'b00: temp = and_output & or_output ^ shifted_a;
      2'b01: temp = and_output;
      2'b10: temp = or_output;
      2'b11: temp = xor_output;
    endcase
  end
  
  assign result = temp;
  
endmodule
module and_module (
  input [31:0] a,
  input [31:0] b,
  output [31:0] result
);
  
  assign result = a & b;
  
endmodule
module or_module (
  input [31:0] a,
  input [31:0] b,
  output [31:0] result
);
  
  assign result = a | b;
  
endmodule
module xor_module (
  input [31:0] a,
  input [31:0] b,
  output [31:0] result
);
  
  assign result = a ^ b;
  
endmodule