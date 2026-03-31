
module bitwise_operations (
  input [31:0] a,
  input [31:0] b,
  input [1:0] operation_select,
  input [4:0] shift_amount,
  output reg [31:0] result
);

  wire [31:0] and_result;
  wire [31:0] or_result;
  wire [31:0] xor_result;
  wire [31:0] shift_result;

  and_module and_inst (
    .a(a),
    .b(b),
    .and_result(and_result)
  );

  or_module or_inst (
    .a(a),
    .b(b),
    .or_result(or_result)
  );

  xor_module xor_inst (
    .a(a),
    .b(b),
    .xor_result(xor_result)
  );

  shift_left_module shift_inst (
    .a(a),
    .shift_amount(shift_amount),
    .shift_result(shift_result)
  );

  always @(*) begin
    case (operation_select)
      2'b00: result = and_result;
      2'b01: result = or_result;
      2'b10: result = xor_result;
      2'b11: result = shift_result;
    endcase
  end

endmodule
module and_module (
  input [31:0] a,
  input [31:0] b,
  output [31:0] and_result
);

  assign and_result = a & b;

endmodule
module or_module (
  input [31:0] a,
  input [31:0] b,
  output [31:0] or_result
);

  assign or_result = a | b;

endmodule
module xor_module (
  input [31:0] a,
  input [31:0] b,
  output [31:0] xor_result
);

  assign xor_result = a ^ b;

endmodule
module shift_left_module (
  input [31:0] a,
  input [4:0] shift_amount,
  output [31:0] shift_result
);

  assign shift_result = a << shift_amount;

endmodule