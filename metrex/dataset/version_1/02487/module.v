module bitwise_operations_with_adder (
  input [31:0] a,
  input [31:0] b,
  input [1:0] operation_select,
  input [4:0] shift_amount,
  input [15:0] adder_input,
  input select, 
  output reg [31:0] bitwise_result,
  output reg [31:0] adder_result
);

  // Bitwise operations module
  wire [31:0] and_result = a & b;
  wire [31:0] or_result = a | b;
  wire [31:0] xor_result = a ^ b;
  wire [31:0] shift_left_result = a << shift_amount;

  // Functional module
  wire [31:0] functional_result = and_result;
  always @(*) begin
    adder_result = functional_result + adder_input;
  end

  // Control logic module
  always @* begin
    case(operation_select)
      2'b00: bitwise_result = and_result;
      2'b01: bitwise_result = or_result;
      2'b10: bitwise_result = xor_result;
      2'b11: bitwise_result = shift_left_result;
    endcase

    if(select) begin
      bitwise_result = functional_result;
    end
  end

endmodule