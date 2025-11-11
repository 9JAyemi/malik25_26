module arithmetic_module #(parameter WIDTH=32)
  (input [1:0] op,
   input [WIDTH-1:0] a,
   input [WIDTH-1:0] b,
   output reg [WIDTH-1:0] out);

  always @(*) begin
    case (op)
      2'b00: out = a + b; // addition
      2'b01: out = a - b; // subtraction
      2'b10: out = a * b; // multiplication
      2'b11: out = a / b; // division
    endcase
  end

endmodule