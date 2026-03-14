module mult_module (A, B, enable, Z);
input [7:0] A ;
input [7:0] B ;
input enable ;
output [15:0] Z ;

wire [15:0] result;

// Multiplication operation
assign result = A * B;

// Output logic
assign Z = enable ? result : 16'b0;

endmodule