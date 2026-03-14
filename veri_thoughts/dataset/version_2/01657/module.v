
module multiplier(
    input [3:0] A,
    input [3:0] B,
    output [7:0] out
);

assign out = A * B;

endmodule

module top_module (
    input [3:0] A,
    input [3:0] B,
    output [7:0] out
);

multiplier mult(A, B, out);

endmodule
