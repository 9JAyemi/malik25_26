
module xor_module (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

localparam WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

wire carry, carry_sign;
wire [WIDTH-1:0] A_buf, B_buf;
assign A_buf = A_SIGNED ? {{WIDTH-A_WIDTH{A_buf[A_WIDTH-1]}}, A} : A;
assign B_buf = B_SIGNED ? {{WIDTH-B_WIDTH{B_buf[B_WIDTH-1]}}, B} : B;

assign Y = ~(A_buf ^ B_buf);

endmodule
