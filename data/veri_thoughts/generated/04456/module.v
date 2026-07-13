
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input CI,
    output [3:0] C,
    output CO
);

wire [3:0] sum;
wire [4:0] carry;

// Full adder
assign sum[0] = A[0] ^ B[0] ^ CI;
assign carry[0] = (A[0] & B[0]) | (A[0] & CI) | (B[0] & CI);

assign sum[1] = A[1] ^ B[1] ^ carry[0];
assign carry[1] = (A[1] & B[1]) | (A[1] & carry[0]) | (B[1] & carry[0]);

assign sum[2] = A[2] ^ B[2] ^ carry[1];
assign carry[2] = (A[2] & B[2]) | (A[2] & carry[1]) | (B[2] & carry[1]);

assign sum[3] = A[3] ^ B[3] ^ carry[2];
assign carry[3] = (A[3] & B[3]) | (A[3] & carry[2]) | (B[3] & carry[2]);

assign CO = carry[3];
assign C = sum;

endmodule