module binary_adder (
    // inputs
    input [3:0] A,
    input [3:0] B,
    // outputs
    output [3:0] S,
    output Cout
);

wire [3:0] sum;
wire [3:0] carry;

full_adder fa0(
    .A(A[0]),
    .B(B[0]),
    .Cin(1'b0),
    .S(sum[0]),
    .Cout(carry[0])
);

full_adder fa1(
    .A(A[1]),
    .B(B[1]),
    .Cin(carry[0]),
    .S(sum[1]),
    .Cout(carry[1])
);

full_adder fa2(
    .A(A[2]),
    .B(B[2]),
    .Cin(carry[1]),
    .S(sum[2]),
    .Cout(carry[2])
);

full_adder fa3(
    .A(A[3]),
    .B(B[3]),
    .Cin(carry[2]),
    .S(sum[3]),
    .Cout(Cout)
);

assign S = sum;

endmodule

module full_adder (
    // inputs
    input A,
    input B,
    input Cin,
    // outputs
    output S,
    output Cout
);

wire xor1;
wire and1;
wire and2;

assign xor1 = A ^ B;
assign and1 = A & B;
assign and2 = xor1 & Cin;

assign S = xor1 ^ Cin;
assign Cout = and1 | and2;

endmodule