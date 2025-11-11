
module add_sub_shift (
    input [3:0] A,
    input [3:0] B,
    input mode,
    input DIR,
    input [1:0] AMT,
    output [3:0] Q
);

reg [3:0] shifted_A;
wire [3:0] shifted_B;

// Barrel shifter module
barrel_shifter bs(
    .A(A),
    .B(B),
    .DIR(DIR),
    .AMT(AMT),
    .Q(shifted_A),
    .fill(shifted_B)
);

// Adder-subtractor module
adder_subtractor as(
    .A(shifted_A),
    .B(shifted_B),
    .mode(mode),
    .Q(Q)
);

endmodule
module barrel_shifter (
    input [3:0] A,
    input [3:0] B,
    input DIR,
    input [1:0] AMT,
    output [3:0] Q,
    output [3:0] fill
);

wire [3:0] shifted_A;

assign shifted_A = (DIR) ? {B[3-AMT[1:0]:0], A[3:AMT[1:0]]} : {A[AMT[1:0]-1:0], B[3:AMT[1:0]]};

assign Q = shifted_A;
assign fill = (DIR) ? {B[3:AMT[1:0]], shifted_A[AMT[1:0]-1:0]} : {A[AMT[1:0]-1:0], shifted_A[AMT[1:0]-1:0]};

endmodule
module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input mode,
    output [3:0] Q
);

assign Q = (mode) ? A - B : A + B;

endmodule