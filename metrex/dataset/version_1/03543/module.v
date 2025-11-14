module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    // Define internal signals
    wire [3:0] sum;
    wire [3:0] carry;

    // Generate the sum and carry signals
    full_adder fa0(A[0], B[0], Cin, sum[0], carry[0]);
    full_adder fa1(A[1], B[1], carry[0], sum[1], carry[1]);
    full_adder fa2(A[2], B[2], carry[1], sum[2], carry[2]);
    full_adder fa3(A[3], B[3], carry[2], sum[3], Cout);

    // Assign the sum signal to the output port
    assign S = sum;

endmodule

module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    // Define internal signals
    wire sum;
    wire Cout1;
    wire Cout2;

    // Generate the sum and carry signals
    xor(sum, A, B);
    xor(S, sum, Cin);
    and(Cout1, A, B);
    and(Cout2, sum, Cin);
    or(Cout, Cout1, Cout2);

endmodule