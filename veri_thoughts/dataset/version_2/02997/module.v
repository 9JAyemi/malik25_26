module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    wire c0, c1, c2, c3; // intermediate carry signals

    // full adder for bit 0
    full_adder fa0 (.a(A[0]), .b(B[0]), .cin(Cin), .s(Sum[0]), .cout(c0));

    // full adder for bit 1
    full_adder fa1 (.a(A[1]), .b(B[1]), .cin(c0), .s(Sum[1]), .cout(c1));

    // full adder for bit 2
    full_adder fa2 (.a(A[2]), .b(B[2]), .cin(c1), .s(Sum[2]), .cout(c2));

    // full adder for bit 3
    full_adder fa3 (.a(A[3]), .b(B[3]), .cin(c2), .s(Sum[3]), .cout(c3));

    // carry-out calculation
    assign Cout = (A[3] & B[3]) | (c2 & (A[3] | B[3])) | (c1 & c0);

endmodule


module full_adder (
    input a,
    input b,
    input cin,
    output s,
    output cout
);

    wire w1, w2, w3;

    // XOR gate for sum
    assign s = a ^ b ^ cin;

    // AND gate for carry-out
    assign w1 = a & b;
    assign w2 = a & cin;
    assign w3 = b & cin;
    assign cout = w1 | w2 | w3;

endmodule