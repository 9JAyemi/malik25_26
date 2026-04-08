
module two_bit_adder (
    input [1:0] A,
    input [1:0] B,
    input cin,
    output [1:0] sum,
    output cout
);

    // Local signals
    wire c1;
    wire [1:0] s1;

    //  Name  Output  Other arguments
    full_adder U0 (.COUT(c1), .SUM(s1[0]), .A(A[0]), .B(B[0]), .CI(cin));
    full_adder U1 (.COUT(cout), .SUM(s1[1]), .A(A[1]), .B(B[1]), .CI(c1));
    assign sum = {s1[1], s1[0]};

endmodule

module full_adder (
    output COUT,
    output SUM,
    input A,
    input B,
    input CI
);
    assign {COUT, SUM} = A + B + CI;

endmodule
