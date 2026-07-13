
module full_adder (
    input  a,
    input  b,
    input  cin,
    output cout,
    output sum
);

    wire ps, pc; // pc2 is not used

    half_adder ha1 (
        .A(a),
        .B(b),
        .SUM(ps),
        .COUT(pc)
    );

    half_adder ha2 (
        .A(ps),
        .B(cin),
        .SUM(sum),
        .COUT(cout)
    );

endmodule

module half_adder(
    input A,
    input B,
    output SUM,
    output COUT
    );

    assign SUM = A ^ B;
    assign COUT = A & B;

endmodule
