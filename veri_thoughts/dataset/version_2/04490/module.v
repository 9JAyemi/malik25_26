module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign {cout, sum} = a + b + cin;

endmodule

module ripple_adder(
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] s,
    output cout
);

    wire [3:0] carry;

    full_adder fa0(a[0], b[0], cin, s[0], carry[0]);
    full_adder fa1(a[1], b[1], carry[0], s[1], carry[1]);
    full_adder fa2(a[2], b[2], carry[1], s[2], carry[2]);
    full_adder fa3(a[3], b[3], carry[2], s[3], cout);

endmodule