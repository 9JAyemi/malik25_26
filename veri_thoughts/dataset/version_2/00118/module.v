module ripple_carry_adder (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

    wire [3:0] carry;
    assign carry[0] = cin;
    
    full_adder fa0(a[0], b[0], carry[0], sum[0], carry[1]);
    full_adder fa1(a[1], b[1], carry[1], sum[1], carry[2]);
    full_adder fa2(a[2], b[2], carry[2], sum[2], carry[3]);
    full_adder fa3(a[3], b[3], carry[3], sum[3], cout);

endmodule

module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign {cout, sum} = a + b + cin;

endmodule