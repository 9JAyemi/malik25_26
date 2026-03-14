
module four_bit_adder(
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] s,
    output cout
);

    wire [3:0] sum;
    wire cout0, cout1, cout2;
    
    // full adder for least significant bit
    full_adder fa0(
        .a(a[0]),
        .b(b[0]),
        .cin(cin),
        .s(sum[0]),
        .cout(cout0)
    );
    
    // full adder for second least significant bit
    full_adder fa1(
        .a(a[1]),
        .b(b[1]),
        .cin(cout0),
        .s(sum[1]),
        .cout(cout1)
    );
    
    // full adder for third least significant bit
    full_adder fa2(
        .a(a[2]),
        .b(b[2]),
        .cin(cout1),
        .s(sum[2]),
        .cout(cout2)
    );
    
    // full adder for most significant bit
    full_adder fa3(
        .a(a[3]),
        .b(b[3]),
        .cin(cout2),
        .s(sum[3]),
        .cout(cout)
    );
    
    assign s = sum;

endmodule
module full_adder(
    input a,
    input b,
    input cin,
    output s,
    output cout
);

    wire sum1, sum2, sum3;
    
    // XOR gates to calculate sum
    assign sum1 = a ^ b;
    assign s = sum1 ^ cin;
    
    // AND gates to calculate carry out
    assign sum2 = a & b;
    assign sum3 = cin & sum1;
    assign cout = sum2 | sum3;
    
endmodule