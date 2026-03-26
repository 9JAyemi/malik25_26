
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] sum;
    wire carry0, carry1, carry2;
    
    // Full adder for the least significant bit
    full_adder FA0(
        .a(A[0]),
        .b(B[0]),
        .c(Cin),
        .sum(sum[0]),
        .carry(carry0)
    );
    
    // Full adder for bits 1-3
    full_adder FA1(
        .a(A[1]),
        .b(B[1]),
        .c(carry0),
        .sum(sum[1]),
        .carry(carry1)
    );
    
    full_adder FA2(
        .a(A[2]),
        .b(B[2]),
        .c(carry1),
        .sum(sum[2]),
        .carry(carry2)
    );
    
    full_adder FA3(
        .a(A[3]),
        .b(B[3]),
        .c(carry2),
        .sum(sum[3]),
        .carry(Cout)
    );
    
    assign S = sum;
    
endmodule
module full_adder(
    input a,
    input b,
    input c,
    output sum,
    output carry
);

    assign sum = a ^ b ^ c;
    assign carry = (a & b) | (a & c) | (b & c);
    
endmodule