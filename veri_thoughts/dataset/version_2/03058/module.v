module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    wire [3:0] temp_sum;
    wire [4:0] temp_carry;
    
    // Full adder for the least significant bit
    full_adder FA0(
        .a(A[0]),
        .b(B[0]),
        .c(Cin),
        .sum(temp_sum[0]),
        .carry(temp_carry[0])
    );
    
    // Full adder for the second least significant bit
    full_adder FA1(
        .a(A[1]),
        .b(B[1]),
        .c(temp_carry[0]),
        .sum(temp_sum[1]),
        .carry(temp_carry[1])
    );
    
    // Full adder for the third least significant bit
    full_adder FA2(
        .a(A[2]),
        .b(B[2]),
        .c(temp_carry[1]),
        .sum(temp_sum[2]),
        .carry(temp_carry[2])
    );
    
    // Full adder for the most significant bit
    full_adder FA3(
        .a(A[3]),
        .b(B[3]),
        .c(temp_carry[2]),
        .sum(temp_sum[3]),
        .carry(Cout)
    );
    
    assign Sum = temp_sum;

endmodule

module full_adder(
    input a,
    input b,
    input c,
    output sum,
    output carry
);

    wire s1, c1, c2;
    
    // First XOR gate
    xor_gate XG1(
        .a(a),
        .b(b),
        .out(s1)
    );
    
    // Second XOR gate
    xor_gate XG2(
        .a(s1),
        .b(c),
        .out(sum)
    );
    
    // First AND gate
    and_gate AG1(
        .a(a),
        .b(b),
        .out(c1)
    );
    
    // Second AND gate
    and_gate AG2(
        .a(s1),
        .b(c),
        .out(c2)
    );
    
    // OR gate for the carry out
    or_gate OG1(
        .a(c1),
        .b(c2),
        .out(carry)
    );

endmodule

module xor_gate(
    input a,
    input b,
    output out
);

    assign out = a ^ b;

endmodule

module and_gate(
    input a,
    input b,
    output out
);

    assign out = a & b;

endmodule

module or_gate(
    input a,
    input b,
    output out
);

    assign out = a | b;

endmodule