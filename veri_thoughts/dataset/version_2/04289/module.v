module four_bit_adder(
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

    wire c1, c2, c3;

    full_adder fa0(a[0], b[0], cin, sum[0], c1);
    full_adder fa1(.a(a[1]), .b(b[1]), .cin(c1), .sum(sum[1]), .cout(c2));
    full_adder fa2(.a(a[2]), .b(b[2]), .cin(c2), .sum(sum[2]), .cout(c3));
    full_adder fa3(.a(a[3]), .b(b[3]), .cin(c3), .sum(sum[3]), .cout(cout));

endmodule

module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    wire w1, w2, w3;
    
    xor_gate x1(.a(a), .b(b), .z(w1));
    xor_gate x2(.a(w1), .b(cin), .z(sum));
    
    and_gate a1(.a1(w1), .a2(cin), .zn(w2));
    and_gate a2(.a1(a), .a2(b), .zn(w3));
    
    or_gate o1(.o1(w2), .o2(w3), .zn(cout));

endmodule

module xor_gate(
    input a,
    input b,
    output z
);

    assign z = a ^ b;

endmodule

module and_gate(
    input a1,
    input a2,
    output zn
);

    assign zn = a1 & a2;

endmodule

module or_gate(
    input o1,
    input o2,
    output zn
);

    assign zn = o1 | o2;

endmodule