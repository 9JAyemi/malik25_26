module bitwise_operations(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_and_bitwise,
    output [2:0] out_xor_bitwise,
    output [2:0] out_nor_bitwise,
    output [5:0] out_not
);

    // Bitwise AND
    assign out_and_bitwise = a & b;

    // Bitwise XOR
    assign out_xor_bitwise = a ^ b;

    // Bitwise NOR
    assign out_nor_bitwise = ~(a | b);

    // NOT of both vectors
    assign out_not[5:3] = ~b;
    assign out_not[2:0] = ~a;

endmodule

module top_module( 
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_and_bitwise,
    output [2:0] out_xor_bitwise,
    output [2:0] out_nor_bitwise,
    output [5:0] out_not
);

    bitwise_operations bitwise_ops(.a(a), .b(b), .out_and_bitwise(out_and_bitwise), .out_xor_bitwise(out_xor_bitwise), .out_nor_bitwise(out_nor_bitwise), .out_not(out_not));

endmodule