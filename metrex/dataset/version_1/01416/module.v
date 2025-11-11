module bitwise_operations(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_and,
    output [2:0] out_xor,
    output [2:0] out_nand
);

assign out_and = a & b;
assign out_xor = a ^ b;
assign out_nand = !(a & b);

endmodule