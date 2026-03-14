
module bit_converter(
    input [3:0] in,
    output [1:0] out
);

    assign out = (in < 5) ? 2'b00 : (in < 9) ? 2'b01 : (in < 11) ? 2'b10 : 2'b11;

endmodule
