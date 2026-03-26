
module bit_converter(
    input bit_in,
    input strobe,
    input clk,
    output bit_out
);

reg bit_in_sync;

always @(posedge clk)
begin
    if (strobe)
        bit_in_sync <= bit_in;
end

assign bit_out = bit_in_sync;

endmodule
module byte_to_bit_converter(
    input [7:0] byte_in,
    input strobe,
    input clk,
    output [7:0] bit_out
);

wire bit0_out, bit1_out, bit2_out, bit3_out, bit4_out, bit5_out, bit6_out, bit7_out;

bit_converter bit0(
    .bit_in(byte_in[0]),
    .strobe(strobe),
    .clk(clk),
    .bit_out(bit0_out)
);

bit_converter bit1(
    .bit_in(byte_in[1]),
    .strobe(strobe),
    .clk(clk),
    .bit_out(bit1_out)
);

bit_converter bit2(
    .bit_in(byte_in[2]),
    .strobe(strobe),
    .clk(clk),
    .bit_out(bit2_out)
);

bit_converter bit3(
    .bit_in(byte_in[3]),
    .strobe(strobe),
    .clk(clk),
    .bit_out(bit3_out)
);

bit_converter bit4(
    .bit_in(byte_in[4]),
    .strobe(strobe),
    .clk(clk),
    .bit_out(bit4_out)
);

bit_converter bit5(
    .bit_in(byte_in[5]),
    .strobe(strobe),
    .clk(clk),
    .bit_out(bit5_out)
);

bit_converter bit6(
    .bit_in(byte_in[6]),
    .strobe(strobe),
    .clk(clk),
    .bit_out(bit6_out)
);

bit_converter bit7(
    .bit_in(byte_in[7]),
    .strobe(strobe),
    .clk(clk),
    .bit_out(bit7_out)
);

assign bit_out = {bit7_out, bit6_out, bit5_out, bit4_out, bit3_out, bit2_out, bit1_out, bit0_out};

endmodule