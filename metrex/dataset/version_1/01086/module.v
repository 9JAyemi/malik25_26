module ripple_bcd_adder (
    input [3:0] A,
    input [3:0] B,
    input select,
    output [3:0] binary_sum,
    output reg [3:0] BCD0,
    output reg [3:0] BCD1
);

reg [3:0] sum;
wire [7:0] bcd_sum;

// Ripple carry adder
assign binary_sum = A + B;

// Binary to BCD converter
binary_to_bcd_converter bcd_converter(
    .binary_in(binary_sum),
    .bcd_out(bcd_sum)
);

// Output select
always @(*) begin
    if (select) begin
        BCD0 = bcd_sum[3:0];
        BCD1 = bcd_sum[7:4];
    end
    else begin
        BCD0 = 4'b0000;
        BCD1 = 4'b0000;
    end
end

endmodule

module binary_to_bcd_converter (
    input [3:0] binary_in,
    output reg [7:0] bcd_out
);

always @(*) begin
    case (binary_in)
        4'b0000: bcd_out = 8'b00000001;
        4'b0001: bcd_out = 8'b00000010;
        4'b0010: bcd_out = 8'b00000100;
        4'b0011: bcd_out = 8'b00000110;
        4'b0100: bcd_out = 8'b00001000;
        4'b0101: bcd_out = 8'b00001010;
        4'b0110: bcd_out = 8'b00001100;
        4'b0111: bcd_out = 8'b00001110;
        4'b1000: bcd_out = 8'b00010000;
        4'b1001: bcd_out = 8'b00010001;
        4'b1010: bcd_out = 8'b00010010;
        4'b1011: bcd_out = 8'b00010011;
        4'b1100: bcd_out = 8'b00010100;
        4'b1101: bcd_out = 8'b00010101;
        4'b1110: bcd_out = 8'b00010110;
        4'b1111: bcd_out = 8'b00010111;
        default: bcd_out = 8'b00000000;
    endcase
end

endmodule