
module top_module(
    input wire [15:0] in,
    output wire [11:0] out );

    wire [7:0] hi_byte;
    wire [7:0] lo_byte;
    wire [31:0] swapped_word;
    wire [15:0] byte16_hi;
    wire [15:0] byte16_lo;
    wire [15:0] xor_result;
    
    module1 m1(.in(in), .out_hi(hi_byte), .out_lo(lo_byte));
    module2 m2(.in({in[15:8], in[7:0], 16'h0}), .out(swapped_word));
    
    assign byte16_hi = {8'h0, hi_byte};
    assign byte16_lo = {8'h0, lo_byte};
    assign xor_result = byte16_hi ^ byte16_lo;
    assign out = swapped_word & {16'h0, xor_result};

endmodule
module module1(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo );

    assign out_hi = in[15:8];
    assign out_lo = in[7:0];

endmodule
module module2(
    input wire [31:0] in,
    output wire [31:0] out );

    assign out = {in[23:16], in[15:8], in[7:0], in[31:24]};

endmodule