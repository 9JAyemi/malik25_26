
module xor_gate(
    input clk,
    input a,
    input b,
    output wire out_xor
);
    assign out_xor = a ^ b;
endmodule

module decoder_4to16(
    input [3:0] in,
    input [2:0] sel,
    output reg [15:0] out_decoder
);
    always @(*) begin
        case (sel)
            3'b000: out_decoder = {16'b0000000000000001};
            3'b001: out_decoder = {16'b0000000000000010};
            3'b010: out_decoder = {16'b0000000000000100};
            3'b011: out_decoder = {16'b0000000000001000};
            3'b100: out_decoder = {16'b0000000000010000};
            3'b101: out_decoder = {16'b0000000000100000};
            3'b110: out_decoder = {16'b0000000001000000};
            3'b111: out_decoder = {16'b0000000010000000};
            default: out_decoder = 16'b0;
        endcase
    end
endmodule

module functional_module(
    input clk,
    input a,
    input b,
    input [3:0] in,
    input [2:0] sel,
    output wire out_func
);
    wire out_xor;
    wire [15:0] out_decoder;
    
    xor_gate xor_inst(
        .clk(clk),
        .a(a),
        .b(b),
        .out_xor(out_xor)
    );
    
    decoder_4to16 decoder_inst(
        .in(in),
        .sel(sel),
        .out_decoder(out_decoder)
    );
    
    assign out_func = out_xor ^ out_decoder[sel];
endmodule

module top_module(
    input clk,
    input a,
    input b,
    input [255:0] in,
    input [2:0] sel,
    output wire out_func
);
    functional_module func_inst(
        .clk(clk),
        .a(a),
        .b(b),
        .in(in[3:0]),
        .sel(sel),
        .out_func(out_func)
    );
endmodule
