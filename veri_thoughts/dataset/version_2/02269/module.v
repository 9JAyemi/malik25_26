module top_module( 
    input [255:0] in,
    input [7:0] sel,
    output out );
    
    wire [7:0] decoder_out;
    wire [1:0] mux2_out;
    
    // Decoder
    decoder dec1(
        .in(sel),
        .out(decoder_out)
    );
    
    // 2-to-1 Mux
    mux2 mux2_1(
        .in0(in[decoder_out]),
        .in1(in[decoder_out + 1]),
        .sel(sel[0]),
        .out(mux2_out)
    );
    
    // Final Mux
    assign out = mux2_out[sel[0]];
    
endmodule

// Decoder
module decoder(
    input [7:0] in,
    output reg [7:0] out
);
    always @ (in) begin
        case (in)
            8'b00000001: out = 8'b00000001;
            8'b00000010: out = 8'b00000010;
            8'b00000100: out = 8'b00000100;
            8'b00001000: out = 8'b00001000;
            8'b00010000: out = 8'b00010000;
            8'b00100000: out = 8'b00100000;
            8'b01000000: out = 8'b01000000;
            8'b10000000: out = 8'b10000000;
            default: out = 8'b00000000;
        endcase
    end
endmodule

// 2-to-1 Mux
module mux2(
    input in0,
    input in1,
    input sel,
    output reg [1:0] out
);
    always @ (in0, in1, sel) begin
        case (sel)
            1'b0: out = {in1, in1};
            1'b1: out = {in0, in0};
            default: out = {in0, in0};
        endcase
    end
endmodule