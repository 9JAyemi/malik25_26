
module and_module (
    input [3:0] a,
    input [3:0] b,
    output [3:0] out
);
    assign out = a & b;
endmodule

module decoder_module (
    input [1:0] sel,
    output [3:0] out
);
    assign out = (sel == 2'b00) ? 4'b1110 :
                  (sel == 2'b01) ? 4'b1101 :
                  (sel == 2'b10) ? 4'b1011 :
                  (sel == 2'b11) ? 4'b0111 : 4'b0000;
endmodule

module mux_module (
    input [3:0] a,
    input [3:0] b,
    input A,
    input B,
    output out
);
    wire [3:0] and_out;
    wire [3:0] decoder_out;
    
    and_module and_inst (
        .a(a),
        .b(b),
        .out(and_out)
    );
    
    decoder_module decoder_inst (
        .sel({A, B}),
        .out(decoder_out)
    );
    
    assign out = (decoder_out == 4'b1110) ? and_out[0] :
                  (decoder_out == 4'b1101) ? and_out[1] :
                  (decoder_out == 4'b1011) ? and_out[2] :
                  (decoder_out == 4'b0111) ? and_out[3] : 1'b0;
endmodule

module top_module (
    input [3:0] a,
    input [3:0] b,
    input A,
    input B,
    output out
);
    wire mux_out;
    mux_module mux_inst (
        .a(a),
        .b(b),
        .A(A),
        .B(B),
        .out(mux_out)
    );
    
    assign out = ~mux_out;
endmodule
