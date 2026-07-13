
module byte_reversal(
    input [31:0] in,
    output [31:0] out
    );
    assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};
endmodule
module adder(
    input [31:0] in1,
    input [31:0] in2,
    output [31:0] out
    );
    assign out = in1 + in2;
endmodule
module top_module( 
    input [255:0] in,
    input [7:0] sel,
    output [31:0] out );
    
    wire [31:0] byte_reversal_out;
    wire [31:0] selected_input;
    wire [31:0] mux_inputs [7:0];
    
    genvar i;
    wire [7:0] decoder_out;
    
    assign decoder_out = {8{~sel}};
    
    for (i = 0; i < 8; i = i + 1) begin
        assign mux_inputs[i] = in[i * 32 +: 32];
    end
    
    assign selected_input = mux_inputs[decoder_out];
    
    // Byte reversal
    byte_reversal byte_reversal_inst(
        .in(selected_input),
        .out(byte_reversal_out)
        );
    
    // Adder
    adder adder_inst(
        .in1(selected_input),
        .in2(byte_reversal_out),
        .out(out)
        );
    
endmodule