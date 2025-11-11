module top_module( 
    input [7:0] in,
    input [1:0] sel,
    output [3:0] out );
    
    wire [1:0] sel_inv;
    assign sel_inv = ~sel;
    
    wire [1:0] sel_2to1;
    assign sel_2to1[0] = sel[0];
    assign sel_2to1[1] = sel[1];
    
    wire [1:0] sel_inv_2to1;
    assign sel_inv_2to1[0] = sel_inv[0];
    assign sel_inv_2to1[1] = sel_inv[1];
    
    wire [1:0] mux1_out;
    wire [1:0] mux2_out;
    wire [1:0] mux3_out;
    wire [1:0] mux4_out;
    
    mux_2to1 mux1(.in0(in[1:0]), .in1(in[3:2]), .sel(sel_2to1[0]), .out(mux1_out));
    mux_2to1 mux2(.in0(in[5:4]), .in1(in[7:6]), .sel(sel_2to1[1]), .out(mux2_out));
    mux_2to1 mux3(.in0(mux1_out), .in1(mux2_out), .sel(sel_inv_2to1[0]), .out(mux3_out));
    mux_2to1 mux4(.in0(mux3_out), .in1(mux3_out), .sel(sel_inv_2to1[1]), .out(mux4_out));
    
    assign out = mux4_out;
    
endmodule

module mux_2to1(
    input [1:0] in0,
    input [1:0] in1,
    input sel,
    output [1:0] out );
    
    assign out = (sel == 1'b0) ? in0 : in1;
    
endmodule