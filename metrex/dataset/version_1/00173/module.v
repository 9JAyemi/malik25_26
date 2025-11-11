
module top_module( 
    input wire clk,
    input wire reset,
    input wire [15:0] in,
    input wire select,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    output wire [1023:0] out_demux );
    
    // Demultiplexer
    wire [255:0] demux_out;
    wire [3:0] demux_sel = in[3:0];
    demux_256to1 demux(
        .in(select ? 4'b0 : demux_sel),
        .out(demux_out)
    );
    
    // Multiplexer
    wire [7:0] mux_out;
    wire [1:0] mux_sel = in[11:10];
    mux_2to1 mux(
        .in0(in[7:0]),
        .in1(in[15:8]),
        .sel(select ? mux_sel : 2'b0),
        .out(mux_out)
    );
    
    // Control Logic
    wire demux_enable = select ? 0 : 1;
    wire mux_enable = select ? 1 : 0;
    
    // Output
    assign out_demux = {demux_enable ? demux_out : 256'b0};
    assign out_hi = {mux_enable ? mux_out : 8'b0};
    assign out_lo = {demux_enable ? 256'b0 : 8'b0};
    
endmodule
module demux_256to1(
    input wire [3:0] in,
    output wire [255:0] out
);
    genvar i;
    generate
        for (i = 0; i < 256; i = i + 1) begin : demux_gen
            assign out[i] = (in == i);
        end
    endgenerate
endmodule
module mux_2to1(
    input wire [7:0] in0,
    input wire [7:0] in1,
    input wire [1:0] sel,
    output wire [7:0] out
);
    assign out = (sel == 2'b0) ? in0 : in1;
endmodule