module demux_256to1(
    input [3:0] in,
    input [7:0] sel,
    output [1023:0] out
);

wire [255:0] mux_out;

genvar i;
generate
    for (i = 0; i < 256; i = i + 1) begin : mux_gen
        assign mux_out[i] = (sel == i) ? in : 4'b0;
    end
endgenerate

assign out = {mux_out};

endmodule

module top_module( 
    input [3:0] in,
    input [7:0] sel,
    output [1023:0] out );

demux_256to1 demux(
    .in(in),
    .sel(sel),
    .out(out)
);

endmodule