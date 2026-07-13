module multiplexer_256to1(
    input [255:0] in,
    input [7:0] sel,
    output out
);

wire [7:0] sel_inv;
assign sel_inv = ~sel;

wire [255:0] in_sel;
assign in_sel = {in[255:0], in[255:0], in[255:0], in[255:0], in[255:0], in[255:0], in[255:0], in[255:0]} & {sel_inv[7], sel_inv[6], sel_inv[5], sel_inv[4], sel_inv[3], sel_inv[2], sel_inv[1], sel_inv[0]};

assign out = in_sel[0];

endmodule

module top_module( 
    input [255:0] in,
    input [7:0] sel,
    output out
);

multiplexer_256to1 mux(
    .in(in),
    .sel(sel),
    .out(out)
);

endmodule