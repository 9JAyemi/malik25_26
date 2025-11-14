
module mux_256to1(
    input [255:0] in,
    input [7:0] sel,
    output out
);

wire sel_temp;

assign sel_temp = sel[7];
assign out = sel_temp ? in[sel[6:0]] : 1'b0;

endmodule