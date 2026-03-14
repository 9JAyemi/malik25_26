
module dff_negedge (
    input clk,
    input d,
    output reg q
);

always @(negedge clk) begin
    q <= #1 ~d;
end

endmodule
module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);

wire [7:0] dff_outputs;
wire [7:0] inverted_outputs;

dff_negedge dff0(clk, d[0], dff_outputs[0]);
dff_negedge dff1(clk, d[1], dff_outputs[1]);
dff_negedge dff2(clk, d[2], dff_outputs[2]);
dff_negedge dff3(clk, d[3], dff_outputs[3]);
dff_negedge dff4(clk, d[4], dff_outputs[4]);
dff_negedge dff5(clk, d[5], dff_outputs[5]);
dff_negedge dff6(clk, d[6], dff_outputs[6]);
dff_negedge dff7(clk, d[7], dff_outputs[7]);

assign inverted_outputs = ~dff_outputs;
assign q = inverted_outputs;

endmodule