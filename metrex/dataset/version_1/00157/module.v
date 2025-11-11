
module and_using_nand (
input [1:0] a_b,
output wire out
);

nand n1 (out, ~a_b[0], ~a_b[1]);

endmodule
module dff_with_reset (
input clk,
input reset,
input d,
output reg q
);
always @(posedge clk) begin
if (reset) begin
q <= 1'b0;
end else begin
q <= d;
end
end
endmodule
module functional_module (
input and_out,
input dff_out,
output reg q
);
always @(posedge and_out) begin
if (and_out && (dff_out == 1'b1)) begin
q <= 1'b1;
end else begin
q <= 1'b0;
end
end
endmodule
module top_module (
input clk,
input reset,
input [1:0] a_b,
input d,
output q
);
wire and_out;
wire dff_out;

and_using_nand and_gate (
.a_b(a_b),
.out(and_out)
);

dff_with_reset dff (
.clk(clk),
.reset(reset),
.d(d),
.q(dff_out)
);

functional_module func_mod (
.and_out(and_out),
.dff_out(dff_out),
.q(q)
);

endmodule