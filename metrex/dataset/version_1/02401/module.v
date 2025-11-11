module dff_module (
    input clk,
    input d,
    output reg q
);

always @(negedge clk) begin
    q <= d;
end

endmodule

module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);

wire [7:0] q_internal;

dff_module dff0(clk, d[0], q_internal[0]);
dff_module dff1(clk, d[1], q_internal[1]);
dff_module dff2(clk, d[2], q_internal[2]);
dff_module dff3(clk, d[3], q_internal[3]);
dff_module dff4(clk, d[4], q_internal[4]);
dff_module dff5(clk, d[5], q_internal[5]);
dff_module dff6(clk, d[6], q_internal[6]);
dff_module dff7(clk, d[7], q_internal[7]);

assign q = q_internal;

endmodule