
module dff (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q
);

always @(posedge clk) begin
    if (reset) begin
        q <= 8'b0;
    end else begin
        q <= d;
    end
end

endmodule
module mux_2to1 (
    input [7:0] a,
    input [7:0] b,
    input sel_b1,
    input sel_b2,
    output [7:0] out_always
);

assign out_always = (sel_b1 & ~sel_b2) ? a : b;

endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] d,
    input sel_b1,
    input sel_b2,
    input [7:0] a,
    input [7:0] b,
    output [7:0] q
);

wire [7:0] out_always;
dff dff_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(q)
);

mux_2to1 mux_inst (
    .a(q),
    .b(out_always),
    .sel_b1(sel_b1),
    .sel_b2(sel_b2),
    .out_always(out_always)
);

endmodule