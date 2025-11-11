module falling_edge_detector (
    input clk,
    input reset,
    input [31:0] in,
    output reg [31:0] out
);

always @(posedge clk, negedge reset) begin
    if (reset == 0) begin
        out <= 0;
    end else begin
        out <= (in ^ (in & (in - 1))) & ~out;
    end
end

endmodule

module top_module (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

falling_edge_detector detector (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out)
);

endmodule