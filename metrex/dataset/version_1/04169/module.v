module rising_edge_detector (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

reg [31:0] stage1_out;
reg [31:0] stage2_out;
reg [31:0] stage3_out;

always @(posedge clk) begin
    if (reset) begin
        stage1_out <= 0;
        stage2_out <= 0;
        stage3_out <= 0;
    end else begin
        stage1_out <= in;
        stage2_out <= stage1_out ^ {stage1_out[0], stage1_out[31:1]};
        stage3_out <= stage2_out & {~stage2_out[0], stage2_out[31:1]};
    end
end

assign out = stage3_out;

endmodule

module top_module (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

rising_edge_detector detector (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out)
);

endmodule