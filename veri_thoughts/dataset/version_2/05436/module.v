
module pipeline_stage_2 (
    input [3:0] in,
    output reg [3:0] out,
    input clk
);

reg [3:0] stage_1_out;

always @(*) begin
    stage_1_out = in;
end

always @(posedge clk) begin
    out <= stage_1_out;
end

endmodule
