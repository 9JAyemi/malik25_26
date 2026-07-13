module demux_1to256_pipeline(
    input [31:0] in,
    input clk,
    output reg [7:0] out
);

reg [7:0] stage1_out;
reg [7:0] stage2_out;
reg [7:0] stage3_out;
reg [7:0] stage4_out;
reg [7:0] stage5_out;
reg [7:0] stage6_out;
reg [7:0] stage7_out;
reg [7:0] stage8_out;

always @(*) begin
    stage1_out = in[0] ? 8'b00000001 : 8'b00000000;
end

always @(*) begin
    stage2_out[0] = stage1_out[0] | stage1_out[1];
    stage2_out[1] = stage1_out[2] | stage1_out[3];
    stage2_out[2] = stage1_out[4] | stage1_out[5];
    stage2_out[3] = stage1_out[6] | stage1_out[7];
    stage2_out[4] = stage1_out[0] | stage1_out[1];
    stage2_out[5] = stage1_out[2] | stage1_out[3];
    stage2_out[6] = stage1_out[4] | stage1_out[5];
    stage2_out[7] = stage1_out[6] | stage1_out[7];
end

always @(*) begin
    stage3_out[0] = stage2_out[0] | stage2_out[2];
    stage3_out[1] = stage2_out[4] | stage2_out[6];
    stage3_out[2] = stage2_out[0] | stage2_out[2];
    stage3_out[3] = stage2_out[4] | stage2_out[6];
    stage3_out[4] = stage2_out[1] | stage2_out[3];
    stage3_out[5] = stage2_out[5] | stage2_out[7];
    stage3_out[6] = stage2_out[1] | stage2_out[3];
    stage3_out[7] = stage2_out[5] | stage2_out[7];
end

always @(*) begin
    stage4_out[0] = stage3_out[0] | stage3_out[4];
    stage4_out[1] = stage3_out[2] | stage3_out[6];
    stage4_out[2] = stage3_out[0] | stage3_out[4];
    stage4_out[3] = stage3_out[2] | stage3_out[6];
    stage4_out[4] = stage3_out[1] | stage3_out[5];
    stage4_out[5] = stage3_out[3] | stage3_out[7];
    stage4_out[6] = stage3_out[1] | stage3_out[5];
    stage4_out[7] = stage3_out[3] | stage3_out[7];
end

always @(*) begin
    stage5_out[0] = stage4_out[0] | stage4_out[4];
    stage5_out[1] = stage4_out[1] | stage4_out[5];
    stage5_out[2] = stage4_out[2] | stage4_out[6];
    stage5_out[3] = stage4_out[3] | stage4_out[7];
    stage5_out[4] = stage4_out[4] | stage4_out[0];
    stage5_out[5] = stage4_out[5] | stage4_out[1];
    stage5_out[6] = stage4_out[6] | stage4_out[2];
    stage5_out[7] = stage4_out[7] | stage4_out[3];
end

always @(*) begin
    stage6_out[0] = stage5_out[0] | stage5_out[4];
    stage6_out[1] = stage5_out[1] | stage5_out[5];
    stage6_out[2] = stage5_out[2] | stage5_out[6];
    stage6_out[3] = stage5_out[3] | stage5_out[7];
    stage6_out[4] = stage5_out[0] | stage5_out[4];
    stage6_out[5] = stage5_out[1] | stage5_out[5];
    stage6_out[6] = stage5_out[2] | stage5_out[6];
    stage6_out[7] = stage5_out[3] | stage5_out[7];
end

always @(*) begin
    stage7_out[0] = stage6_out[0] | stage6_out[2];
    stage7_out[1] = stage6_out[4] | stage6_out[6];
    stage7_out[2] = stage6_out[0] | stage6_out[2];
    stage7_out[3] = stage6_out[4] | stage6_out[6];
    stage7_out[4] = stage6_out[1] | stage6_out[3];
    stage7_out[5] = stage6_out[5] | stage6_out[7];
    stage7_out[6] = stage6_out[1] | stage6_out[3];
    stage7_out[7] = stage6_out[5] | stage6_out[7];
end

always @(*) begin
    stage8_out[0] = stage7_out[0] | stage7_out[4];
    stage8_out[1] = stage7_out[2] | stage7_out[6];
    stage8_out[2] = stage7_out[0] | stage7_out[2];
    stage8_out[3] = stage7_out[2] | stage7_out[6];
    stage8_out[4] = stage7_out[1] | stage7_out[5];
    stage8_out[5] = stage7_out[3] | stage7_out[7];
    stage8_out[6] = stage7_out[1] | stage7_out[3];
    stage8_out[7] = stage7_out[5] | stage7_out[7];
end

always @(posedge clk) begin
    out <= stage8_out;
end

endmodule