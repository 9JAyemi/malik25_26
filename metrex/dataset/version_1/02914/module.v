
module decoder (
    input clk,
    input [3:0] ABCD,
    output [15:0] out
);

reg [15:0] stage1_out;
reg [15:0] stage2_out;

always @ (posedge clk) begin
    stage1_out <= {~ABCD[0], ~ABCD[1], ~ABCD[2], ~ABCD[3]};
end

always @ (posedge clk) begin
    stage2_out <= {stage1_out[0], stage1_out[1], stage1_out[2], stage1_out[3], stage1_out[4], stage1_out[5], stage1_out[6], stage1_out[7], stage1_out[8], stage1_out[9], stage1_out[10], stage1_out[11], stage1_out[12], stage1_out[13], stage1_out[14], stage1_out[15]};
end

assign out = ~stage2_out;

endmodule
