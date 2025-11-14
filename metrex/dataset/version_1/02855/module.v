module binary_to_gray (
    input [4:0] bin_in,
    output reg [4:0] gray_out
);

reg [4:0] stage1_out;
reg [4:0] stage2_out;

// Stage 1
always @ (bin_in) begin
    stage1_out[0] = bin_in[0];
    stage1_out[1] = bin_in[0] ^ bin_in[1];
    stage1_out[2] = bin_in[1] ^ bin_in[2];
    stage1_out[3] = bin_in[2] ^ bin_in[3];
    stage1_out[4] = bin_in[3] ^ bin_in[4];
end

// Stage 2
always @ (stage1_out) begin
    stage2_out[0] = stage1_out[0];
    stage2_out[1] = stage1_out[1] ^ stage1_out[0];
    stage2_out[2] = stage1_out[2] ^ stage1_out[1];
    stage2_out[3] = stage1_out[3] ^ stage1_out[2];
    stage2_out[4] = stage1_out[4] ^ stage1_out[3];
end

always @* begin
    gray_out = stage2_out;
end

endmodule