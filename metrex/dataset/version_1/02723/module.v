module decoder (
    input sel2,
    input sel1,
    input sel0,
    input clk,
    output reg [63:0] out
);

reg [63:0] stage1_out;
reg [63:0] stage2_out;

always @(*) begin
    if(sel2 == 0 && sel1 == 0 && sel0 == 0) begin
        stage1_out[0] <= 1'b1;
        stage1_out[63:1] <= 64'b0;
    end
    else if(sel2 == 1 && sel1 == 0 && sel0 == 0) begin
        stage1_out[8] <= 1'b1;
        stage1_out[63:9] <= 56'b0;
        stage1_out[7:0] <= 8'b0;
    end
    else if(sel2 == 0 && sel1 == 1 && sel0 == 1) begin
        stage1_out[56] <= 1'b1;
        stage1_out[63:57] <= 56'b0;
    end
    else if(sel2 == 1 && sel1 == 1 && sel0 == 0) begin
        stage1_out[60] <= 1'b1;
        stage1_out[63:61] <= 3'b0;
        stage1_out[60:0] <= 60'b0;
    end
    else if(sel2 == 0 && sel1 == 1 && sel0 == 1) begin
        stage1_out[48] <= 1'b1;
        stage1_out[63:49] <= 15'b0;
        stage1_out[48:0] <= 48'b0;
    end
    else begin
        stage1_out[63:48] <= 16'b0;
        stage1_out[47:0] <= 48'b0;
    end
end

always @(posedge clk) begin
    stage2_out <= stage1_out;
end

always @* begin
    out = stage2_out;
end

endmodule