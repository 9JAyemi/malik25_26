
module priority_encoder (
    input [3:0] in,
    input clk,
    output [1:0] out
);

reg [1:0] stage1_out;
reg [1:0] stage2_out;

// Stage 1
always @(*) begin
    if (in[0]) stage1_out = 2'b00;
    else if (in[1]) stage1_out = 2'b01;
    else if (in[2]) stage1_out = 2'b10;
    else if (in[3]) stage1_out = 2'b11;
end

// Stage 2
always @(posedge clk) begin
    if (clk == 1'b1) begin
        stage2_out <= stage1_out;
    end
end

// Output
assign out = stage2_out;

endmodule
