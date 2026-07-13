module bitwise_or (
    input [3:0] a,
    input [3:0] b,
    input clk,
    output reg [3:0] out
);

reg [3:0] stage1_out;
reg [3:0] stage2_out;

always @ (posedge clk) begin
    stage1_out <= a | b;
    stage2_out <= stage1_out;
end

always @* begin
    out = stage2_out;
end

endmodule