
module alu (
    input [3:0] data1,
    input [3:0] data2,
    input [1:0] op,
    output reg [3:0] q,
    input clk
);

reg [3:0] stage1_out;
reg [3:0] stage2_out;

always @(*) begin
    case(op)
        2'b00: stage1_out = data1 + data2;
        2'b01: stage1_out = data1 - data2;
        2'b10: stage1_out = data1 & data2;
        2'b11: stage1_out = data1 | data2;
    endcase
end

always @(posedge clk) begin
    q <= stage2_out;
    stage2_out <= stage1_out;
end

endmodule
