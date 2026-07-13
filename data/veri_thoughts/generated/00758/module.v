module barrel_shifter_4bit (
    input [3:0] in,
    input [1:0] shift,
    input clk,
    output reg [3:0] out
);

reg [3:0] stage1_out;
reg [3:0] stage2_out;

always @(*) begin
    case(shift)
        2'b00: stage1_out = in << 1; // logical left shift
        2'b01: stage1_out = in >> 1; // logical right shift
        2'b10: stage1_out = {in[1:0], in[3:2]}; // arithmetic left shift
        2'b11: stage1_out = {in[3:2], in[0]}; // arithmetic right shift
    endcase
    stage2_out <= stage1_out;
end

always @(posedge clk) begin
    out <= stage2_out;
end

endmodule