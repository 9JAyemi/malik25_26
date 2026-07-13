module mux_4to1 (
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] sel,
    input clk,   // Added clock input
    output [3:0] out
);

reg [3:0] stage1_out;
reg [3:0] stage2_out;

always @(in0, in1, in2, in3, sel) begin
    case (sel)
        2'b00: stage1_out <= in0;
        2'b01: stage1_out <= in1;
        2'b10: stage1_out <= in2;
        2'b11: stage1_out <= in3;
    endcase
end

always @(posedge clk) begin
    stage2_out <= stage1_out;
end

assign out = stage2_out;

endmodule