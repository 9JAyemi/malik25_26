
module conditional_output (
    input [3:0] A,
    input [3:0] B,
    input [1:0] C,
    input clk,        
    output [3:0] out
);

reg [3:0] stage1_out;
reg [3:0] stage2_out;

always @(*) begin
    case(C)
        2'b10: stage1_out = A ^ B;
        2'b01: stage1_out = B;
        default: stage1_out = A;
    endcase
end

always @(posedge clk) begin  // Use clk in the always block
    stage2_out <= stage1_out;
end

assign out = stage2_out;

endmodule
