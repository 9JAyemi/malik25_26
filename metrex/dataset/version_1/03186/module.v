
module barrel_shifter (
    input [3:0] in,
    input [1:0] ctrl,
    output reg [3:0] out,
    input clk  // Added clock input
);

reg [3:0] stage1_out;
reg [3:0] stage2_out;

always @(posedge clk) begin 
    case(ctrl)
        2'b00: stage1_out = {in[2:0], 1'b0};
        2'b01: stage1_out = {in[1:0], 2'b0};
        2'b10: stage1_out = {1'b0, in[3:1]};
        2'b11: stage1_out = {2'b0, in[3:2]};
        default: stage1_out = 4'b0;
    endcase
end

always @(posedge clk) begin  
    stage2_out <= stage1_out;
    out <= stage2_out;       
end

endmodule
