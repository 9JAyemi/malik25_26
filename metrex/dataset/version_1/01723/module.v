module decoder (
    input [3:0] in,
    input clk,
    output [15:0] out
);

reg [15:0] out_reg1, out_reg2, out_reg3, out_reg4;

assign out = out_reg4;

always @ (in) begin
    out_reg1[0] = ~in[0] & ~in[1] & ~in[2] & ~in[3];
    out_reg1[1] = ~in[0] & ~in[1] & ~in[2] & in[3];
    out_reg1[2] = ~in[0] & ~in[1] & in[2] & ~in[3];
    out_reg1[3] = ~in[0] & ~in[1] & in[2] & in[3];
    out_reg1[4] = ~in[0] & in[1] & ~in[2] & ~in[3];
    out_reg1[5] = ~in[0] & in[1] & ~in[2] & in[3];
    out_reg1[6] = ~in[0] & in[1] & in[2] & ~in[3];
    out_reg1[7] = ~in[0] & in[1] & in[2] & in[3];
    out_reg1[8] = in[0] & ~in[1] & ~in[2] & ~in[3];
    out_reg1[9] = in[0] & ~in[1] & ~in[2] & in[3];
    out_reg1[10] = in[0] & ~in[1] & in[2] & ~in[3];
    out_reg1[11] = in[0] & ~in[1] & in[2] & in[3];
    out_reg1[12] = in[0] & in[1] & ~in[2] & ~in[3];
    out_reg1[13] = in[0] & in[1] & ~in[2] & in[3];
    out_reg1[14] = in[0] & in[1] & in[2] & ~in[3];
    out_reg1[15] = in[0] & in[1] & in[2] & in[3];
end

always @ (posedge clk) begin
    out_reg4 <= out_reg3;
    out_reg3 <= out_reg2;
    out_reg2 <= out_reg1;
end

endmodule