
module binary_to_gray (
    input [3:0] B,
    input clk,
    output [3:0] G
);

reg [3:0] G_reg1, G_reg2, G_reg3;

assign G = G_reg3;

// Pipeline stage 1
always @(*) begin
    G_reg1[0] = B[0];
    G_reg1[1] = B[0] ^ B[1];
    G_reg1[2] = B[1] ^ B[2];
    G_reg1[3] = B[2] ^ B[3];
end

// Pipeline stage 2
always @(posedge clk) begin
    G_reg2[0] <= G_reg1[0];
    G_reg2[1] <= G_reg1[1] ^ G_reg1[0];
    G_reg2[2] <= G_reg1[2] ^ G_reg1[1];
    G_reg2[3] <= G_reg1[3] ^ G_reg1[2];
end

// Pipeline stage 3
always @(posedge clk) begin
    G_reg3[0] <= G_reg2[0];
    G_reg3[1] <= G_reg2[1] ^ G_reg2[0];
    G_reg3[2] <= G_reg2[2] ^ G_reg2[1];
    G_reg3[3] <= G_reg2[3] ^ G_reg2[2];
end

endmodule
