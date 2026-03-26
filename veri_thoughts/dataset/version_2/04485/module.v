module edge_detector_pipeline (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

reg [7:0] reg1, reg2, reg3, reg4, reg5, reg6, reg7, reg8;

always @(posedge clk) begin
    reg1 <= in;
end

always @(posedge clk) begin
    reg2 <= reg1;
end

always @(posedge clk) begin
    reg3 <= reg2;
end

always @(posedge clk) begin
    reg4 <= reg3;
end

always @(posedge clk) begin
    reg5 <= reg4;
end

always @(posedge clk) begin
    reg6 <= reg5;
end

always @(posedge clk) begin
    reg7 <= reg6;
end

always @(posedge clk) begin
    reg8 <= reg7;
end

assign anyedge[0] = reg1[0] ^ reg2[0];
assign anyedge[1] = reg2[1] ^ reg3[1];
assign anyedge[2] = reg3[2] ^ reg4[2];
assign anyedge[3] = reg4[3] ^ reg5[3];
assign anyedge[4] = reg5[4] ^ reg6[4];
assign anyedge[5] = reg6[5] ^ reg7[5];
assign anyedge[6] = reg7[6] ^ reg8[6];
assign anyedge[7] = reg8[7];

endmodule

module top_module (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

edge_detector_pipeline edp(
    .clk(clk),
    .in(in),
    .anyedge(anyedge)
);

endmodule