module any_edge_detection_pipeline (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

reg [7:0] reg1, reg2, reg3;

always @(posedge clk) begin
    reg1 <= in;
end

always @(posedge clk) begin
    reg2 <= reg1;
end

always @(posedge clk) begin
    reg3 <= reg2;
end

assign anyedge = (reg1 ^ reg2) & ~reg1 & reg3;

endmodule

module top_module (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

any_edge_detection_pipeline pipeline1(
    .clk(clk),
    .in(in),
    .anyedge(anyedge)
);

endmodule