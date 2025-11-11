
module top_module (
    input clk,
    input [7:0] in,
    output reg [7:0] q
);

// Edge Detection Module
reg [7:0] in_prev;
reg [7:0] edge_detected;
always @(posedge clk) begin
    in_prev <= in;
    edge_detected <= in ^ in_prev;
end

// Functional Module
reg [7:0] q_reg;
always @(*) begin
    q_reg <= edge_detected;
end

always @(posedge clk) begin
    q <= q_reg;
end

endmodule