module edge_detection (
    input clk,
    input reset,
    input [3:0] in,
    output reg [3:0] out
);

reg [3:0] prev_in;

always @(posedge clk) begin
    if (reset) begin
        prev_in <= 4'b0000;
        out <= 4'b0000;
    end else begin
        prev_in <= in;
        out <= 4'b0000;
        if (in[0] != prev_in[0]) out[0] <= 1'b1;
        if (in[1] != prev_in[1]) out[1] <= 1'b1;
        if (in[2] != prev_in[2]) out[2] <= 1'b1;
        if (in[3] != prev_in[3]) out[3] <= 1'b1;
    end
end

endmodule

module bitwise_or (
    input [3:0] in1,
    input [3:0] in2,
    output reg [3:0] out
);

always @(in1, in2) begin
    out <= in1 | in2;
end

endmodule

module top_module (
    input clk,
    input reset,
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);

wire [3:0] edge1;
wire [3:0] edge2;

edge_detection ed1(clk, reset, in1, edge1);
edge_detection ed2(clk, reset, in2, edge2);
bitwise_or or_gate(edge1, edge2, out);

endmodule