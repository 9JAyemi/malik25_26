module edge_detector (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

reg [7:0] prev;
reg [7:0] curr;
wire [7:0] xor_out;

always @(posedge clk) begin
    prev <= curr;
    curr <= in;
end

assign xor_out = curr ^ prev;
assign anyedge = xor_out & curr;

endmodule

module top_module (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

edge_detector detector(
    .clk(clk),
    .in(in),
    .anyedge(anyedge)
);

endmodule