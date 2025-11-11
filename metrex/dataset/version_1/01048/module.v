module any_edge_detector (
    input clk,
    input [7:0] in,
    output reg [7:0] anyedge
);

reg [7:0] prev_in;

always @(posedge clk) begin
    anyedge <= (in ^ prev_in) & in;
    prev_in <= in;
end

endmodule

module top_module (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

any_edge_detector detector (
    .clk(clk),
    .in(in),
    .anyedge(anyedge)
);

endmodule