
module any_edge_detection (
    input clk,
    input [7:0] in,
    output reg [7:0] anyedge
);

reg [7:0] prev_in;

always @(posedge clk) begin
    prev_in <= in;
end

always @(posedge clk) begin
    if (in != prev_in) begin
        anyedge <= {8{1'b0}};
    end else begin
        anyedge <= in & ~prev_in;
    end
end

endmodule
module top_module (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

any_edge_detection edge_detector (
    .clk(clk),
    .in(in),
    .anyedge(anyedge)
);

endmodule