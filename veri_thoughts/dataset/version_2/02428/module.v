
module rising_edge_detector (
    input clk,
    input [31:0] in,
    output reg [31:0] out
);

reg [31:0] prev_in;

always @(posedge clk) begin
    prev_in <= in;
    out <= in & ~prev_in;
end

endmodule
