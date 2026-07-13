
module rising_edge_detection (
    input clk,
    input [7:0] d,
    output [7:0] q
);

reg [7:0] q_reg;
reg [7:0] d_reg;

always @(posedge clk) begin
    d_reg <= d;
    q_reg <= q_reg & ~(d_reg ^ q_reg);
end

assign q = q_reg;

endmodule
module eight_bit_adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);

assign sum = a + b;

endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] d,
    input [7:0] in,
    output [7:0] q,
    output [7:0] rising_edge,
    output [7:0] sum_output
);

wire [7:0] rising_edge_detection_output;
wire [7:0] random_number;

rising_edge_detection red(clk, in, rising_edge_detection_output);
eight_bit_adder adder(rising_edge_detection_output, d, sum_output);

assign q = rising_edge_detection_output;
assign rising_edge = sum_output;

endmodule