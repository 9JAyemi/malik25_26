module transition_capture (
    input clk,
    input reset,
    input [31:0] in,
    output reg [31:0] out
);

reg [31:0] prev_in;

always @(posedge clk) begin
    if (reset) begin
        prev_in <= 32'h0;
        out <= 32'h0;
    end else begin
        prev_in <= in;
        out <= (prev_in & ~in) | out;
    end
end

endmodule

module top_module (
    input clk,
    input reset,
    input [31:0] in1,
    input [31:0] in2,
    output [31:0] out
);

wire [31:0] out1, out2;

transition_capture tc1 (.clk(clk), .reset(reset), .in(in1), .out(out1));
transition_capture tc2 (.clk(clk), .reset(reset), .in(in2), .out(out2));

assign out = out1 | out2;

endmodule