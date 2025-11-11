module transition_capture (
    input clk,
    input reset,
    input [31:0] in,
    output reg [31:0] out
);

reg [31:0] prev_state;

always @(posedge clk) begin
    if (reset) begin
        prev_state <= 0;
        out <= 0;
    end else begin
        prev_state <= in;
        out <= prev_state & ~in;
    end
end

endmodule

module top_module (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

transition_capture tc (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out)
);

endmodule