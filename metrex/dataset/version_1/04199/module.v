module flip_flop (
    input clk,
    input reset,           // Asynchronous active-high reset
    input [7:0] d,
    output reg [7:0] q
);

always @(negedge clk or posedge reset) begin
    if (reset) begin
        q <= 8'b0;
    end else begin
        q <= d;
    end
end

endmodule

module transition_detector (
    input clk,
    input reset,           // Synchronous active-high reset
    input [31:0] in,
    output reg [31:0] out
);

reg [31:0] prev_in;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        out <= 32'b0;
        prev_in <= 32'b0;
    end else begin
        out <= (in & ~prev_in);
        prev_in <= in;
    end
end

endmodule

module bitwise_or (
    input [7:0] in1,
    input [31:0] in2,
    output reg [7:0] out
);

always @* begin
    out = in1 | in2[7:0];
end

endmodule

module top_module (
    input clk,
    input reset,           // Synchronous active-high reset
    input [7:0] d,
    input [31:0] in,
    output reg [7:0] q
);

wire [31:0] transition_out;
wire [7:0] flip_flop_out;

flip_flop ff (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(flip_flop_out)
);

transition_detector td (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(transition_out)
);

bitwise_or bo (
    .in1(flip_flop_out),
    .in2(transition_out),
    .out(q)
);

endmodule