
module async_reset_binary_counter(
    input clk,
    input reset,
    output reg [3:0] q
);
    always @(posedge clk or negedge reset) begin
        if (reset == 0) begin
            q <= 4'b1000; // Reset to 8
        end else begin
            q <= q + 1;
        end
    end
endmodule
module mux_2to1(
    input [3:0] a,
    input [3:0] b,
    input sel_b1,
    input sel_b2,
    output reg [3:0] out
);
    always @(*) begin
        if (sel_b1 && sel_b2) begin
            out <= b;
        end else begin
            out <= a;
        end
    end
endmodule
module adder(
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);
    assign out = in1 + in2;
endmodule
module top_module(
    input clk,
    input reset,      // Asynchronous active-high reset
    input sel_b1,
    input sel_b2,
    output reg out_always,
    output reg [3:0] q_counter,
    output reg [3:0] mux_out,  // Fixed the width from [1:0] to [3:0]
    output reg [3:0] adder_out
);
    async_reset_binary_counter counter(
        .clk(clk),
        .reset(reset),
        .q(q_counter)
    );

    mux_2to1 mux(
        .a(q_counter),
        .b(4'b1111),
        .sel_b1(sel_b1),
        .sel_b2(sel_b2),
        .out(mux_out)
    );

    adder add(
        .in1(q_counter),
        .in2(mux_out),
        .out(adder_out)
    );

    always @(posedge clk) begin
        out_always <= 1;
    end
endmodule