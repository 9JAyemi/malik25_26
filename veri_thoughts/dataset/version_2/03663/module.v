
module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    input select,
    output [7:0] sum,
    output [7:0] mux_out,
    output [7:0] final_out
);

// 8-bit adder module
adder add_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .sum(sum)
);

// 8-bit multiplexer module
mux mux_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .select(select),
    .mux_out(mux_out)
);

// Bitwise OR module
bitwise_or or_inst (
    .clk(clk),
    .reset(reset),
    .a(sum),
    .b(mux_out),
    .final_out(final_out)
);

endmodule

module adder (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] sum
);
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            sum <= 8'b0;
        end else begin
            sum <= a + b;
        end
    end
endmodule

module mux (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    input select,
    output reg [7:0] mux_out
);
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            mux_out <= 8'b0;
        end else begin
            mux_out <= select ? b : a;
        end
    end
endmodule

module bitwise_or (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] final_out
);
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            final_out <= 8'b0;
        end else begin
            final_out <= a | b;
        end
    end
endmodule
