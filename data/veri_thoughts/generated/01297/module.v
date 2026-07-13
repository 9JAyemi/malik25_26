module adder (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] sum
);

    always @(posedge clk) begin
        if (reset) begin
            sum <= 8'b0;
        end else begin
            sum <= a + b;
        end
    end

endmodule

module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    input select,
    output [7:0] sum
);

    wire [7:0] sum1, sum2;

    adder adder1 (
        .clk(clk),
        .reset(reset),
        .a(a),
        .b(b),
        .sum(sum1)
    );

    adder adder2 (
        .clk(clk),
        .reset(reset),
        .a(a),
        .b(b),
        .sum(sum2)
    );

    assign sum = select ? sum2 : sum1;

endmodule