module adder (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

    assign {cout, sum} = a + b + cin;

endmodule

module counter (
    input clk,
    input reset,
    input enable,
    output reg [7:0] count
);

    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            count <= 8'b0;
        end else if (enable) begin
            count <= count + 1;
        end
    end

endmodule

module functional_module (
    input [3:0] adder_sum,
    input [7:0] counter_count,
    output [11:0] result
);

    assign result = {4'b0, adder_sum} + counter_count;

endmodule

module top_module (
    input clk,
    input reset,
    input enable,
    input [3:0] a,
    input [3:0] b,
    input cin,
    output cout,
    output [3:0] sum,
    output [7:0] count,
    output [11:0] result
);

    adder adder_inst (
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum),
        .cout(cout)
    );

    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .count(count)
    );

    functional_module functional_inst (
        .adder_sum(sum),
        .counter_count(count),
        .result(result)
    );

endmodule