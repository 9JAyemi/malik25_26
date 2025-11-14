
module adder (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

    wire [4:0] temp = a + b + cin;
    assign {cout, sum} = temp[4:0];

endmodule

module max_finder (
    input [3:0] a,
    input [3:0] b,
    output [3:0] max_val
);

    assign max_val = (a > b) ? a : b;

endmodule

module top_module (
    input clk,
    input reset,
    input [3:0] a,
    input [3:0] b,
    input cin1,
    input cin2,
    output [3:0] sum1,
    output [3:0] sum2,
    output cout1,
    output cout2,
    output [3:0] max_sum
);

    reg [3:0] sum1_reg, sum2_reg;
    reg cout1_reg, cout2_reg;

    adder adder1(
        .a(a),
        .b(b),
        .cin(cin1),
        .sum(sum1),
        .cout(cout1)
    );

    adder adder2(
        .a(a),
        .b(b),
        .cin(cin2),
        .sum(sum2),
        .cout(cout2)
    );

    max_finder max_finder1(
        .a(sum1),
        .b(sum2),
        .max_val(max_sum)
    );

    always @(posedge clk) begin
        if (reset) begin
            sum1_reg <= 4'b0;
            sum2_reg <= 4'b0;
            cout1_reg <= 1'b0;
            cout2_reg <= 1'b0;
        end else begin
            sum1_reg <= sum1;
            sum2_reg <= sum2;
            cout1_reg <= cout1;
            cout2_reg <= cout2;
        end
    end

endmodule
