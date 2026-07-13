
module adder_module (
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);

    wire [31:0] carry_out;
    wire [31:0] sum1;

    assign {carry_out, sum1} = a + b;

    assign sum = sum1;

endmodule
module control_logic (
    input [31:0] a,
    input [31:0] b,
    input select,
    output [31:0] sum
);

    wire [31:0] sum1;
    wire [31:0] sum2;

    adder_module adder1(.a(a), .b(b), .sum(sum1));
    adder_module adder2(.a(a), .b(~b), .sum(sum2));

    assign sum = select ? sum2 : sum1;

endmodule
module top_module (
    input clk,
    input reset,
    input [31:0] a,
    input [31:0] b,
    input select,
    output [31:0] sum
);

    wire [31:0] sum_out;

    control_logic control(.a(a), .b(b), .select(select), .sum(sum_out));

    register #(32) sum_reg(.clk(clk), .reset(reset), .d(sum_out), .q(sum));

endmodule
module register #(parameter N = 32) (
    input clk,
    input reset,
    input [N-1:0] d,
    output [N-1:0] q
);

    reg [N-1:0] q_reg;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            q_reg <= 0;
        end else begin
            q_reg <= d;
        end
    end

    assign q = q_reg;

endmodule