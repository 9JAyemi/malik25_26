module simple_calculator_sva (
    input logic clk,
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic signed [7:0] add_out,
    input logic signed [7:0] sub_out,
    input logic signed [7:0] mul_out,
    input logic signed [7:0] div_out,
    input logic [1:0] op
);

// Addition mode drives add_out to a+b and the other outputs to zero.
    check_add_mode: assert property (
        @(posedge clk) (op == 2'b00) |-> (add_out == (a + b)) && (sub_out == 8'sd0) && (mul_out == 8'sd0) && (div_out == 8'sd0)
    );

// Subtraction mode drives sub_out to a-b and the other outputs to zero.
    check_sub_mode: assert property (
        @(posedge clk) (op == 2'b01) |-> (add_out == 8'sd0) && (sub_out == (a - b)) && (mul_out == 8'sd0) && (div_out == 8'sd0)
    );

// Multiplication mode drives mul_out to a*b and the other outputs to zero.
    check_mul_mode: assert property (
        @(posedge clk) (op == 2'b10) |-> (add_out == 8'sd0) && (sub_out == 8'sd0) && (mul_out == (a * b)) && (div_out == 8'sd0)
    );

// Division mode drives div_out to a/b and the other outputs to zero.
    check_div_mode: assert property (
        @(posedge clk) (op == 2'b11) |-> (add_out == 8'sd0) && (sub_out == 8'sd0) && (mul_out == 8'sd0) && (div_out == (a / b))
    );

// When op is 00, add_out equals a+b and the other outputs are zero.
    check_add_out_when_add: assert property (
        @(posedge clk) (op == 2'b00) |-> (add_out == (a + b))
    );

// When op is 01, sub_out equals a-b and the other outputs are zero.
    check_sub_out_when_sub: assert property (
        @(posedge clk) (op == 2'b01) |-> (sub_out == (a - b))
    );

// When op is 10, mul_out equals a*b and the other outputs are zero.
    check_mul_out_when_mul: assert property (
        @(posedge clk) (op == 2'b10) |-> (mul_out == (a * b))
    );

// When op is 11, div_out equals a/b and the other outputs are zero.
    check_div_out_when_div: assert property (
        @(posedge clk) (op == 2'b11) |-> (div_out == (a / b))
    );

endmodule
