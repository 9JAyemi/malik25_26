```systemverilog
module simple_calculator_sva (
    input signed [7:0] a,
    input signed [7:0] b,
    input [1:0] op,
    output reg signed [7:0] add_out,
    output reg signed [7:0] sub_out,
    output reg signed [7:0] mul_out,
    output reg signed [7:0] div_out
);
    // Addition operation
    add_check: assert property (
        @(posedge clk) disable iff (!reset_n) (op == 2'b00) |-> (add_out == a + b)
    );

    // Subtraction operation
    sub_check: assert property (
        @(posedge clk) disable iff (!reset_n) (op == 2'b01) |-> (sub_out == a - b)
    );

    // Multiplication operation
    mul_check: assert property (
        @(posedge clk) disable iff (!reset_n) (op == 2'b10) |-> (mul_out == a * b)
    );

    // Division operation
    div_check: assert property (
        @(posedge clk) disable iff (!reset_n) (op == 2'b11) |-> (div_out == a / b)
    );

    // Reset behavior
    reset_check: assert property (
        @(posedge clk) disable iff (!reset_n) (reset_n == 1'b0) |-> (add_out == 0 && sub_out == 0 && mul_out == 0 && div_out == 0)
    );
endmodule
```