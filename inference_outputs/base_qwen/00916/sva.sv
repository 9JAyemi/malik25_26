```systemverilog
module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);
    // Addition operation
    add_check: assert property (
        @(posedge clk) disable iff (!rst_n) (op == 2'b00) |-> (result == a + b)
    );
    // Subtraction operation
    sub_check: assert property (
        @(posedge clk) disable iff (!rst_n) (op == 2'b01) |-> (result == a - b)
    );
    // Multiplication operation
    mul_check: assert property (
        @(posedge clk) disable iff (!rst_n) (op == 2'b10) |-> (result == a * b)
    );
    // Division operation
    div_check: assert property (
        @(posedge clk) disable iff (!rst_n) (op == 2'b11) |-> (result == a / b)
    );
    // Reset behavior
    reset_check: assert property (
        @(posedge clk) !rst_n |-> (result == 8'b0)
    );
endmodule
```