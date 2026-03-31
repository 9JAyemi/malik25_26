```systemverilog
module calculator_sva (
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [1:0] op,
    output logic [7:0] result
);
    // Addition operation
    add_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 2'b00) |-> (result == num1 + num2)
    );
    // Subtraction operation
    sub_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 2'b01) |-> (result == num1 - num2)
    );
    // Multiplication operation
    mul_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 2'b10) |-> (result == num1 * num2)
    );
    // Division operation
    div_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 2'b11) |-> (result == num1 / num2)
    );
    // Division by zero check
    div_zero_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 2'b11 && num2 == 0) |-> (result == 8'b00000000)
    );
endmodule
```