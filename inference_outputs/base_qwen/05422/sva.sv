```systemverilog
module calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    output logic [7:0] result
);
    // Combinational logic, so use @(posedge clk)
    // Check that the result is correctly calculated based on the operation
    check_result: assert property (
        @(posedge clk) $rose(op) |-> (case(op)
            2'b00: result == A + B;
            2'b01: result == A - B;
            2'b10: result == A * B;
            2'b11: begin
                if(B == 0) result == 0;
                else result == A / B;
            end
            default: result == 0;
        endcase)
    ) else $error("Result calculation is incorrect");

    // Check that the result is not modified when op is not changing
    check_no_change: assert property (
        @(posedge clk) $stable(op) |-> $stable(result)
    ) else $error("Result is modified when operation is not changing");

    // Check that the result is zero when op is not valid
    check_invalid_op: assert property (
        @(posedge clk) (op == 2'b11 && B == 0) |-> result == 0
    ) else $error("Result is not zero when division by zero is attempted");

    // Check that the result is zero when op is not valid
    check_default_op: assert property (
        @(posedge clk) (op != 2'b00 && op != 2'b01 && op != 2'b10 && op != 2'b11) |-> result == 0
    ) else $error("Result is not zero when invalid operation is selected");

endmodule
```