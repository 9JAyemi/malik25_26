module calculator_sva (
    input logic [3:0] num1,
    input logic [3:0] num2,
    input logic op,
    input logic reset,
    output logic [3:0] result
);
    // Reset behavior: result should be 0 at reset
    reset_behavior: assert property (
        @(posedge clk) disable iff (!reset) (reset |-> result == 4'b0)
    );

    // Operation behavior: result should be num1 - num2 when op is 1
    subtract_behavior: assert property (
        @(posedge clk) disable iff (!reset) (op |-> result == num1 - num2)
    );

    // Operation behavior: result should be num1 + num2 when op is 0
    add_behavior: assert property (
        @(posedge clk) disable iff (!reset) (!op |-> result == num1 + num2)
    );
endmodule