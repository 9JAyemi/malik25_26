module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic select,
    output logic [31:0] sum
);
    // Register reset behavior
    register_reset: assert property (
        @(posedge clk) disable iff (!reset) sum == 32'b0
    ) else $error("Register not reset to 0 on reset");

    // Sequential logic in control logic
    control_logic_seq: assert property (
        @(posedge clk) disable iff (!reset) (select ? sum == a - b : sum == a + b)
    ) else $error("Control logic does not correctly select between addition and subtraction");

    // Sequential logic in register
    register_seq: assert property (
        @(posedge clk) disable iff (!reset) sum == sum_out
    ) else $error("Register does not hold the value of sum_out");

endmodule