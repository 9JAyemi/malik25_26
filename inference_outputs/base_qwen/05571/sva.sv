module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d1,
    input logic [7:0] d2,
    output logic [7:0] q,
    output logic [7:0] count
);
    // Register module behavior
    // Register q should hold the sum of d1 and d2 when enabled and not reset
    reg_module_behavior: assert property (
        @(posedge clk) disable iff (!reset) (en == 1'b1) |-> (q == d1 + d2)
    );

    // Counter module behavior
    // Counter count should increment by 1 when enabled and not reset
    counter_module_behavior: assert property (
        @(posedge clk) disable iff (!reset) (en == 1'b1) |-> (count == count + 1)
    );

    // Register reset behavior
    // Register q should be reset to 0 when reset is asserted
    reg_reset_behavior: assert property (
        @(posedge clk) !reset |-> (q == 0)
    );

    // Counter reset behavior
    // Counter count should be reset to 0 when reset is asserted
    counter_reset_behavior: assert property (
        @(posedge clk) !reset |-> (count == 0)
    );
endmodule