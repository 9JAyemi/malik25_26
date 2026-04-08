module my_module_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP
);

    // No reset exists in the RTL; this checker uses an external sampling clock.

    // X must always match the implemented sleep-gated function.
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (1'b0)
        (X == (!SLEEP ? A : 1'b0))
    );

    // When SLEEP is high, X is forced low.
    check_sleep_forces_low: assert property (
        @(posedge clk) disable iff (1'b0)
        SLEEP |-> (X == 1'b0)
    );

    // When SLEEP is low, X must mirror A.
    check_awake_passes_a: assert property (
        @(posedge clk) disable iff (1'b0)
        (!SLEEP) |-> (X == A)
    );

    // A high X can only occur when A is high and SLEEP is low.
    check_high_x_requires_awake_high_a: assert property (
        @(posedge clk) disable iff (1'b0)
        X |-> ((!SLEEP) && A)
    );

endmodule