module sky130_fd_sc_hd__lpflow_inputiso1n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);
    // X implements X = A | ~SLEEP_B.
    check_function_equation: assert property (
        @(posedge clk) X == (A | (~SLEEP_B))
    );

    // When SLEEP_B is LOW, X must be HIGH.
    check_sleep_forces_high: assert property (
        @(posedge clk) (SLEEP_B == 1'b0) |-> (X == 1'b1)
    );

    // When SLEEP_B is HIGH, X must equal A.
    check_awake_pass_through: assert property (
        @(posedge clk) (SLEEP_B == 1'b1) |-> (X == A)
    );

    // When SLEEP_B is HIGH and A is LOW, X must be LOW.
    check_awake_low_results_low: assert property (
        @(posedge clk) (SLEEP_B == 1'b1 && A == 1'b0) |-> (X == 1'b0)
    );

    // When SLEEP_B is HIGH and A is HIGH, X must be HIGH.
    check_awake_high_results_high: assert property (
        @(posedge clk) (SLEEP_B == 1'b1 && A == 1'b1) |-> (X == 1'b1)
    );

    // On A rising while SLEEP_B is HIGH, X must be HIGH in the same cycle.
    check_rise_A_awake: assert property (
        @(posedge clk) (SLEEP_B == 1'b1 && $rose(A)) |-> (X == 1'b1)
    );

    // On A falling while SLEEP_B is HIGH, X must be LOW in the same cycle.
    check_fall_A_awake: assert property (
        @(posedge clk) (SLEEP_B == 1'b1 && $fell(A)) |-> (X == 1'b0)
    );

    // On SLEEP_B falling, X must be forced HIGH in the same cycle.
    check_sleepb_fall_forces_high: assert property (
        @(posedge clk) $fell(SLEEP_B) |-> (X == 1'b1)
    );

    // On SLEEP_B rising, X must equal A in the same cycle.
    check_sleepb_rise_restores_passthrough: assert property (
        @(posedge clk) $rose(SLEEP_B) |-> (X == A)
    );

    // If X is LOW, then A is LOW and SLEEP_B is HIGH.
    check_zero_output_implies_inputs_zero: assert property (
        @(posedge clk) (X == 1'b0) |-> ((A == 1'b0) && (SLEEP_B == 1'b1))
    );
endmodule