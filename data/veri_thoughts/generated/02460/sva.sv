module sky130_fd_sc_ls__o2111a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);
    // No clock/reset in RTL; pure combinational: X = B1 & C1 & D1 & (A1 | A2)

    // X equals the Boolean function on any A1 edge.
    check_function_on_A1_edge: assert property (
        @(posedge A1 or negedge A1) X == (B1 & C1 & D1 & (A1 | A2))
    );

    // X equals the Boolean function on any A2 edge.
    check_function_on_A2_edge: assert property (
        @(posedge A2 or negedge A2) X == (B1 & C1 & D1 & (A1 | A2))
    );

    // X equals the Boolean function on any B1 edge.
    check_function_on_B1_edge: assert property (
        @(posedge B1 or negedge B1) X == (B1 & C1 & D1 & (A1 | A2))
    );

    // X equals the Boolean function on any C1 edge.
    check_function_on_C1_edge: assert property (
        @(posedge C1 or negedge C1) X == (B1 & C1 & D1 & (A1 | A2))
    );

    // X equals the Boolean function on any D1 edge.
    check_function_on_D1_edge: assert property (
        @(posedge D1 or negedge D1) X == (B1 & C1 & D1 & (A1 | A2))
    );

    // X equals the Boolean function on any X edge.
    check_function_on_X_edge: assert property (
        @(posedge X or negedge X) X == (B1 & C1 & D1 & (A1 | A2))
    );

    // If B1 is LOW, X must be LOW.
    check_B1_zero_forces_X_zero: assert property (
        @(posedge B1 or negedge B1) (!B1) |-> (X == 1'b0)
    );

    // If C1 is LOW, X must be LOW.
    check_C1_zero_forces_X_zero: assert property (
        @(posedge C1 or negedge C1) (!C1) |-> (X == 1'b0)
    );

    // If D1 is LOW, X must be LOW.
    check_D1_zero_forces_X_zero: assert property (
        @(posedge D1 or negedge D1) (!D1) |-> (X == 1'b0)
    );

    // If both A1 and A2 are LOW, X must be LOW.
    check_A_both_low_forces_X_zero: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2) (!A1 && !A2) |-> (X == 1'b0)
    );

    // On a rising edge of X, all gating inputs must be HIGH and at least one of A1/A2 must be HIGH.
    check_X_rise_requires_all_inputs_high: assert property (
        @(posedge X) (B1 && C1 && D1 && (A1 || A2))
    );

endmodule