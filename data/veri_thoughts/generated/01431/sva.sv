module sky130_fd_sc_ms__o32a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // Clocks: none; Reset: none; Type: combinational; Behavior: X = (A1|A2|A3) & (B1|B2)

    // X matches boolean function on A1 posedge.
    check_function_eq_on_A1: assert property (
        @(posedge A1) X == ((A1 | A2 | A3) & (B1 | B2))
    );

    // X matches boolean function on A2 posedge.
    check_function_eq_on_A2: assert property (
        @(posedge A2) X == ((A1 | A2 | A3) & (B1 | B2))
    );

    // X matches boolean function on A3 posedge.
    check_function_eq_on_A3: assert property (
        @(posedge A3) X == ((A1 | A2 | A3) & (B1 | B2))
    );

    // X matches boolean function on B1 posedge.
    check_function_eq_on_B1: assert property (
        @(posedge B1) X == ((A1 | A2 | A3) & (B1 | B2))
    );

    // X matches boolean function on B2 posedge.
    check_function_eq_on_B2: assert property (
        @(posedge B2) X == ((A1 | A2 | A3) & (B1 | B2))
    );

    // If X is HIGH, at least one A and one B input must be HIGH.
    check_x_high_requires_groups_true_on_A1: assert property (
        @(posedge A1) X |-> ((A1 | A2 | A3) && (B1 | B2))
    );

    // If all A inputs are LOW, X must be LOW.
    check_a_group_all_zero_forces_x0_on_B1: assert property (
        @(posedge B1) (~A1 && ~A2 && ~A3) |-> (X == 1'b0)
    );

    // If all B inputs are LOW, X must be LOW.
    check_b_group_all_zero_forces_x0_on_A2: assert property (
        @(posedge A2) (~B1 && ~B2) |-> (X == 1'b0)
    );

    // If at least one A and one B are HIGH, X must be HIGH.
    check_groups_true_implies_x1_on_A3: assert property (
        @(posedge A3) ((A1 | A2 | A3) && (B1 | B2)) |-> (X == 1'b1)
    );

    // Specific sufficient condition: A1 and B1 HIGH implies X HIGH.
    check_a1_b1_implies_x1_on_B1: assert property (
        @(posedge B1) (A1 && B1) |-> (X == 1'b1)
    );
endmodule