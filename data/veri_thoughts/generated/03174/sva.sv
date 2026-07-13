module sky130_fd_sc_hd__and4bb_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);

    // X implements (~A_N & ~B_N & C & D).
    check_output_matches_function: assert property (
        @(posedge clk) X == ((!A_N) && (!B_N) && C && D)
    );

    // All required input conditions drive X HIGH.
    check_output_high_when_all_terms_true: assert property (
        @(posedge clk) ((!A_N) && (!B_N) && C && D) |-> X
    );

    // X HIGH implies every input term is satisfied.
    check_output_high_implies_valid_inputs: assert property (
        @(posedge clk) X |-> ((!A_N) && (!B_N) && C && D)
    );

    // A_N HIGH forces X LOW.
    check_a_n_high_forces_output_low: assert property (
        @(posedge clk) A_N |-> !X
    );

    // B_N HIGH forces X LOW.
    check_b_n_high_forces_output_low: assert property (
        @(posedge clk) B_N |-> !X
    );

    // C LOW or D LOW forces X LOW.
    check_c_or_d_low_forces_output_low: assert property (
        @(posedge clk) ((!C) || (!D)) |-> !X
    );

    // Stable inputs keep the combinational output stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) $stable({A_N, B_N, C, D}) |-> $stable(X)
    );

endmodule