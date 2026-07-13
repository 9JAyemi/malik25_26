module sky130_fd_sc_hdll__nand4bb_sva (
    input  logic clk,
    input  logic Y,
    input  logic A_N,
    input  logic B_N,
    input  logic C,
    input  logic D
);
    // Y equals A_N | B_N | ~C | ~D.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == (A_N | B_N | (~C) | (~D))
    );

    // Y is 0 only when A_N=0, B_N=0, C=1, and D=1.
    check_y_zero_only_in_one_case: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b1) && (D == 1'b1))
    );

    // When C=1 and D=1, Y reduces to A_N | B_N.
    check_reduce_when_c_and_d_high: assert property (
        @(posedge clk) (C && D) |-> (Y == (A_N | B_N))
    );

    // When A_N=0 and B_N=0, Y reduces to ~C | ~D.
    check_reduce_when_a_and_b_low: assert property (
        @(posedge clk) (!A_N && !B_N) |-> (Y == ((~C) | (~D)))
    );

    // A_N=1 forces Y=1.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> (Y == 1'b1)
    );

    // B_N=1 forces Y=1.
    check_b_n_high_forces_y_high: assert property (
        @(posedge clk) B_N |-> (Y == 1'b1)
    );

    // C=0 forces Y=1.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) (!C) |-> (Y == 1'b1)
    );

    // D=0 forces Y=1.
    check_d_low_forces_y_high: assert property (
        @(posedge clk) (!D) |-> (Y == 1'b1)
    );

    // If Y=0 then A_N must be 0.
    check_y_zero_implies_a_n_low: assert property (
        @(posedge clk) (Y == 1'b0) |-> (A_N == 1'b0)
    );

    // If Y=0 then B_N must be 0.
    check_y_zero_implies_b_n_low: assert property (
        @(posedge clk) (Y == 1'b0) |-> (B_N == 1'b0)
    );

    // If Y=0 then C must be 1.
    check_y_zero_implies_c_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (C == 1'b1)
    );

    // If Y=0 then D must be 1.
    check_y_zero_implies_d_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (D == 1'b1)
    );
endmodule