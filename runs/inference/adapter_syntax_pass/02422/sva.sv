module sky130_fd_sc_hdll__nand4bb_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);

    // Y matches the implemented NAND/OR/BUF function.
    check_output_function: assert property (
        @(posedge clk) Y == ((A_N | B_N) & ~(C & D))
    );

    // A_N high forces Y high.
    check_a_n_forces_y_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // B_N high forces Y high.
    check_b_n_forces_y_high: assert property (
        @(posedge clk) B_N |-> Y
    );

    // C and D both high force Y low.
    check_cd_pair_forces_y_low: assert property (
        @(posedge clk) (C & D) |-> !Y
    );

    // With C and D low, Y reduces to A_N OR B_N.
    check_cd_low_reduces_to_or: assert property (
        @(posedge clk) (!C & !D) |-> (Y == (A_N | B_N))
    );

    // With A_N and B_N low, Y reduces to C AND D.
    check_ab_low_reduces_to_and: assert property (
        @(posedge clk) (!A_N & !B_N) |-> (Y == (C & D))
    );

    // With A_N and B_N high, Y reduces to the NAND of C and D.
    check_ab_high_reduces_to_nand: assert property (
        @(posedge clk) (A_N & B_N) |-> (Y == ~(C & D))
    );

endmodule