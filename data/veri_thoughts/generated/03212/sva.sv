module sky130_fd_sc_ls__nor4bb_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // Y equals the implemented NOR/AND function of the inputs.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ((~A) & (~B) & C_N & D_N)
    );

    // A high forces the NOR term low and keeps Y low.
    check_a_blocks_output: assert property (
        @(posedge clk) A |-> !Y
    );

    // B high forces the NOR term low and keeps Y low.
    check_b_blocks_output: assert property (
        @(posedge clk) B |-> !Y
    );

    // C_N low blocks the final AND and keeps Y low.
    check_c_n_low_blocks_output: assert property (
        @(posedge clk) !C_N |-> !Y
    );

    // D_N low blocks the final AND and keeps Y low.
    check_d_n_low_blocks_output: assert property (
        @(posedge clk) !D_N |-> !Y
    );

    // When all enabling conditions are met, Y is high.
    check_output_high_condition: assert property (
        @(posedge clk) ((~A) & (~B) & C_N & D_N) |-> Y
    );

    // Y high implies the exact enabling input combination.
    check_output_high_implies_inputs: assert property (
        @(posedge clk) Y |-> ((~A) & (~B) & C_N & D_N)
    );

endmodule