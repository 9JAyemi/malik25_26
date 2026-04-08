module sky130_fd_sc_lp__nor4bb_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // Y matches the implemented combinational function.
    check_output_function: assert property (
        @(posedge clk) Y == ((~(A | B)) & C_N & D_N)
    );

    // A high forces the NOR stage low, so Y must be low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> !Y
    );

    // B high forces the NOR stage low, so Y must be low.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) B |-> !Y
    );

    // C_N low blocks the AND stage, so Y must be low.
    check_cn_low_forces_y_low: assert property (
        @(posedge clk) !C_N |-> !Y
    );

    // D_N low blocks the AND stage, so Y must be low.
    check_dn_low_forces_y_low: assert property (
        @(posedge clk) !D_N |-> !Y
    );

    // All enabling inputs produce a high output.
    check_enabling_inputs_drive_y_high: assert property (
        @(posedge clk) (!A && !B && C_N && D_N) |-> Y
    );

    // A high output implies the required input combination.
    check_y_high_implies_input_combination: assert property (
        @(posedge clk) Y |-> (!A && !B && C_N && D_N)
    );

endmodule