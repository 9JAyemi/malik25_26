module sky130_fd_sc_hdll__nor4b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

    // Y implements the NOR4-with-inverted-D function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == (!A && !B && !C && D_N)
    );

    // A asserted forces the NOR output low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> !Y
    );

    // B asserted forces the NOR output low.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) B |-> !Y
    );

    // C asserted forces the NOR output low.
    check_c_high_forces_y_low: assert property (
        @(posedge clk) C |-> !Y
    );

    // D_N low makes the inverted D input high and forces Y low.
    check_dn_low_forces_y_low: assert property (
        @(posedge clk) !D_N |-> !Y
    );

    // Y high requires all three direct inputs low and D_N high.
    check_y_high_only_for_all_clear: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && D_N)
    );

    // When all three direct inputs are low and D_N is high, Y is high.
    check_all_clear_drives_y_high: assert property (
        @(posedge clk) (!A && !B && !C && D_N) |-> Y
    );

endmodule