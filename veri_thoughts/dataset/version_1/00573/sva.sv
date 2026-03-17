module sky130_fd_sc_hd__nor4b_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y matches the RTL NOR expression.
    check_nor4b_function: assert property (
        @($global_clock) Y == ~(A | B | C | D_N)
    );

    // All four low inputs drive Y high.
    check_all_low_drives_y_high: assert property (
        @($global_clock) (!A && !B && !C && !D_N) |-> Y
    );

    // Any high input drives Y low.
    check_any_high_drives_y_low: assert property (
        @($global_clock) (A || B || C || D_N) |-> !Y
    );

    // Y high means every input is low.
    check_y_high_requires_all_low: assert property (
        @($global_clock) Y |-> (!A && !B && !C && !D_N)
    );

    // Y low means at least one input is high.
    check_y_low_requires_any_high: assert property (
        @($global_clock) !Y |-> (A || B || C || D_N)
    );

endmodule