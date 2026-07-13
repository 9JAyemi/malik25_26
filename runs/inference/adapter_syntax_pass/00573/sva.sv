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

    // Y must equal the NOR of A, B, C, and D_N.
    check_nor_function: assert property (
        @($global_clock) Y == ~(A | B | C | D_N)
    );

    // All active-low inputs high must drive Y low.
    check_all_inputs_low_drive_y_low: assert property (
        @($global_clock) (!A && !B && !C && !D_N) |-> !Y
    );

    // A high must force Y low.
    check_a_high_forces_y_low: assert property (
        @($global_clock) A |-> !Y
    );

    // B high must force Y low.
    check_b_high_forces_y_low: assert property (
        @($global_clock) B |-> !Y
    );

    // C high must force Y low.
    check_c_high_forces_y_low: assert property (
        @($global_clock) C |-> !Y
    );

    // D_N high must force Y low.
    check_d_n_high_forces_y_low: assert property (
        @($global_clock) D_N |-> !Y
    );

    // A low Y means all active-low inputs are high.
    check_y_low_implies_all_inputs_low: assert property (
        @($global_clock) !Y |-> (!A && !B && !C && !D_N)
    );

    // A high Y means at least one active-low input is low.
    check_y_high_implies_some_input_low: assert property (
        @($global_clock) Y |-> (A || B || C || D_N)
    );

endmodule