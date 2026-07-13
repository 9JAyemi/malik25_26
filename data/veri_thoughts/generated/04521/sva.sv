module three_input_or_gate_sva (
    input logic A,
    input logic B,
    input logic C_N,
    input logic X,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X matches the implemented OR of the inputs and power pins.
    check_x_matches_or_expression: assert property (
        @($global_clock) X == (A | B | ~C_N | VPWR | VGND | VPB | VNB)
    );

    // A high makes X high.
    check_a_high_forces_x_high: assert property (
        @($global_clock) (A == 1'b1) |-> (X == 1'b1)
    );

    // B high makes X high.
    check_b_high_forces_x_high: assert property (
        @($global_clock) (B == 1'b1) |-> (X == 1'b1)
    );

    // C_N low makes X high.
    check_c_n_low_forces_x_high: assert property (
        @($global_clock) (C_N == 1'b0) |-> (X == 1'b1)
    );

    // VPWR high makes X high.
    check_vpwr_high_forces_x_high: assert property (
        @($global_clock) (VPWR == 1'b1) |-> (X == 1'b1)
    );

    // VGND high makes X high.
    check_vgnd_high_forces_x_high: assert property (
        @($global_clock) (VGND == 1'b1) |-> (X == 1'b1)
    );

    // VPB high makes X high.
    check_vpb_high_forces_x_high: assert property (
        @($global_clock) (VPB == 1'b1) |-> (X == 1'b1)
    );

    // VNB high makes X high.
    check_vnb_high_forces_x_high: assert property (
        @($global_clock) (VNB == 1'b1) |-> (X == 1'b1)
    );

    // X is low when every OR term is inactive.
    check_all_terms_inactive_make_x_low: assert property (
        @($global_clock)
        ((A == 1'b0) && (B == 1'b0) && (C_N == 1'b1) &&
         (VPWR == 1'b0) && (VGND == 1'b0) && (VPB == 1'b0) && (VNB == 1'b0))
        |-> (X == 1'b0)
    );

    // X low means every OR term is inactive.
    check_x_low_means_all_terms_inactive: assert property (
        @($global_clock)
        (X == 1'b0)
        |-> ((A == 1'b0) && (B == 1'b0) && (C_N == 1'b1) &&
             (VPWR == 1'b0) && (VGND == 1'b0) && (VPB == 1'b0) && (VNB == 1'b0))
    );

endmodule