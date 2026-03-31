module four_input_and_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // X must equal the inverted AND of all four inputs.
    check_x_matches_inverted_and: assert property (
        @($global_clock) X == ~((A & B) & (C & D))
    );

    // All inputs high must drive X low.
    check_all_inputs_high_drive_x_low: assert property (
        @($global_clock) (A & B & C & D) |-> (X == 1'b0)
    );

    // A low must drive X high.
    check_a_low_drives_x_high: assert property (
        @($global_clock) !A |-> (X == 1'b1)
    );

    // B low must drive X high.
    check_b_low_drives_x_high: assert property (
        @($global_clock) !B |-> (X == 1'b1)
    );

    // C low must drive X high.
    check_c_low_drives_x_high: assert property (
        @($global_clock) !C |-> (X == 1'b1)
    );

    // D low must drive X high.
    check_d_low_drives_x_high: assert property (
        @($global_clock) !D |-> (X == 1'b1)
    );

    // X low implies all inputs are high.
    check_x_low_implies_all_inputs_high: assert property (
        @($global_clock) (X == 1'b0) |-> (A & B & C & D)
    );

    // X high implies at least one input is low.
    check_x_high_implies_some_input_low: assert property (
        @($global_clock) (X == 1'b1) |-> (!A || !B || !C || !D)
    );

endmodule