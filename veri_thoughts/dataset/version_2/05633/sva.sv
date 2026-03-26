module my_or4_1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // No clock or reset exists in the RTL; sample on the formal global clock.

    // X must always equal the OR of all four inputs.
    check_output_matches_or: assert property (
        @($global_clock) X == (A | B | C | D)
    );

    // If all inputs are low, X must be low.
    check_all_low_drives_x_low: assert property (
        @($global_clock) !(A | B | C | D) |-> !X
    );

    // A high must force X high.
    check_a_high_drives_x_high: assert property (
        @($global_clock) A |-> X
    );

    // B high must force X high.
    check_b_high_drives_x_high: assert property (
        @($global_clock) B |-> X
    );

    // C high must force X high.
    check_c_high_drives_x_high: assert property (
        @($global_clock) C |-> X
    );

    // D high must force X high.
    check_d_high_drives_x_high: assert property (
        @($global_clock) D |-> X
    );

    // A high X must come from at least one high input.
    check_x_high_has_input_source: assert property (
        @($global_clock) X |-> (A | B | C | D)
    );

    // A low X means all inputs are low.
    check_x_low_means_all_inputs_low: assert property (
        @($global_clock) !X |-> !(A | B | C | D)
    );

endmodule