module my_and_gate_sva (
    input logic A,
    input logic B,
    input logic X
);

    // X must equal the NAND of A and B.
    check_x_is_nand_of_inputs: assert property (
        @($global_clock) X == ~(A & B)
    );

    // When both inputs are high, X must be low.
    check_both_high_drive_low: assert property (
        @($global_clock) (A && B) |-> !X
    );

    // When A is low, X must be high.
    check_a_low_drives_high: assert property (
        @($global_clock) !A |-> X
    );

    // When B is low, X must be high.
    check_b_low_drives_high: assert property (
        @($global_clock) !B |-> X
    );

    // A low output implies both inputs are high.
    check_low_output_only_when_both_high: assert property (
        @($global_clock) !X |-> (A && B)
    );

endmodule