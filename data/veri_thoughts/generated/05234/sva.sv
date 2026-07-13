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

    // X implements the inverted four-input AND.
    check_nand_function: assert property (
        @($global_clock) X == ~(A & B & C & D)
    );

    // All four inputs high drive X low.
    check_all_high_drives_low: assert property (
        @($global_clock) (A && B && C && D) |-> (X == 1'b0)
    );

    // Any low input drives X high.
    check_any_low_drives_high: assert property (
        @($global_clock) ((!A) || (!B) || (!C) || (!D)) |-> (X == 1'b1)
    );

    // X low implies all four inputs are high.
    check_low_output_requires_all_high: assert property (
        @($global_clock) (X == 1'b0) |-> (A && B && C && D)
    );

    // X high implies at least one input is low.
    check_high_output_requires_some_low: assert property (
        @($global_clock) (X == 1'b1) |-> ((!A) || (!B) || (!C) || (!D))
    );

endmodule