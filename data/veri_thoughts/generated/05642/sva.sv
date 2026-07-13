module nand3_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y,
    input logic VPWR,
    input logic VGND
);

    // Y matches the RTL 3-input NAND equation.
    check_nand_equation: assert property (
        @($global_clock) Y == ~(A & B & C)
    );

    // All three high inputs force Y low.
    check_all_high_drives_low: assert property (
        @($global_clock) (A && B && C) |-> !Y
    );

    // A low forces Y high.
    check_a_low_drives_high: assert property (
        @($global_clock) !A |-> Y
    );

    // B low forces Y high.
    check_b_low_drives_high: assert property (
        @($global_clock) !B |-> Y
    );

    // C low forces Y high.
    check_c_low_drives_high: assert property (
        @($global_clock) !C |-> Y
    );

    // Y low can only happen when all inputs are high.
    check_low_output_requires_all_high: assert property (
        @($global_clock) !Y |-> (A && B && C)
    );

    // Y high means at least one input is low.
    check_high_output_requires_any_low: assert property (
        @($global_clock) Y |-> (!A || !B || !C)
    );

endmodule