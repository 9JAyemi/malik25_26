module my_nand4_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND
);

    // No RTL clock or reset; sample this combinational DUT on the formal global clock.

    // Y always matches the 4-input NAND of A, B, C, and D.
    check_output_matches_nand_function: assert property (
        @($global_clock) (Y == ~(A & B & C & D))
    );

    // All four HIGH inputs drive Y LOW.
    check_all_inputs_high_drive_y_low: assert property (
        @($global_clock)
        ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1)) |-> (Y == 1'b0)
    );

    // A LOW forces Y HIGH.
    check_a_low_forces_y_high: assert property (
        @($global_clock) (A == 1'b0) |-> (Y == 1'b1)
    );

    // B LOW forces Y HIGH.
    check_b_low_forces_y_high: assert property (
        @($global_clock) (B == 1'b0) |-> (Y == 1'b1)
    );

    // C LOW forces Y HIGH.
    check_c_low_forces_y_high: assert property (
        @($global_clock) (C == 1'b0) |-> (Y == 1'b1)
    );

    // D LOW forces Y HIGH.
    check_d_low_forces_y_high: assert property (
        @($global_clock) (D == 1'b0) |-> (Y == 1'b1)
    );

endmodule