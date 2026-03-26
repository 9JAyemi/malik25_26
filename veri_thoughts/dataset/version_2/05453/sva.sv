module nand_gate_sva (
    input logic A,
    input logic B,
    input logic Z
);

    // Z always equals the NAND of A and B.
    check_nand_function: assert property (
        @($global_clock) Z == ~(A & B)
    );

    // If both inputs are high, Z must be low.
    check_both_high_drive_low: assert property (
        @($global_clock) ((A == 1'b1) && (B == 1'b1)) |-> (Z == 1'b0)
    );

    // If A is low, Z must be high.
    check_a_low_drive_high: assert property (
        @($global_clock) (A == 1'b0) |-> (Z == 1'b1)
    );

    // If B is low, Z must be high.
    check_b_low_drive_high: assert property (
        @($global_clock) (B == 1'b0) |-> (Z == 1'b1)
    );

endmodule