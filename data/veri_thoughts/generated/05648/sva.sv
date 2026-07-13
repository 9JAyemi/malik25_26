module AND4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Z
);

    // Z must match the four-input AND of A, B, C, and D.
    check_and_function: assert property (
        @(posedge clk) Z == (A & B & C & D)
    );

    // A high output requires all four inputs to be high.
    check_high_output_requires_all_high: assert property (
        @(posedge clk) Z |-> (A && B && C && D)
    );

    // All four high inputs must drive the output high.
    check_all_high_drives_output_high: assert property (
        @(posedge clk) (A && B && C && D) |-> Z
    );

    // Any low input must force the output low.
    check_any_low_forces_output_low: assert property (
        @(posedge clk) (!A || !B || !C || !D) |-> !Z
    );

endmodule