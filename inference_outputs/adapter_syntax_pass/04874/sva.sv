module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must equal the AND of A, B, and C.
    check_y_matches_and_function: assert property (
        @(posedge clk) Y == (A & B & C)
    );

    // All three high inputs must drive Y high.
    check_all_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A && B && C) |-> Y
    );

    // A low input must force Y low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !A |-> !Y
    );

    // B low input must force Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

    // C low input must force Y low.
    check_c_low_forces_y_low: assert property (
        @(posedge clk) !C |-> !Y
    );

endmodule