module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

    // Output must equal the AND of the two inputs.
    check_y_matches_and: assert property (
        @(posedge clk) Y == (A & B)
    );

    // Both inputs high must drive the output high.
    check_both_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A && B) |-> Y
    );

    // A low must force the output low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) (!A) |-> (!Y)
    );

    // B low must force the output low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) (!B) |-> (!Y)
    );

    // A high output requires both inputs high.
    check_y_high_requires_both_inputs_high: assert property (
        @(posedge clk) Y |-> (A && B)
    );

endmodule