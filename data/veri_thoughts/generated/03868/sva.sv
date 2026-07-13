module my_and_gate_sva (
    input logic A,
    input logic B,
    input logic Y
);

    // Y must equal the AND of A and B.
    check_and_function: assert property (
        @($global_clock) Y === (A & B)
    );

    // Both inputs high must drive Y high.
    check_both_high_drive_y_high: assert property (
        @($global_clock) ((A === 1'b1) && (B === 1'b1)) |-> (Y === 1'b1)
    );

    // A low must force Y low.
    check_a_low_forces_y_low: assert property (
        @($global_clock) (A === 1'b0) |-> (Y === 1'b0)
    );

    // B low must force Y low.
    check_b_low_forces_y_low: assert property (
        @($global_clock) (B === 1'b0) |-> (Y === 1'b0)
    );

    // Y high implies both inputs are high.
    check_y_high_implies_both_high: assert property (
        @($global_clock) (Y === 1'b1) |-> ((A === 1'b1) && (B === 1'b1))
    );

endmodule