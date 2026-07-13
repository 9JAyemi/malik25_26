module sky130_fd_sc_hd__nor2_sva (
    input logic Y,
    input logic A,
    input logic B
);

    // Output always matches the 2-input NOR equation.
    check_nor_equation: assert property (
        @($global_clock) (Y === ~(A | B))
    );

    // Both low inputs drive the output high.
    check_output_high_for_both_low: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b0)) |-> (Y === 1'b1)
    );

    // A high input forces the output low.
    check_output_low_when_a_high: assert property (
        @($global_clock) (A === 1'b1) |-> (Y === 1'b0)
    );

    // B high input forces the output low.
    check_output_low_when_b_high: assert property (
        @($global_clock) (B === 1'b1) |-> (Y === 1'b0)
    );

    // A high output implies both inputs are low.
    check_output_high_implies_both_low: assert property (
        @($global_clock) (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0))
    );

endmodule