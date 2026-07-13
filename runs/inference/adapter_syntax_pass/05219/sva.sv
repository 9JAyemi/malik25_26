module xor_gate_sva (
    input logic A,
    input logic B,
    input logic X,
    input logic VPWR,
    input logic VGND
);

    // X must equal A XOR B.
    check_xor_function: assert property (
        @($global_clock) X == (A ^ B)
    );

    // When A and B are equal, X must be low.
    check_equal_inputs_low: assert property (
        @($global_clock) (A == B) |-> (X == 1'b0)
    );

    // When A and B differ, X must be high.
    check_different_inputs_high: assert property (
        @($global_clock) (A != B) |-> (X == 1'b1)
    );

    // A high X means the inputs differ.
    check_high_output_implies_inputs_different: assert property (
        @($global_clock) (X == 1'b1) |-> (A != B)
    );

    // A low X means the inputs are equal.
    check_low_output_implies_inputs_equal: assert property (
        @($global_clock) (X == 1'b0) |-> (A == B)
    );

endmodule