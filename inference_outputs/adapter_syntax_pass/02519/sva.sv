module addsub_sva (
    input logic [15:0] A,
    input logic [15:0] B,
    input logic        C,
    input logic [15:0] Q
);

    // Q must match the selected arithmetic operation.
    check_selected_operation: assert property (
        @($global_clock) Q == ((C == 1'b1) ? (A - B) : (A + B))
    );

    // When C is low, Q must be the 16-bit sum of A and B.
    check_add_mode: assert property (
        @($global_clock) (C == 1'b0) |-> (Q == (A + B))
    );

    // When C is high, Q must be the 16-bit difference of A and B.
    check_sub_mode: assert property (
        @($global_clock) (C == 1'b1) |-> (Q == (A - B))
    );

    // With B at zero, Q must pass A regardless of C.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 16'h0000) |-> (Q == A)
    );

    // With A at zero, Q must pass B when adding and zero when subtracting.
    check_zero_a_behavior: assert property (
        @($global_clock) (A == 16'h0000) |-> ((C == 1'b0) ? (Q == B) : (Q == 16'h0000))
    );

endmodule