module binary_adder_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       C,
    input logic [7:0] S
);

    // When C is low, S must be the sum of A and B.
    check_add_mode: assert property (
        @($global_clock) !C |-> (S == (A + B))
    );

    // When C is high, S must be the difference of A and B.
    check_sub_mode: assert property (
        @($global_clock) C |-> (S == (A - B))
    );

    // S must always match the operation selected by C.
    check_selected_operation: assert property (
        @($global_clock) S == (C ? (A - B) : (A + B))
    );

    // If the inputs stay the same, the output must stay the same.
    check_stable_inputs_hold_output: assert property (
        @($global_clock) $stable({A, B, C}) |-> $stable(S)
    );

endmodule