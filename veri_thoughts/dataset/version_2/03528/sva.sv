module comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] C
);

    // A greater-than comparison drives 01.
    check_greater_than_result: assert property (
        @($global_clock) (A > B) |-> (C == 2'b01)
    );

    // A less-than comparison drives 10.
    check_less_than_result: assert property (
        @($global_clock) (A < B) |-> (C == 2'b10)
    );

    // Equal inputs drive 00.
    check_equal_result: assert property (
        @($global_clock) (A == B) |-> (C == 2'b00)
    );

    // Unequal inputs drive one of the nonzero compare codes.
    check_unequal_inputs_encoding: assert property (
        @($global_clock) (A != B) |-> ((C == 2'b01) || (C == 2'b10))
    );

    // The comparator never produces 11.
    check_output_never_11: assert property (
        @($global_clock) (C != 2'b11)
    );

    // Stable inputs keep the output stable.
    check_stable_inputs_stable_output: assert property (
        @($global_clock) (!$initstate && $stable(A) && $stable(B)) |-> $stable(C)
    );

endmodule