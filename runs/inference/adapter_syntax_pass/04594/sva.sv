module comparator_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] result
);

    // Result must be 00 when A equals B.
    check_equal_maps_to_zero: assert property (
        @($global_clock) (A == B) |-> (result == 2'b00)
    );

    // Result must be 01 when A is greater than B.
    check_greater_maps_to_one: assert property (
        @($global_clock) (A > B) |-> (result == 2'b01)
    );

    // Result must be 10 when A is less than B.
    check_less_maps_to_two: assert property (
        @($global_clock) (A < B) |-> (result == 2'b10)
    );

    // Result must never be 11.
    check_result_never_three: assert property (
        @($global_clock) (result != 2'b11)
    );

    // Result must never be 01 and 10 simultaneously.
    check_result_not_both_one_and_two: assert property (
        @($global_clock) !(result == 2'b01 && result == 2'b10)
    );

endmodule