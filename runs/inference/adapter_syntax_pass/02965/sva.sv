module two_bit_comparator_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] C
);

    // C must be 00 when A equals B.
    check_equal_maps_to_zero: assert property (
        @($global_clock) (A == B) |-> (C == 2'b00)
    );

    // C must be 01 when A is greater than B.
    check_greater_maps_to_one: assert property (
        @($global_clock) (A > B) |-> (C == 2'b01)
    );

    // C must be 10 when A is less than B.
    check_less_maps_to_two: assert property (
        @($global_clock) (A < B) |-> (C == 2'b10)
    );

    // C must always be one of the three defined encodings.
    check_output_encoding: assert property (
        @($global_clock) (C inside {2'b00, 2'b01, 2'b10})
    );

    // C must never be 11.
    check_output_not_three: assert property (
        @($global_clock) (C != 2'b11)
    );

endmodule