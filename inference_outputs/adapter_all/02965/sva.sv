module two_bit_comparator_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] C
);

    // C must match the RTL compare result for all input combinations.
    check_compare_result: assert property (
        @($global_clock) C == ((A == B) ? 2'b00 : ((A > B) ? 2'b01 : 2'b10))
    );

    // Equal inputs must drive C to 00.
    check_equal_case: assert property (
        @($global_clock) (A == B) |-> (C == 2'b00)
    );

    // A greater than B must drive C to 01.
    check_greater_case: assert property (
        @($global_clock) (A > B) |-> (C == 2'b01)
    );

    // A less than B must drive C to 10.
    check_less_case: assert property (
        @($global_clock) (A < B) |-> (C == 2'b10)
    );

    // C must never drive the unused 11 encoding.
    check_c_range: assert property (
        @($global_clock) C inside {2'b00, 2'b01, 2'b10}
    );

endmodule