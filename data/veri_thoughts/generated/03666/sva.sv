module comparator_4bit_assertions (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] COMP
);

    // Less-than comparison must encode as 00.
    check_less_than_encoding: assert property (
        @($global_clock) (A < B) |-> (COMP == 2'b00)
    );

    // Equality comparison must encode as 01.
    check_equal_encoding: assert property (
        @($global_clock) (A == B) |-> (COMP == 2'b01)
    );

    // Greater-than comparison must encode as 10.
    check_greater_than_encoding: assert property (
        @($global_clock) (A > B) |-> (COMP == 2'b10)
    );

    // Output 00 must only occur when A is less than B.
    check_comp_00_means_less_than: assert property (
        @($global_clock) (COMP == 2'b00) |-> (A < B)
    );

    // Output 01 must only occur when A equals B.
    check_comp_01_means_equal: assert property (
        @($global_clock) (COMP == 2'b01) |-> (A == B)
    );

    // Output 10 must only occur when A is greater than B.
    check_comp_10_means_greater_than: assert property (
        @($global_clock) (COMP == 2'b10) |-> (A > B)
    );

    // The unused 11 encoding must never be driven.
    check_comp_never_11: assert property (
        @($global_clock) COMP != 2'b11
    );

    // COMP must always match the full comparator function.
    check_full_compare_function: assert property (
        @($global_clock) COMP == ((A < B) ? 2'b00 : ((A == B) ? 2'b01 : 2'b10))
    );

endmodule