module comparator_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] result
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // When A is greater than B, result must be 01.
    check_result_when_a_gt_b: assert property (
        @($global_clock) (A > B) |-> (result == 2'b01)
    );

    // When A is less than B, result must be 10.
    check_result_when_a_lt_b: assert property (
        @($global_clock) (A < B) |-> (result == 2'b10)
    );

    // When A equals B, result must be 00.
    check_result_when_a_eq_b: assert property (
        @($global_clock) (A == B) |-> (result == 2'b00)
    );

    // Result 01 can only occur when A is greater than B.
    check_result_01_implies_a_gt_b: assert property (
        @($global_clock) (result == 2'b01) |-> (A > B)
    );

    // Result 10 can only occur when A is less than B.
    check_result_10_implies_a_lt_b: assert property (
        @($global_clock) (result == 2'b10) |-> (A < B)
    );

    // Result 00 can only occur when A equals B.
    check_result_00_implies_a_eq_b: assert property (
        @($global_clock) (result == 2'b00) |-> (A == B)
    );

    // Result must never be 11.
    check_result_never_11: assert property (
        @($global_clock) (result != 2'b11)
    );

endmodule