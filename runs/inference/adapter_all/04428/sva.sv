module comparator_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [1:0] result
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // Result must match the RTL compare function.
    check_result_matches_compare: assert property (
        @($global_clock)
        result == ((in0 > in1) ? 2'b01 : ((in0 < in1) ? 2'b10 : 2'b00))
    );

    // Equal inputs must drive 00.
    check_equal_inputs_drive_zero: assert property (
        @($global_clock)
        (in0 == in1) |-> (result == 2'b00)
    );

    // Greater-than inputs must drive 01.
    check_greater_than_drive_one: assert property (
        @($global_clock)
        (in0 > in1) |-> (result == 2'b01)
    );

    // Less-than inputs must drive 10.
    check_less_than_drive_two: assert property (
        @($global_clock)
        (in0 < in1) |-> (result == 2'b10)
    );

    // Result 01 can only occur when in0 is greater than in1.
    check_one_implies_greater_than: assert property (
        @($global_clock)
        (result == 2'b01) |-> (in0 > in1)
    );

    // Result 10 can only occur when in0 is less than in1.
    check_two_implies_less_than: assert property (
        @($global_clock)
        (result == 2'b10) |-> (in0 < in1)
    );

    // Result 00 can only occur when in0 equals in1.
    check_zero_implies_equal: assert property (
        @($global_clock)
        (result == 2'b00) |-> (in0 == in1)
    );

    // Result 11 is never produced by the RTL.
    check_result_never_11: assert property (
        @($global_clock)
        result != 2'b11
    );

endmodule