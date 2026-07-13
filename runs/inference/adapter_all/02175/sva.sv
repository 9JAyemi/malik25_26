module Comparator_sva #(
    parameter n = 4
)(
    input logic [n-1:0] in1,
    input logic [n-1:0] in2,
    input logic [1:0]   out
);

    // No RTL clock or reset; sample on the formal global clock.

    // out must always match the RTL comparison result.
    check_out_matches_rtl: assert property (
        @($global_clock) out == ((in1 > in2) ? 2'b01 : ((in1 == in2) ? 2'b00 : 2'b10))
    );

    // Equal inputs must drive out low.
    check_equal_inputs_drive_zero: assert property (
        @($global_clock) (in1 == in2) |-> (out == 2'b00)
    );

    // Greater-than inputs must drive out high.
    check_greater_inputs_drive_one: assert property (
        @($global_clock) (in1 > in2) |-> (out == 2'b01)
    );

    // Less-than inputs must drive out high.
    check_less_inputs_drive_two: assert property (
        @($global_clock) (in1 < in2) |-> (out == 2'b10)
    );

    // out low can only occur when inputs are equal.
    check_zero_output_requires_equal_inputs: assert property (
        @($global_clock) (out == 2'b00) |-> (in1 == in2)
    );

    // out high can only occur when in1 is greater than in2.
    check_one_output_requires_greater_inputs: assert property (
        @($global_clock) (out == 2'b01) |-> (in1 > in2)
    );

    // out high can only occur when in1 is less than in2.
    check_two_output_requires_less_inputs: assert property (
        @($global_clock) (out == 2'b10) |-> (in1 < in2)
    );

endmodule