module Comparator_sva #(
    parameter n = 4
)(
    input logic [n-1:0] in1,
    input logic [n-1:0] in2,
    input logic [1:0] out
);

    // out must be 00 when the inputs are equal.
    check_equal_maps_to_zero: assert property (
        @($global_clock) (in1 == in2) |-> (out == 2'b00)
    );

    // out must be 01 when in1 is greater than in2.
    check_greater_maps_to_one: assert property (
        @($global_clock) (in1 > in2) |-> (out == 2'b01)
    );

    // out must be 10 when in1 is less than in2.
    check_less_maps_to_two: assert property (
        @($global_clock) (in1 < in2) |-> (out == 2'b10)
    );

    // out must never be 11.
    check_out_never_11: assert property (
        @($global_clock) (out != 2'b11)
    );

    // out must always be one of the three defined encodings.
    check_out_is_valid: assert property (
        @($global_clock) (out inside {2'b00, 2'b01, 2'b10})
    );

endmodule