module add_three_module_assertions (
    input logic [3:0] A,
    input logic [3:0] result
);

    // Result must always equal A plus 3 modulo 16.
    check_add_three_function: assert property (
        @($global_clock) result == (A + 4'b0011)
    );

    // Zero input must produce 3.
    check_zero_input_mapping: assert property (
        @($global_clock) (A == 4'b0000) |-> (result == 4'b0011)
    );

    // Input 12 must produce 15 before wraparound.
    check_upper_non_wrap_boundary: assert property (
        @($global_clock) (A == 4'b1100) |-> (result == 4'b1111)
    );

    // Input 13 must wrap around to 0.
    check_wrap_start_mapping: assert property (
        @($global_clock) (A == 4'b1101) |-> (result == 4'b0000)
    );

    // Maximum input must wrap around to 2.
    check_max_input_mapping: assert property (
        @($global_clock) (A == 4'b1111) |-> (result == 4'b0010)
    );

endmodule