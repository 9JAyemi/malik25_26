module arithmetic_op_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] ctrl,
    input logic [7:0] result
);

    // ctrl=00 selects the 8-bit sum of a and b.
    check_add_operation: assert property (
        @($global_clock) (ctrl == 2'b00) |-> (result == (a + b))
    );

    // ctrl=01 selects the 8-bit difference of a and b.
    check_sub_operation: assert property (
        @($global_clock) (ctrl == 2'b01) |-> (result == (a - b))
    );

    // ctrl=10 selects the bitwise XOR of a and b.
    check_xor_operation: assert property (
        @($global_clock) (ctrl == 2'b10) |-> (result == (a ^ b))
    );

    // ctrl=11 selects the default zero output.
    check_default_zero: assert property (
        @($global_clock) (ctrl == 2'b11) |-> (result == 8'h00)
    );

endmodule