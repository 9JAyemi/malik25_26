module arithmetic_op_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] ctrl,
    input logic [7:0] result
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // ctrl=00 selects the 8-bit add result.
    check_add_result: assert property (
        @($global_clock) (ctrl == 2'b00) |-> (result == (a + b))
    );

    // ctrl=01 selects the 8-bit subtract result.
    check_sub_result: assert property (
        @($global_clock) (ctrl == 2'b01) |-> (result == (a - b))
    );

    // ctrl=10 selects the bitwise XOR result.
    check_xor_result: assert property (
        @($global_clock) (ctrl == 2'b10) |-> (result == (a ^ b))
    );

    // ctrl=11 selects the default zero result.
    check_default_zero_result: assert property (
        @($global_clock) (ctrl == 2'b11) |-> (result == 8'h00)
    );

    // With stable inputs, the combinational result must remain stable.
    check_stable_inputs_stable_result: assert property (
        @($global_clock) ($stable(a) && $stable(b) && $stable(ctrl)) |-> $stable(result)
    );

endmodule