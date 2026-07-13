module bitwise_operations_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [1:0]  operation_select,
    input logic [4:0]  shift_amount,
    input logic [31:0] result
);

    // No reset in the RTL; assertions sample combinational behavior on clk.

    // AND mode drives result with a & b.
    check_and_mode_result: assert property (
        @(posedge clk) (operation_select == 2'b00) |-> (result == (a & b))
    );

    // OR mode drives result with a | b.
    check_or_mode_result: assert property (
        @(posedge clk) (operation_select == 2'b01) |-> (result == (a | b))
    );

    // XOR mode drives result with a ^ b.
    check_xor_mode_result: assert property (
        @(posedge clk) (operation_select == 2'b10) |-> (result == (a ^ b))
    );

    // Shift mode drives result with a left shift by shift_amount.
    check_shift_mode_result: assert property (
        @(posedge clk) (operation_select == 2'b11) |-> (result == (a << shift_amount))
    );

    // If all inputs are unchanged, result must remain unchanged.
    check_stable_inputs_hold_result: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $stable(operation_select) && $stable(shift_amount)) |-> $stable(result)
    );

    // In AND/OR/XOR modes, shift_amount must not affect result.
    check_shift_amount_ignored_in_logic_modes: assert property (
        @(posedge clk) ((operation_select != 2'b11) && $stable(a) && $stable(b) && $stable(operation_select)) |-> $stable(result)
    );

    // In shift mode, b must not affect result.
    check_b_ignored_in_shift_mode: assert property (
        @(posedge clk) ((operation_select == 2'b11) && $stable(a) && $stable(shift_amount) && $stable(operation_select)) |-> $stable(result)
    );

endmodule