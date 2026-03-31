module bitwise_operations_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [1:0]  operation_select,
    input logic [4:0]  shift_amount,
    input logic [31:0] result
);

    // AND operation selects the bitwise AND result.
    check_and_operation: assert property (
        @(posedge clk) (operation_select == 2'b00) |-> (result == (a & b))
    );

    // OR operation selects the bitwise OR result.
    check_or_operation: assert property (
        @(posedge clk) (operation_select == 2'b01) |-> (result == (a | b))
    );

    // XOR operation selects the bitwise XOR result.
    check_xor_operation: assert property (
        @(posedge clk) (operation_select == 2'b10) |-> (result == (a ^ b))
    );

    // Shift operation selects the left-shifted result.
    check_shift_operation: assert property (
        @(posedge clk) (operation_select == 2'b11) |-> (result == (a << shift_amount))
    );

    // Stable inputs keep the sampled result stable.
    check_stable_inputs_stable_result: assert property (
        @(posedge clk) $stable({a, b, operation_select, shift_amount}) |-> $stable(result)
    );

endmodule