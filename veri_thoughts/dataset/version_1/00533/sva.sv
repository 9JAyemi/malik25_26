module arithmetic_op_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] ctrl,
    input logic [7:0] result
);

    // Addition select drives result to a + b.
    check_add_operation: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (result == (a + b))
    );

    // Subtraction select drives result to a - b.
    check_sub_operation: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (result == (a - b))
    );

    // AND select drives result to a & b.
    check_and_operation: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (result == (a & b))
    );

    // OR select drives result to a | b.
    check_or_operation: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (result == (a | b))
    );

    // Stable inputs keep the sampled result stable.
    check_stable_inputs_hold_result: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $stable(ctrl)) |-> $stable(result)
    );

endmodule