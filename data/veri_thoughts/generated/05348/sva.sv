module calculator_sva (
    input logic clk,
    input logic signed [31:0] a,
    input logic signed [31:0] b,
    input logic op,
    input logic signed [31:0] result
);

    // When op is 0, result must be the signed sum of a and b.
    check_add_operation: assert property (
        @(posedge clk)
        (op === 1'b0) |-> (result == ($signed(a) + $signed(b)))
    );

    // When op is not 0, result must be the signed difference of a and b.
    check_sub_operation: assert property (
        @(posedge clk)
        (op !== 1'b0) |-> (result == ($signed(a) - $signed(b)))
    );

    // If all inputs are stable, the sampled result must remain stable.
    check_stable_inputs_stable_result: assert property (
        @(posedge clk)
        ($stable(a) && $stable(b) && $stable(op)) |-> $stable(result)
    );

endmodule