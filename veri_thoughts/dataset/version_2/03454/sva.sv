module mag_comparator_sva (
    input logic clk,
    input logic [2:0] A,
    input logic [2:0] B,
    input logic [1:0] result
);

    // Result matches the implemented comparator function.
    check_function_map: assert property (
        @(posedge clk) result == ((A == B) ? 2'b00 : ((A > B) ? 2'b01 : 2'b10))
    );

    // Equal inputs produce 00.
    check_equal_case: assert property (
        @(posedge clk) (A == B) |-> (result == 2'b00)
    );

    // A greater than B produces 01.
    check_greater_case: assert property (
        @(posedge clk) (A > B) |-> (result == 2'b01)
    );

    // A less than B produces 10.
    check_less_case: assert property (
        @(posedge clk) (A < B) |-> (result == 2'b10)
    );

    // 00 indicates equal inputs.
    check_result_equal_encoding: assert property (
        @(posedge clk) (result == 2'b00) |-> (A == B)
    );

    // 01 indicates A is greater than B.
    check_result_greater_encoding: assert property (
        @(posedge clk) (result == 2'b01) |-> (A > B)
    );

    // 10 indicates A is less than B.
    check_result_less_encoding: assert property (
        @(posedge clk) (result == 2'b10) |-> (A < B)
    );

    // 11 is never a valid output encoding.
    check_no_invalid_encoding: assert property (
        @(posedge clk) (result != 2'b11)
    );

    // Stable inputs keep the output stable.
    check_stable_inputs_stable_result: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(result)
    );

endmodule