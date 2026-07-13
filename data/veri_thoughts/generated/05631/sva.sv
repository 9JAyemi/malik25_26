module top_module_sva (
    input logic clk,
    input logic [2:0] in,
    input logic select,
    input logic and_result,
    input logic or_result,
    input logic xor_result
);

    // and_result is masked low when select is high, else it is the 3-input AND.
    check_and_output_function: assert property (
        @(posedge clk)
        and_result == (select ? 1'b0 : (in[0] & in[1] & in[2]))
    );

    // or_result passes the 3-input OR when select is high, else it is low.
    check_or_output_function: assert property (
        @(posedge clk)
        or_result == (select ? (in[0] | in[1] | in[2]) : 1'b0)
    );

    // xor_result is always the XOR of the raw AND and raw OR results.
    check_xor_output_function: assert property (
        @(posedge clk)
        xor_result == ((in[0] & in[1] & in[2]) ^ (in[0] | in[1] | in[2]))
    );

    // When select is high, AND is blocked and OR is selected.
    check_select_high_routing: assert property (
        @(posedge clk)
        select |-> ((and_result == 1'b0) && (or_result == (in[0] | in[1] | in[2])))
    );

    // When select is low, OR is blocked and AND is selected.
    check_select_low_routing: assert property (
        @(posedge clk)
        !select |-> ((and_result == (in[0] & in[1] & in[2])) && (or_result == 1'b0))
    );

    // All outputs are low when all inputs are low.
    check_all_zero_input_case: assert property (
        @(posedge clk)
        (in == 3'b000) |-> ((and_result == 1'b0) && (or_result == 1'b0) && (xor_result == 1'b0))
    );

    // xor_result is high for any nonzero input pattern that is not all ones.
    check_partial_one_input_xor_high: assert property (
        @(posedge clk)
        ((in != 3'b000) && (in != 3'b111)) |-> (xor_result == 1'b1)
    );

    // xor_result is low when all inputs are high.
    check_all_one_input_xor_low: assert property (
        @(posedge clk)
        (in == 3'b111) |-> (xor_result == 1'b0)
    );

endmodule