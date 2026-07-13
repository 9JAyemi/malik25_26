module xor_product_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] in_1,
    input logic [7:0] in_2,
    input logic select,
    input logic [7:0] xor_output,
    input logic [7:0] or_output
);

    // xor_output is the registered adder sum XORed with the selected input.
    check_xor_output_matches_registered_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (xor_output == (($past(in_1) + $past(in_2)) ^ ($past(select) ? $past(in_2) : $past(in_1))))
    );

    // or_output is the registered two's complement of in_1 ANDed with in_2.
    check_or_output_matches_registered_twos_and: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (or_output == ((~$past(in_1) + 8'h01) & $past(in_2)))
    );

    // xor_output also matches the adder sum XORed with the non-selected input.
    check_xor_output_matches_registered_nonselected_input: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (xor_output == (($past(in_1) + $past(in_2)) ^ ($past(select) ? $past(in_1) : $past(in_2))))
    );

    // or_output is also the registered adder sum ANDed with the selected input.
    check_or_output_matches_registered_sum_and_selected_input: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (or_output == (($past(in_1) + $past(in_2)) & ($past(select) ? $past(in_2) : $past(in_1))))
    );

    // xor_output and or_output are never both zero.
    check_outputs_never_both_zero: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((xor_output != 8'h00) || (or_output != 8'h00))
    );

    // xor_output and or_output are never both all ones.
    check_outputs_never_both_all_ones: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((xor_output != 8'hFF) || (or_output != 8'hFF))
    );

    // xor_output and or_output are never equal.
    check_outputs_never_equal: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (xor_output != or_output)
    );

    // or_output is always a subset of the adder sum.
    check_or_output_subset_of_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((or_output & ~($past(in_1) + $past(in_2))) == 8'h00)
    );

    // xor_output is always a subset of the selected input.
    check_xor_output_subset_of_selected_input: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((xor_output & ~($past(select) ? $past(in_2) : $past(in_1))) == 8'h00)
    );

    // or_output is always a subset of the non-selected input.
    check_or_output_subset_of_nonselected_input: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((or_output & ~($past(select) ? $past(in_1) : $past(in_2))) == 8'h00)
    );

    // xor_output is always a subset of the adder sum.
    check_xor_output_subset_of_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((xor_output & ~($past(in_1) + $past(in_2))) == 8'h00)
    );

endmodule