module xor_product_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] in_1,
    input logic [7:0] in_2,
    input logic select,
    input logic [7:0] xor_output,
    input logic [7:0] or_output
);

// xor_output is the previous cycle's sum XORed with the selected input.
    check_xor_output_function: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (xor_output == ($past(sum) ^ ($past(select) ? in_2 : in_1)))
    );

// or_output is the previous cycle's two's complement of in_1 ANDed with in_2.
    check_or_output_function: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (or_output == (($past(~in_1) + 8'h01) & $past(in_2)))
    );

// When select is low, xor_output uses the previous cycle's in_1.
    check_xor_select_in_1: assert property (
        @(posedge clk) disable iff (reset)
        !select |=> (xor_output == ($past(sum) ^ $past(in_1)))
    );

// When select is high, xor_output uses the previous cycle's in_2.
    check_xor_select_in_2: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (xor_output == ($past(sum) ^ $past(in_2)))
    );

// When select is low, or_output uses the previous cycle's two's complement of in_1.
    check_or_select_in_1: assert property (
        @(posedge clk) disable iff (reset)
        !select |=> (or_output == (($past(~in_1) + 8'h01) & $past(in_2)))
    );

// When select is high, or_output is zero because the two's complement term is zero.
    check_or_select_in_2_zero: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (or_output == 8'h00)
    );

// A zero in_2 forces both outputs to zero on the next cycle.
    check_zero_in2_clears_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (in_2 == 8'h00) |=> ((xor_output == 8'h00) && (or_output == 8'h00))
    );

endmodule
