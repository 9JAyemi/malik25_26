module xor_product_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] in_1,
    input logic [7:0] in_2,
    input logic select,
    input logic [7:0] xor_output,
    input logic [7:0] or_output
);

    // xor_output is the previous cycle's adder output XORed with the selected input.
    check_xor_output_definition: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (xor_output == ($past(in_1) + $past(in_2)) ^ ($past(select) ? $past(in_2) : $past(in_1)))
    );

    // or_output is the previous cycle's two's complement of in_1 ANDed with in_2.
    check_or_output_definition: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (or_output == (($past(in_1) == 8'h00) ? 8'h00 : (~$past(in_1) + 8'h01)) & $past(in_2))
    );

    // or_output is zero whenever the previous cycle's in_1 was zero.
    check_or_output_zero_when_in1_zero: assert property (
        @(posedge clk) disable iff (reset)
        (in_1 == 8'h00) |=> (or_output == 8'h00)
    );

    // or_output is zero whenever the previous cycle's in_2 was zero.
    check_or_output_zero_when_in2_zero: assert property (
        @(posedge clk) disable iff (reset)
        (in_2 == 8'h00) |=> (or_output == 8'h00)
    );

    // or_output is zero whenever the previous cycle's in_1 was all ones.
    check_or_output_zero_when_in1_all_ones: assert property (
        @(posedge clk) disable iff (reset)
        (in_1 == 8'hFF) |=> (or_output == 8'h00)
    );

    // or_output is equal to in_2 whenever the previous cycle's in_1 was one.
    check_or_output_equals_in2_when_in1_one: assert property (
        @(posedge clk) disable iff (reset)
        (in_1 == 8'h01) |=> (or_output == $past(in_2))
    );

    // or_output is equal to the previous cycle's in_2 whenever the previous cycle's in_1 was zero.
    check_or_output_equals_in2_when_in1_zero: assert property (
        @(posedge clk) disable iff (reset)
        (in_1 == 8'h00) |=> (or_output == $past(in_2))
    );

    // or_output is equal to the previous cycle's in_2 whenever the previous cycle's in_1 was all ones.
    check_or_output_equals_in2_when_in1_all_ones: assert property (
        @(posedge clk) disable iff (reset)
        (in_1 == 8'hFF) |=> (or_output == $past(in_2))
    );

endmodule