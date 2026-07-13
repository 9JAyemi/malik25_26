module top_module_sva (
    input logic clk,
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [15:0] product
);

// Product equals the 8-bit inputs multiplied together.
    check_product_matches_multiplication: assert property (
        @(posedge clk) product == {8'h00, num1} * {8'h00, num2}
    );

// LSB of product equals num1[0] AND num2[0].
    check_lsb_matches_bitwise_and: assert property (
        @(posedge clk) product[0] == (num1[0] & num2[0])
    );

// Upper byte of product equals the 16-bit multiplication result.
    check_upper_byte_matches_16bit_product: assert property (
        @(posedge clk) product[15:8] == ({8'h00, num1} * {8'h00, num2})[15:8]
    );

// Zero on num1 forces the entire product to zero.
    check_zero_on_num1_clears_product: assert property (
        @(posedge clk) (num1 == 8'h00) |-> (product == 16'h0000)
    );

// Zero on num2 forces the entire product to zero.
    check_zero_on_num2_clears_product: assert property (
        @(posedge clk) (num2 == 8'h00) |-> (product == 16'h0000)
    );

// Maximum 8-bit inputs produce the maximum 16-bit product.
    check_max_inputs_produce_max_product: assert property (
        @(posedge clk) ((num1 == 8'hFF) && (num2 == 8'hFF)) |-> (product == 16'hFFFF)
    );

// 8'hFF on num1 with num2 == 1 produces num1 in the lower byte.
    check_ff_times_one_lower_byte: assert property (
        @(posedge clk) ((num1 == 8'hFF) && (num2 == 8'h01)) |-> (product == {8'h00, num1})
    );

// 8'hFF on num2 with num1 == 1 produces num2 in the lower byte.
    check_ff_times_one_upper_byte: assert property (
        @(posedge clk) ((num2 == 8'hFF) && (num1 == 8'h01)) |-> (product == {8'h00, num2})
    );

endmodule
