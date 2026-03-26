module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        select,
    input logic [7:0]  out,
    input logic [31:0] sum,
    input logic [7:0]  upper_byte,
    input logic [7:0]  lower_byte,
    input logic [7:0]  product,
    input logic [15:0] sum_low,
    input logic [15:0] sum_high,
    input logic        carry_out_low,
    input logic        carry_out_high
);

    // Lower ripple adder output matches a[15:0] + b[15:0].
    check_ripple_low_add: assert property (
        @(posedge clk) ({carry_out_low, sum_low} == (a[15:0] + b[15:0]))
    );

    // Upper ripple adder output matches a[31:16] + b[31:16].
    check_ripple_high_add: assert property (
        @(posedge clk) ({carry_out_high, sum_high} == (a[31:16] + b[31:16]))
    );

    // Lower half of sum follows the carry-select lower assignment.
    check_carry_select_lower_half: assert property (
        @(posedge clk) (sum[15:0] == (carry_out_low ? sum_high : sum_low))
    );

    // Upper half of sum follows the carry-select upper assignment.
    check_carry_select_upper_half: assert property (
        @(posedge clk) (sum[31:16] == (carry_out_high ? (sum_high + 16'd1) : sum_high))
    );

    // upper_byte is sum[15:8].
    check_decoder_upper_byte: assert property (
        @(posedge clk) (upper_byte == sum[15:8])
    );

    // lower_byte is sum[7:0].
    check_decoder_lower_byte: assert property (
        @(posedge clk) (lower_byte == sum[7:0])
    );

    // product is the low 8 bits of upper_byte * lower_byte.
    check_functional_product: assert property (
        @(posedge clk) ({8'h00, product} == ((upper_byte * lower_byte) & 16'h00ff))
    );

    // When select is high, out follows product.
    check_output_select_product: assert property (
        @(posedge clk) select |-> (out == product)
    );

    // When select is low, the 16-bit decoder path truncates to lower_byte.
    check_output_select_decoder_low_byte: assert property (
        @(posedge clk) !select |-> (out == lower_byte)
    );

    // out matches the implemented 8-bit mux behavior.
    check_output_mux_behavior: assert property (
        @(posedge clk) (out == (select ? product : lower_byte))
    );

endmodule