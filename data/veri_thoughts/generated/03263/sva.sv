module top_module_sva (
    input logic        clk,
    input logic        a,
    input logic        b,
    input logic [31:0] in,
    input logic        select,
    input logic [31:0] out
);

    // When select is low, output is the zero-extended XOR result.
    check_select_low_full: assert property (
        @(posedge clk) (!select) |-> (out == {31'b0, (a ^ b)})
    );

    // When select is low, upper bits are all zero.
    check_select_low_upper_zero: assert property (
        @(posedge clk) (!select) |-> (out[31:1] == 31'b0)
    );

    // When select is low, bit 0 matches a XOR b.
    check_select_low_lsb_xor: assert property (
        @(posedge clk) (!select) |-> (out[0] == (a ^ b))
    );

    // When select is high, output matches the functional path result.
    check_select_high_full: assert property (
        @(posedge clk) select |-> (out == ({31'b0, (a ^ b)} | {in[7:0], in[15:8], in[23:16], in[31:24]}))
    );

    // When select is high, the top byte is in[7:0].
    check_select_high_byte_3: assert property (
        @(posedge clk) select |-> (out[31:24] == in[7:0])
    );

    // When select is high, bits [23:16] are in[15:8].
    check_select_high_byte_2: assert property (
        @(posedge clk) select |-> (out[23:16] == in[15:8])
    );

    // When select is high, bits [15:8] are in[23:16].
    check_select_high_byte_1: assert property (
        @(posedge clk) select |-> (out[15:8] == in[23:16])
    );

    // When select is high, bits [7:1] come from in[31:25].
    check_select_high_low_slice: assert property (
        @(posedge clk) select |-> (out[7:1] == in[31:25])
    );

    // When select is high, bit 0 is reversed bit 0 OR the XOR result.
    check_select_high_lsb_or: assert property (
        @(posedge clk) select |-> (out[0] == (in[24] | (a ^ b)))
    );

    // Output always follows the top-level select mux expression.
    check_top_mux_expression: assert property (
        @(posedge clk) out == (select ? ({31'b0, (a ^ b)} | {in[7:0], in[15:8], in[23:16], in[31:24]}) : {31'b0, (a ^ b)})
    );

endmodule