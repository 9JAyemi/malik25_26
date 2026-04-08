module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);

    // out_always selects b when both select inputs are high.
    check_out_always_selects_b: assert property (
        @(posedge clk) (sel_b1 & sel_b2) |-> (out_always == b)
    );

    // out_always selects a when both select inputs are not high.
    check_out_always_selects_a: assert property (
        @(posedge clk) !(sel_b1 & sel_b2) |-> (out_always == a)
    );

    // out_and is the 4-input AND of a, b, sel_b1, and sel_b2.
    check_out_and_is_four_input_and: assert property (
        @(posedge clk) out_and == (a & b & sel_b1 & sel_b2)
    );

    // out_or is the 4-input OR of a, b, sel_b1, and sel_b2.
    check_out_or_is_four_input_or: assert property (
        @(posedge clk) out_or == (a | b | sel_b1 | sel_b2)
    );

    // out_xor is the 4-input XOR of a, b, sel_b1, and sel_b2.
    check_out_xor_is_four_input_xor: assert property (
        @(posedge clk) out_xor == (a ^ b ^ sel_b1 ^ sel_b2)
    );

endmodule