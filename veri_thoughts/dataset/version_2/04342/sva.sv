module top_module_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        enable,
    input logic [1:0]  comp_out,
    input logic [15:0] dec_out,
    input logic [3:0]  final_out,
    input logic [3:0]  result
);

    // EQ reflects A == B.
    check_comparator_eq_flag: assert property (
        @(posedge clk) comp_out[0] == (A == B)
    );

    // GT reflects A > B.
    check_comparator_gt_flag: assert property (
        @(posedge clk) comp_out[1] == (A > B)
    );

    // Comparator never produces the unused 11 code.
    check_comparator_valid_codes: assert property (
        @(posedge clk) comp_out != 2'b11
    );

    // Decoder drives the low nibble from comp_out and keeps upper bits zero.
    check_decoder_mapping: assert property (
        @(posedge clk)
        dec_out == {12'b0,
                    (~comp_out[1] & ~comp_out[0]),
                    (~comp_out[1] &  comp_out[0]),
                    ( comp_out[1] & ~comp_out[0]),
                    ( comp_out[1] &  comp_out[0])}
    );

    // Functional maps decoder code 2 to output 1.
    check_functional_eq_code: assert property (
        @(posedge clk)
        (dec_out == 16'b0000000000000010) |-> (final_out == 4'b0001)
    );

    // Functional maps decoder code 4 to output 2.
    check_functional_gt_code: assert property (
        @(posedge clk)
        (dec_out == 16'b0000000000000100) |-> (final_out == 4'b0010)
    );

    // Functional maps decoder code 8 to output 4.
    check_functional_11_code: assert property (
        @(posedge clk)
        (dec_out == 16'b0000000000001000) |-> (final_out == 4'b0100)
    );

    // Functional drives zero for all other decoder values.
    check_functional_default_zero: assert property (
        @(posedge clk)
        (dec_out != 16'b0000000000000010 &&
         dec_out != 16'b0000000000000100 &&
         dec_out != 16'b0000000000001000) |-> (final_out == 4'b0000)
    );

    // Result is zero when enable is low.
    check_result_disabled_zero: assert property (
        @(posedge clk) !enable |-> (result == 4'b0000)
    );

    // Result follows final_out when enable is high.
    check_result_enabled_follows_final: assert property (
        @(posedge clk) enable |-> (result == final_out)
    );

    // Top-level result matches the implemented compare/decode/function chain.
    check_result_end_to_end: assert property (
        @(posedge clk)
        result == (enable ? ((A == B) ? 4'b0001 :
                             ((A > B) ? 4'b0010 : 4'b0000)) :
                            4'b0000)
    );

endmodule