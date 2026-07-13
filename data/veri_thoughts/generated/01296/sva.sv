module top_module_sva (
    input logic CLK,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic sel_logic_or,
    input logic sel_inverse,
    input logic [2:0] out_or,
    input logic [2:0] out_bitwise,
    input logic [5:0] out_not
);
    // Expected OR of (possibly inverted) inputs used by both output selections
    wire [2:0] expected_or = sel_inverse ? (~a | ~b) : (a | b);

    // out_not lower bits are bitwise NOT of a
    check_out_not_lower: assert property (
        @(posedge CLK) out_not[2:0] == ~a
    );

    // out_not upper bits are bitwise NOT of b
    check_out_not_upper: assert property (
        @(posedge CLK) out_not[5:3] == ~b
    );

    // When sel_logic_or=0, out_or is forced to zero
    check_out_or_zero_when_sel0: assert property (
        @(posedge CLK) (sel_logic_or == 1'b0) |-> (out_or == 3'b000)
    );

    // When sel_logic_or=1, out_bitwise is forced to zero
    check_out_bitwise_zero_when_sel1: assert property (
        @(posedge CLK) (sel_logic_or == 1'b1) |-> (out_bitwise == 3'b000)
    );

    // When sel_logic_or=1, out_or equals OR of selected (possibly inverted) inputs
    check_out_or_value_when_sel1: assert property (
        @(posedge CLK) (sel_logic_or == 1'b1) |-> (out_or == expected_or)
    );

    // When sel_logic_or=0, out_bitwise equals OR of selected (possibly inverted) inputs
    check_out_bitwise_value_when_sel0: assert property (
        @(posedge CLK) (sel_logic_or == 1'b0) |-> (out_bitwise == expected_or)
    );

    // The OR of the two outputs equals the expected OR result
    check_outputs_or_combined_equals_expected: assert property (
        @(posedge CLK) (out_or | out_bitwise) == expected_or
    );

    // The two outputs are bitwise disjoint
    check_outputs_bitwise_disjoint: assert property (
        @(posedge CLK) (out_or & out_bitwise) == 3'b000
    );

    // If out_or is zero then either it is deselected or the expected result is zero
    check_out_or_zero_implication: assert property (
        @(posedge CLK) (out_or == 3'b000) |-> ((sel_logic_or == 1'b0) || (expected_or == 3'b000))
    );

    // If out_bitwise is zero then either it is deselected or the expected result is zero
    check_out_bitwise_zero_implication: assert property (
        @(posedge CLK) (out_bitwise == 3'b000) |-> ((sel_logic_or == 1'b1) || (expected_or == 3'b000))
    );
endmodule