module adder_sva (
    input logic CLK,
    input logic RESETn,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [8:0] res
);
    ///// Functional correctness /////
    // res equals 9-bit sum of in1 and in2.
    check_res_equals_sum: assert property (
        @(posedge CLK) disable iff (!RESETn) res == (in1 + in2)
    );
    // res[8] equals the carry-out of in1 + in2.
    check_carry_equals_sum_bit8: assert property (
        @(posedge CLK) disable iff (!RESETn) res[8] == (in1 + in2)[8]
    );
    // res[7:0] equals the lower 8 bits of in1 + in2.
    check_lower8_equals_sum_mod256: assert property (
        @(posedge CLK) disable iff (!RESETn) res[7:0] == (in1 + in2)[7:0]
    );

    ///// Identities and boundary cases /////
    // Adding zero on in1 yields res = {0,in2}.
    check_zero_plus_identity1: assert property (
        @(posedge CLK) disable iff (!RESETn) (in1 == 8'd0) |-> (res == {1'b0, in2})
    );
    // Adding zero on in2 yields res = {0,in1}.
    check_zero_plus_identity2: assert property (
        @(posedge CLK) disable iff (!RESETn) (in2 == 8'd0) |-> (res == {1'b0, in1})
    );
    // Result is within the possible 8-bit addition range (<= 510).
    check_result_within_possible_range: assert property (
        @(posedge CLK) disable iff (!RESETn) res <= 9'h1FE
    );

    ///// Carry behavior /////
    // If both MSBs are 1, carry-out must be 1.
    check_carry_when_both_msb_one: assert property (
        @(posedge CLK) disable iff (!RESETn) (in1[7] && in2[7]) |-> (res[8] == 1'b1)
    );
    // If both MSBs are 0, carry-out must be 0.
    check_no_carry_when_both_msb_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (!in1[7] && !in2[7]) |-> (res[8] == 1'b0)
    );
    // With carry-out, the low 8 bits are less than both operands.
    check_low_less_both_on_carry: assert property (
        @(posedge CLK) disable iff (!RESETn) res[8] |-> ((res[7:0] < in1) && (res[7:0] < in2))
    );
    // Without carry-out, the low 8 bits are at least each operand.
    check_low_ge_operands_no_carry: assert property (
        @(posedge CLK) disable iff (!RESETn) !res[8] |-> ((res[7:0] >= in1) && (res[7:0] >= in2))
    );
endmodule