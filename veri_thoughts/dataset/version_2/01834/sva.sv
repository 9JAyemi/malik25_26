module LOA_sva #(parameter int LPL=10, parameter int W=16) (
    input logic CLK,
    input logic [W - 1:0] in1,
    input logic [W - 1:0] in2,
    input logic [W:0] res
);
    // RTL has no clock/reset; assertions are sampled on CLK only.
    default clocking cb @(posedge CLK); endclocking

    // Parameters must yield legal slice widths (matches RTL structure).
    check_param_legal: assert property (
        (LPL >= 1) && (W > LPL)
    );

    // Lower LPL result bits are bitwise OR of inputs.
    check_lower_or: assert property (
        res[LPL-1:0] == (in1[LPL-1:0] | in2[LPL-1:0])
    );

    // Upper part equals upper addends plus carry-in from bit LPL-1 AND.
    check_upper_sum_with_cin: assert property (
        res[W:LPL] == ({1'b0, in1[W-1:LPL]} + {1'b0, in2[W-1:LPL]} + (in1[LPL-1] & in2[LPL-1]))
    );

    // Full output matches the RTL concatenation of upper sum and lower OR.
    check_full_concat: assert property (
        res == {({1'b0, in1[W-1:LPL]} + {1'b0, in2[W-1:LPL]} + (in1[LPL-1] & in2[LPL-1])), (in1[LPL-1:0] | in2[LPL-1:0])}
    );

    // If lower OR is zero, both lower input parts must be zero.
    check_lower_zero_implies_inputs_zero: assert property (
        (res[LPL-1:0] == '0) |-> ((in1[LPL-1:0] == '0) && (in2[LPL-1:0] == '0))
    );

    // When not both LPL-1 bits are 1, carry-in to upper add is zero.
    check_no_cin_when_not_both_one: assert property (
        !(in1[LPL-1] & in2[LPL-1]) |-> (res[W:LPL] == ({1'b0, in1[W-1:LPL]} + {1'b0, in2[W-1:LPL]}))
    );

    // When both LPL-1 bits are 1, carry-in to upper add is one.
    check_cin_when_both_one: assert property (
        (in1[LPL-1] & in2[LPL-1]) |-> (res[W:LPL] == ({1'b0, in1[W-1:LPL]} + {1'b0, in2[W-1:LPL]} + 1'b1))
    );

    // MSB of res equals carry-out of the upper addition with carry-in.
    check_top_carry_matches_add: assert property (
        res[W] == (({1'b0, in1[W-1:LPL]} + {1'b0, in2[W-1:LPL]} + (in1[LPL-1] & in2[LPL-1]))[W-LPL])
    );

    // If both inputs are zero, result must be zero.
    check_zero_inputs_zero_output: assert property (
        ((in1 == '0) && (in2 == '0)) |-> (res == '0)
    );

    // Bit LPL-1 of result equals OR of input bits at LPL-1.
    check_boundary_bit_or: assert property (
        res[LPL-1] == (in1[LPL-1] | in2[LPL-1])
    );
endmodule