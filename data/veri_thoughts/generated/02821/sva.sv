module magnitude_comparator_sva (
    input  logic        CLK,
    input  logic        RESETn,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        GT,
    input  logic        EQ
);
    // When A > B, outputs must be GT=1 and EQ=0.
    outputs_for_a_greater: assert property (
        @(posedge CLK) disable iff (!RESETn) (A > B) |-> (GT == 1'b1 && EQ == 1'b0)
    );

    // When A == B, outputs must be GT=0 and EQ=1.
    outputs_for_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == B) |-> (GT == 1'b0 && EQ == 1'b1)
    );

    // When A < B, outputs must be GT=0 and EQ=0.
    outputs_for_a_less: assert property (
        @(posedge CLK) disable iff (!RESETn) (A < B) |-> (GT == 1'b0 && EQ == 1'b0)
    );

    // GT can be 1 only when A > B (and then EQ must be 0).
    gt_only_when_a_greater: assert property (
        @(posedge CLK) disable iff (!RESETn) (GT == 1'b1) |-> ((A > B) && (EQ == 1'b0))
    );

    // EQ can be 1 only when A == B (and then GT must be 0).
    eq_only_when_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) (EQ == 1'b1) |-> ((A == B) && (GT == 1'b0))
    );

    // Combination GT=0 and EQ=0 occurs only when A < B.
    zero_zero_only_when_a_less: assert property (
        @(posedge CLK) disable iff (!RESETn) ((GT == 1'b0) && (EQ == 1'b0)) |-> (A < B)
    );

    // GT and EQ are never both 1 simultaneously.
    gt_eq_mutex: assert property (
        @(posedge CLK) disable iff (!RESETn) !(GT && EQ)
    );

    // GT exactly matches the boolean result of (A > B).
    gt_matches_compare: assert property (
        @(posedge CLK) disable iff (!RESETn) GT == (A > B)
    );

    // EQ exactly matches the boolean result of (A == B).
    eq_matches_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) EQ == (A == B)
    );

    // When A is not greater than B, GT must be 0.
    no_gt_when_not_greater: assert property (
        @(posedge CLK) disable iff (!RESETn) !(A > B) |-> (GT == 1'b0)
    );
endmodule