module unsigned_comparator_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);
    // DUT is pure combinational; assertions are clocked on CLK and gated by active-low RESETn.

    // EQ must reflect A == B.
    check_eq_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) (EQ == (A == B))
    );

    // GT must reflect A > B.
    check_gt_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) (GT == (A > B))
    );

    // LT must reflect A < B.
    check_lt_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) (LT == (A < B))
    );

    // Exactly one of {EQ, GT, LT} must be HIGH.
    check_outputs_onehot: assert property (
        @(posedge CLK) disable iff (!RESETn) $onehot({EQ, GT, LT})
    );

    // If EQ is HIGH, GT and LT must be LOW.
    check_eq_excludes_others: assert property (
        @(posedge CLK) disable iff (!RESETn) EQ |-> (!GT && !LT)
    );

    // If GT is HIGH, EQ and LT must be LOW.
    check_gt_excludes_others: assert property (
        @(posedge CLK) disable iff (!RESETn) GT |-> (!EQ && !LT)
    );

    // If LT is HIGH, EQ and GT must be LOW.
    check_lt_excludes_others: assert property (
        @(posedge CLK) disable iff (!RESETn) LT |-> (!EQ && !GT)
    );

    // EQ must equal the negation of (GT or LT).
    check_eq_is_complement_of_gt_or_lt: assert property (
        @(posedge CLK) disable iff (!RESETn) (EQ == !(GT || LT))
    );

endmodule