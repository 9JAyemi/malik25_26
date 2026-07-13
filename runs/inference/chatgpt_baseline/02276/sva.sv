module mag_comparator_sva (
    input logic CLK,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);

    // EQ reflects 4-state equality of A and B.
    def_eq_matches_relop: assert property (
        @(posedge CLK) (EQ === (A == B))
    );

    // GT reflects 4-state greater-than of A over B.
    def_gt_matches_relop: assert property (
        @(posedge CLK) (GT === (A > B))
    );

    // LT reflects 4-state less-than of A under B.
    def_lt_matches_relop: assert property (
        @(posedge CLK) (LT === (A < B))
    );

    // When inputs are known (no X/Z), exactly one of EQ/GT/LT is 1.
    onehot_outputs_when_inputs_known: assert property (
        @(posedge CLK) (!$isunknown({A,B})) |=> $onehot({EQ,GT,LT})
    );

    // When inputs are known and equal, EQ=1 and GT/LT=0 in the same cycle.
    eq_case_when_inputs_equal: assert property (
        @(posedge CLK) (!$isunknown({A,B}) && (A == B)) |=> (EQ && !GT && !LT)
    );

    // When inputs are known and A > B, GT=1 and EQ/LT=0 in the same cycle.
    gt_case_when_A_gt_B: assert property (
        @(posedge CLK) (!$isunknown({A,B}) && (A > B)) |=> (GT && !EQ && !LT)
    );

    // When inputs are known and A < B, LT=1 and EQ/GT=0 in the same cycle.
    lt_case_when_A_lt_B: assert property (
        @(posedge CLK) (!$isunknown({A,B}) && (A < B)) |=> (LT && !EQ && !GT)
    );

    // When inputs are known, outputs must be known (no X/Z).
    no_x_on_outputs_when_inputs_known: assert property (
        @(posedge CLK) (!$isunknown({A,B})) |=> (!$isunknown({EQ,GT,LT}))
    );

    // If inputs are stable across cycles, outputs remain stable across cycles.
    outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B}) |=> $stable({EQ,GT,LT})
    );

endmodule