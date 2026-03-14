module magnitude_comparator_4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);
    // EQ reflects A == B.
    check_eq_definition: assert property (
        @(posedge CLK) (EQ == (A == B))
    );
    // GT reflects A > B.
    check_gt_definition: assert property (
        @(posedge CLK) (GT == (A > B))
    );
    // LT reflects A < B.
    check_lt_definition: assert property (
        @(posedge CLK) (LT == (A < B))
    );
    // When A == B, only EQ is high.
    check_eq_mapping: assert property (
        @(posedge CLK) (A == B) |-> (EQ && !GT && !LT)
    );
    // When A > B, only GT is high.
    check_gt_mapping: assert property (
        @(posedge CLK) (A > B) |-> (GT && !EQ && !LT)
    );
    // When A < B, only LT is high.
    check_lt_mapping: assert property (
        @(posedge CLK) (A < B) |-> (LT && !EQ && !GT)
    );
    // Outputs are one-hot across EQ/GT/LT.
    check_outputs_onehot: assert property (
        @(posedge CLK) $onehot({EQ, GT, LT})
    );
    // If inputs are stable, outputs remain stable (purely combinational behavior).
    check_stability_with_stable_inputs: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable({EQ, GT, LT})
    );
endmodule