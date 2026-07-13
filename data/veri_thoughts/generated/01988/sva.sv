module signed_mag_comp_sva (
    input logic CLK,
    input logic signed [3:0] A,
    input logic signed [3:0] B,
    input logic EQ,
    input logic GT
);
    // EQ equals signed equality of A and B.
    eq_reflects_signed_equality: assert property (
        @(posedge CLK) (EQ == (A == B))
    );

    // GT equals signed greater-than of A over B.
    gt_reflects_signed_gt: assert property (
        @(posedge CLK) (GT == (A > B))
    );

    // EQ and GT are never both 1.
    check_outputs_mutex: assert property (
        @(posedge CLK) !(EQ && GT)
    );

    // When A < B, outputs are both 0.
    less_case_outputs_zero_zero: assert property (
        @(posedge CLK) (A < B) |-> (!EQ && !GT)
    );

    // Outputs both 0 only when A < B.
    zero_zero_implies_less: assert property (
        @(posedge CLK) (!EQ && !GT) |-> (A < B)
    );

    // When A != B, EQ is 0.
    neq_implies_eq_zero: assert property (
        @(posedge CLK) (A != B) |-> (EQ == 1'b0)
    );
endmodule