module comparator_sva (
    input  logic        CLK,   // Sampling clock for assertions (DUT is combinational)
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        EQ,
    input  logic        GT,
    input  logic        LT
);
    ///// Comparator behavior /////
    // Exactly one of EQ/GT/LT must be HIGH.
    check_outputs_onehot: assert property (
        @(posedge CLK) $onehot({EQ, GT, LT})
    );

    // When A == B, outputs must be EQ=1, GT=0, LT=0.
    check_equal_maps_to_EQ: assert property (
        @(posedge CLK) (A == B) |-> (EQ && !GT && !LT)
    );

    // When A > B, outputs must be EQ=0, GT=1, LT=0.
    check_greater_maps_to_GT: assert property (
        @(posedge CLK) (A > B) |-> (!EQ && GT && !LT)
    );

    // When A < B, outputs must be EQ=0, GT=0, LT=1.
    check_less_maps_to_LT: assert property (
        @(posedge CLK) (A < B) |-> (!EQ && !GT && LT)
    );

    // If EQ is 1, then A must equal B.
    check_EQ_implies_equal: assert property (
        @(posedge CLK) EQ |-> (A == B)
    );

    // If GT is 1, then A must be greater than B.
    check_GT_implies_greater: assert property (
        @(posedge CLK) GT |-> (A > B)
    );

    // If LT is 1, then A must be less than B.
    check_LT_implies_less: assert property (
        @(posedge CLK) LT |-> (A < B)
    );

    // Outputs are never all zero.
    check_not_all_zero: assert property (
        @(posedge CLK) (EQ || GT || LT)
    );
endmodule