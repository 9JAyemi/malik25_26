module comparator_4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);
    ///// Functional equivalence to comparisons /////
    // EQ must reflect (A == B).
    check_eq_definition: assert property (
        @(posedge CLK) EQ == (A == B)
    );
    // GT must reflect (A > B).
    check_gt_definition: assert property (
        @(posedge CLK) GT == (A > B)
    );
    // LT must reflect (A < B).
    check_lt_definition: assert property (
        @(posedge CLK) LT == (A < B)
    );

    ///// Output consistency /////
    // Exactly one of {EQ, GT, LT} is HIGH.
    check_outputs_onehot: assert property (
        @(posedge CLK) $onehot({EQ, GT, LT})
    );
    // If not equal, exactly one of GT or LT is HIGH.
    check_not_eq_xor: assert property (
        @(posedge CLK) (!EQ) |-> (GT ^ LT)
    );
endmodule