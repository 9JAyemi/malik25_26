module comparator_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);
    // EQ equals (A == B).
    check_eq_definition: assert property (
        @(posedge CLK) (EQ === (A == B))
    );

    // GT equals (A > B).
    check_gt_definition: assert property (
        @(posedge CLK) (GT === (A > B))
    );

    // LT equals (A < B).
    check_lt_definition: assert property (
        @(posedge CLK) (LT === (A < B))
    );

    // If EQ is 1 then GT is 0.
    check_eq_excludes_gt: assert property (
        @(posedge CLK) EQ |-> (GT == 1'b0)
    );

    // If EQ is 1 then LT is 0.
    check_eq_excludes_lt: assert property (
        @(posedge CLK) EQ |-> (LT == 1'b0)
    );

    // If GT is 1 then EQ is 0.
    check_gt_excludes_eq: assert property (
        @(posedge CLK) GT |-> (EQ == 1'b0)
    );

    // If GT is 1 then LT is 0.
    check_gt_excludes_lt: assert property (
        @(posedge CLK) GT |-> (LT == 1'b0)
    );

    // If LT is 1 then EQ is 0.
    check_lt_excludes_eq: assert property (
        @(posedge CLK) LT |-> (EQ == 1'b0)
    );

    // If LT is 1 then GT is 0.
    check_lt_excludes_gt: assert property (
        @(posedge CLK) LT |-> (GT == 1'b0)
    );

    // With known inputs, exactly one of {EQ,GT,LT} is 1.
    check_onehot_when_inputs_known: assert property (
        @(posedge CLK) (!$isunknown({A,B})) |-> $onehot({EQ,GT,LT})
    );
endmodule