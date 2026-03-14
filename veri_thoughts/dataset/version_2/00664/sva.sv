module magnitude_comparator_sva (
    input logic clk,          // sampling clock for assertions (DUT is combinational)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT
);
    // EQ must equal (A == B).
    check_eq_definition: assert property (
        @(posedge clk) (EQ === (A == B))
    );

    // GT must equal (A > B).
    check_gt_definition: assert property (
        @(posedge clk) (GT === (A > B))
    );

    // EQ and GT cannot both be HIGH.
    check_eq_gt_mutex: assert property (
        @(posedge clk) !(EQ && GT)
    );

    // If inputs are equal, then EQ=1 and GT=0.
    check_outputs_when_equal: assert property (
        @(posedge clk) (A == B) |-> (EQ && !GT)
    );

    // If A is greater than B, then GT=1 and EQ=0.
    check_outputs_when_greater: assert property (
        @(posedge clk) (A > B) |-> (GT && !EQ)
    );

    // If A is less than B, then both EQ and GT are 0.
    check_outputs_when_less: assert property (
        @(posedge clk) (A < B) |-> (!EQ && !GT)
    );

    // EQ high implies inputs are equal.
    check_eq_implies_inputs_equal: assert property (
        @(posedge clk) EQ |-> (A == B)
    );

    // GT high implies A is greater than B.
    check_gt_implies_inputs_ordered: assert property (
        @(posedge clk) GT |-> (A > B)
    );

    // EQ high implies GT low.
    check_eq_implies_not_gt: assert property (
        @(posedge clk) EQ |-> !GT
    );

    // GT high implies EQ low.
    check_gt_implies_not_eq: assert property (
        @(posedge clk) GT |-> !EQ
    );
endmodule