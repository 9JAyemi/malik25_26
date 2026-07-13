module comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic EQ,
    input logic GT
);
    // EQ must equal (A==B) && (B==C) && (C==D).
    check_eq_definition: assert property (
        @(posedge A[0]) EQ == ((A == B) && (B == C) && (C == D))
    );

    // GT must equal (A>B) || ((A==B) && (C>D)).
    check_gt_definition: assert property (
        @(posedge A[0]) GT == ((A > B) || ((A == B) && (C > D)))
    );

    // If A>B then GT must be 1.
    check_gt_when_a_gt_b: assert property (
        @(posedge A[0]) (A > B) |-> (GT == 1'b1)
    );

    // If A==B and C>D then GT must be 1.
    check_gt_when_a_eq_b_and_c_gt_d: assert property (
        @(posedge A[0]) ((A == B) && (C > D)) |-> (GT == 1'b1)
    );

    // If A<B and C<=D then GT must be 0.
    check_gt_zero_when_a_lt_b_and_c_le_d: assert property (
        @(posedge A[0]) ((A < B) && (C <= D)) |-> (GT == 1'b0)
    );

    // If A==B and C==D then GT must equal (A>B).
    check_gt_when_a_eq_b_and_c_eq_d: assert property (
        @(posedge A[0]) ((A == B) && (C == D)) |-> (GT == (A > B))
    );

    // If A==B and C==D and A>B then GT must be 1.
    check_gt_when_all_equal_and_a_gt_b: assert property (
        @(posedge A[0]) ((A == B) && (C == D) && (A > B)) |-> (GT == 1'b1)
    );

    // If A==B and C==D and A<B then GT must be 0.
    check_gt_when_all_equal_and_a_lt_b: assert property (
        @(posedge A[0]) ((A == B) && (C == D) && (A < B)) |-> (GT == 1'b0)
    );

    // If A==B and C==D and A==B then GT must be 0.
    check_gt_when_all_equal_and_a_eq_b: assert property (
        @(posedge A[0]) ((A == B) && (C == D) && (A == B)) |-> (GT == 1'b0)
    );

    // If A>B then EQ must be 0.
    check_eq_zero_when_a_gt_b: assert property (
        @(posedge A[0]) (A > B) |-> (EQ == 1'b0)
    );

    // If A<B then EQ must be 0.
    check_eq_zero_when_a_lt_b: assert property (
        @(posedge A[0]) (A < B) |-> (EQ == 1'b0)
    );

    // If A==B and B==C and C==D then EQ must be 1.
    check_eq_when_all_equal: assert property (
        @(posedge A[0]) ((A == B) && (B == C) && (C == D)) |-> (EQ == 1'b1)
    );

    // If A!=B then EQ must be 0.
    check_eq_zero_when_a_ne_b: assert property (
        @(posedge A[0]) (A != B) |-> (EQ == 1'b0)
    );

    // If A==B and C!=D then EQ must be 0.
    check_eq_zero_when_a_eq_b_c_ne_d: assert property (
        @(posedge A[0]) ((A == B) && (C != D)) |-> (EQ == 1'b0)
    );

    // If A==B and C==D and A!=B then EQ must be 0.
    check_eq_zero_when_all_equal_but_a_ne_b: assert property (
        @(posedge A[0]) ((A == B) && (C == D) && (A != B)) |-> (EQ == 1'b0)
    );

    // If A==B and C==D and A==B then EQ must be 1.
    check_eq_one_when_all_equal_and_a_eq_b: assert property (
        @(posedge A[0]) ((A == B) && (C == D) && (A == B)) |-> (EQ == 1'b1)
    );
endmodule