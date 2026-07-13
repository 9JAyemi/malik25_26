module logic_operations_sva (
    input logic CLK,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    ///// Functional correctness /////
    // SUM must equal XOR of A, B, CI.
    check_sum_xor3: assert property (
        @(posedge CLK) SUM === (A ^ B ^ CI)
    );

    // COUT must equal majority of A, B, CI.
    check_cout_majority: assert property (
        @(posedge CLK) COUT === ((A & B) | (A & CI) | (B & CI))
    );

    ///// Truth-table spot checks /////
    // When A=B=CI=0, SUM=0 and COUT=0.
    check_tt_all_zero: assert property (
        @(posedge CLK) (A==1'b0 && B==1'b0 && CI==1'b0) |-> (SUM==1'b0 && COUT==1'b0)
    );

    // When A=B=CI=1, SUM=1 and COUT=1.
    check_tt_all_one: assert property (
        @(posedge CLK) (A==1'b1 && B==1'b1 && CI==1'b1) |-> (SUM==1'b1 && COUT==1'b1)
    );

    // When only A=1, SUM=1 and COUT=0.
    check_tt_only_a: assert property (
        @(posedge CLK) (A==1'b1 && B==1'b0 && CI==1'b0) |-> (SUM==1'b1 && COUT==1'b0)
    );

    // When only B=1, SUM=1 and COUT=0.
    check_tt_only_b: assert property (
        @(posedge CLK) (A==1'b0 && B==1'b1 && CI==1'b0) |-> (SUM==1'b1 && COUT==1'b0)
    );

    // When only CI=1, SUM=1 and COUT=0.
    check_tt_only_ci: assert property (
        @(posedge CLK) (A==1'b0 && B==1'b0 && CI==1'b1) |-> (SUM==1'b1 && COUT==1'b0)
    );

    // When A=B=1 and CI=0, SUM=0 and COUT=1.
    check_tt_ab_two_ones: assert property (
        @(posedge CLK) (A==1'b1 && B==1'b1 && CI==1'b0) |-> (SUM==1'b0 && COUT==1'b1)
    );

    // When A=CI=1 and B=0, SUM=0 and COUT=1.
    check_tt_ac_two_ones: assert property (
        @(posedge CLK) (A==1'b1 && B==1'b0 && CI==1'b1) |-> (SUM==1'b0 && COUT==1'b1)
    );

    // When B=CI=1 and A=0, SUM=0 and COUT=1.
    check_tt_bc_two_ones: assert property (
        @(posedge CLK) (A==1'b0 && B==1'b1 && CI==1'b1) |-> (SUM==1'b0 && COUT==1'b1)
    );

    ///// Derived consistency /////
    // COUT high implies at least two inputs are high.
    check_cout_implies_two_high: assert property (
        @(posedge CLK) COUT |-> ((A & B) | (A & CI) | (B & CI))
    );

    // COUT low implies fewer than two inputs are high.
    check_cout_low_implies_lt2: assert property (
        @(posedge CLK) !COUT |-> ~((A & B) | (A & CI) | (B & CI))
    );

endmodule