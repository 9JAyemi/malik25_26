module top_module_sva (
    input logic clk,
    input logic reset,      // Synchronous active-high reset
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ1,
    input logic GT1,
    input logic LT1,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic EQ2,
    input logic GT2,
    input logic LT2,
    input logic [3:0] q
);
    ///// Comparator 1 behavior /////
    // EQ1 reflects A == B.
    check_comp1_eq_definition: assert property (
        @(posedge clk) disable iff (reset) (EQ1 === (A == B))
    );
    // GT1 reflects A > B.
    check_comp1_gt_definition: assert property (
        @(posedge clk) disable iff (reset) (GT1 === (A > B))
    );
    // LT1 reflects A < B.
    check_comp1_lt_definition: assert property (
        @(posedge clk) disable iff (reset) (LT1 === (A < B))
    );
    // GT1 and LT1 cannot be 1 at the same time.
    check_comp1_gt_lt_mutex: assert property (
        @(posedge clk) disable iff (reset) !(GT1 && LT1)
    );
    // If EQ1 is 1 then GT1 and LT1 must be 0.
    check_comp1_eq_excludes_gt_lt: assert property (
        @(posedge clk) disable iff (reset) EQ1 |-> (!GT1 && !LT1)
    );

    ///// Comparator 2 behavior /////
    // EQ2 reflects C == D.
    check_comp2_eq_definition: assert property (
        @(posedge clk) disable iff (reset) (EQ2 === (C == D))
    );
    // GT2 reflects C > D.
    check_comp2_gt_definition: assert property (
        @(posedge clk) disable iff (reset) (GT2 === (C > D))
    );
    // LT2 reflects C < D.
    check_comp2_lt_definition: assert property (
        @(posedge clk) disable iff (reset) (LT2 === (C < D))
    );
    // GT2 and LT2 cannot be 1 at the same time.
    check_comp2_gt_lt_mutex: assert property (
        @(posedge clk) disable iff (reset) !(GT2 && LT2)
    );
    // If EQ2 is 1 then GT2 and LT2 must be 0.
    check_comp2_eq_excludes_gt_lt: assert property (
        @(posedge clk) disable iff (reset) EQ2 |-> (!GT2 && !LT2)
    );

    ///// Output q behavior /////
    // q equals the RTL expression using comparator outputs.
    check_q_matches_rtl_expression: assert property (
        @(posedge clk) disable iff (reset)
        q === (
            (GT2 || EQ2)
                ? ((C > ((GT1 || EQ1) ? A : B)) ? C : ((GT1 || EQ1) ? A : B))
                : ((D > ((GT1 || EQ1) ? A : B)) ? D : ((GT1 || EQ1) ? A : B))
        )
    );
    // When A >= B, q is at least A.
    check_q_ge_a_when_ageb: assert property (
        @(posedge clk) disable iff (reset) (GT1 || EQ1) |-> (q >= A)
    );
    // When B > A, q is at least B.
    check_q_ge_b_when_bgeta_is_false: assert property (
        @(posedge clk) disable iff (reset) (! (GT1 || EQ1)) |-> (q >= B)
    );
    // When C >= D, q is at least C.
    check_q_ge_c_when_cged: assert property (
        @(posedge clk) disable iff (reset) (GT2 || EQ2) |-> (q >= C)
    );
    // When D > C, q is at least D.
    check_q_ge_d_when_dgtc: assert property (
        @(posedge clk) disable iff (reset) (! (GT2 || EQ2)) |-> (q >= D)
    );
endmodule