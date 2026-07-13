module compm4_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B0,
    input logic B1,
    input logic B2,
    input logic B3,
    input logic GT,
    input logic LT
);
    // GT matches unsigned compare A>B
    check_gt_definition: assert property (
        @(posedge clk) GT == ({A3,A2,A1,A0} > {B3,B2,B1,B0})
    );

    // LT matches unsigned compare A<B
    check_lt_definition: assert property (
        @(posedge clk) LT == ({A3,A2,A1,A0} < {B3,B2,B1,B0})
    );

    // GT and LT are never both 1
    check_mutual_exclusion: assert property (
        @(posedge clk) !(GT && LT)
    );

    // When A==B, both outputs are 0
    check_equal_outputs_zero: assert property (
        @(posedge clk) ({A3,A2,A1,A0} == {B3,B2,B1,B0}) |=> (GT == 1'b0 && LT == 1'b0)
    );

    // When A!=B, exactly one of GT or LT is 1
    check_inequal_outputs_xor: assert property (
        @(posedge clk) ({A3,A2,A1,A0} != {B3,B2,B1,B0}) |=> (GT ^ LT)
    );

    // If GT is 1 then LT is 0
    check_gt_implies_not_lt: assert property (
        @(posedge clk) GT |=> (LT == 1'b0)
    );

    // If LT is 1 then GT is 0
    check_lt_implies_not_gt: assert property (
        @(posedge clk) LT |=> (GT == 1'b0)
    );

    // When A>B, GT=1 and LT=0
    check_outputs_when_A_gt_B: assert property (
        @(posedge clk) ({A3,A2,A1,A0} > {B3,B2,B1,B0}) |=> (GT == 1'b1 && LT == 1'b0)
    );

    // When A<B, LT=1 and GT=0
    check_outputs_when_A_lt_B: assert property (
        @(posedge clk) ({A3,A2,A1,A0} < {B3,B2,B1,B0}) |=> (LT == 1'b1 && GT == 1'b0)
    );
endmodule