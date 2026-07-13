module nor_and_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y matches the implemented NOR-of-NORs function.
    check_y_matches_nor_of_nors: assert property (
        @(posedge clk) Y == ~((~(A | B)) & (~(C | D)))
    );

    // If both input pairs are low, Y must be high.
    check_y_high_when_both_pairs_low: assert property (
        @(posedge clk) ((A | B) == 1'b0 && (C | D) == 1'b0) |-> (Y == 1'b1)
    );

    // If A and B are high, Y must be low.
    check_y_low_when_ab_high: assert property (
        @(posedge clk) (A & B) |-> (Y == 1'b0)
    );

    // If C and D are high, Y must be low.
    check_y_low_when_cd_high: assert property (
        @(posedge clk) (C & D) |-> (Y == 1'b0)
    );

    // If either input pair is high, Y must be low.
    check_y_low_when_any_pair_high: assert property (
        @(posedge clk) ((A | B) == 1'b1 || (C | D) == 1'b1) |-> (Y == 1'b0)
    );

    // A high Y means at least one input pair is low.
    check_y_high_implies_some_pair_low: assert property (
        @(posedge clk) (Y == 1'b1) |-> (((A | B) == 1'b0) || ((C | D) == 1'b0))
    );

    // A low Y means both input pairs are high.
    check_y_low_implies_both_pairs_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A | B) == 1'b1 && (C | D) == 1'b1)
    );

endmodule