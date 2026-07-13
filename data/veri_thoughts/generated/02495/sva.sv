module my_nand_gate_sva (
    input logic CLK,   // sampling clock for assertions (DUT has no clock/reset)
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND
);
    // Y implements a 4-input NAND of A,B,C,D.
    check_y_is_nand4: assert property (
        @(posedge CLK) Y == ~(A & B & C & D)
    );

    // When all inputs are HIGH, Y must be LOW.
    check_all_high_implies_y0: assert property (
        @(posedge CLK) (A & B & C & D) |-> (Y == 1'b0)
    );

    // When not all inputs are HIGH, Y must be HIGH.
    check_not_all_high_implies_y1: assert property (
        @(posedge CLK) !(A & B & C & D) |-> (Y == 1'b1)
    );

    // If Y is LOW, then all inputs are HIGH.
    check_y0_implies_all_high: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (A & B & C & D)
    );

    // If Y is HIGH, then not all inputs are HIGH.
    check_y1_implies_not_all_high: assert property (
        @(posedge CLK) (Y == 1'b1) |-> !(A & B & C & D)
    );

    // A falling Y implies inputs are all HIGH now.
    check_y_fall_means_all_high: assert property (
        @(posedge CLK) $fell(Y) |-> (A & B & C & D)
    );

    // A rising Y implies not all inputs are HIGH now.
    check_y_rise_means_not_all_high: assert property (
        @(posedge CLK) $rose(Y) |-> !(A & B & C & D)
    );

    // When inputs collectively rise to all HIGH, Y is LOW.
    check_all_high_rose_implies_y0: assert property (
        @(posedge CLK) $rose(A & B & C & D) |-> (Y == 1'b0)
    );

    // When inputs collectively fall from all HIGH, Y is HIGH.
    check_all_high_fell_implies_y1: assert property (
        @(posedge CLK) $fell(A & B & C & D) |-> (Y == 1'b1)
    );

    // Y changes iff the all-high condition changes (Y = ~all_high).
    check_y_change_matches_all_high: assert property (
        @(posedge CLK) ($changed(Y) == $changed(A & B & C & D))
    );
endmodule