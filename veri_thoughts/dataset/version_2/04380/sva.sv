module sky130_fd_sc_hdll__o32ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // External sampling clock; the DUT RTL is combinational and has no reset.

    // Y matches the OR of the two NOR terms.
    check_y_matches_or_of_nors: assert property (
        @(posedge clk) Y == ((~(A3 | A1 | A2)) | (~(B1 | B2)))
    );

    // If the A-group inputs are all low, Y must be high.
    check_a_group_all_low_forces_y_high: assert property (
        @(posedge clk) (!(A3 | A1 | A2)) |-> Y
    );

    // If the B-group inputs are all low, Y must be high.
    check_b_group_all_low_forces_y_high: assert property (
        @(posedge clk) (!(B1 | B2)) |-> Y
    );

    // If both input groups are active, Y must be low.
    check_both_groups_active_force_y_low: assert property (
        @(posedge clk) ((A3 | A1 | A2) && (B1 | B2)) |-> !Y
    );

    // A low Y requires at least one A-group input high.
    check_y_low_implies_a_group_active: assert property (
        @(posedge clk) (!Y) |-> (A3 | A1 | A2)
    );

    // A low Y requires at least one B-group input high.
    check_y_low_implies_b_group_active: assert property (
        @(posedge clk) (!Y) |-> (B1 | B2)
    );

    // If Y is high while the A-group is active, the B-group must be all low.
    check_y_high_with_a_group_active_implies_b_group_low: assert property (
        @(posedge clk) (Y && (A3 | A1 | A2)) |-> !(B1 | B2)
    );

    // If Y is high while the B-group is active, the A-group must be all low.
    check_y_high_with_b_group_active_implies_a_group_low: assert property (
        @(posedge clk) (Y && (B1 | B2)) |-> !(A3 | A1 | A2)
    );

endmodule