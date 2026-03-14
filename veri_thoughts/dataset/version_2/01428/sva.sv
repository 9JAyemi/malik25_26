module sky130_fd_sc_ls__o22ai_sva (
    input logic clk,     // SVA clock (RTL has no clock/reset)
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // Combinational cell: Y = ~((A1|A2) & (B1|B2))

    // Y must equal the o22ai Boolean function.
    check_function_equivalence: assert property (
        @(posedge clk) Y === ~((A1 | A2) & (B1 | B2))
    );

    // If both OR-groups are HIGH, Y must be LOW.
    check_y_low_when_both_groups_high: assert property (
        @(posedge clk) (((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1)) |-> (Y == 1'b0)
    );

    // If A-group OR is LOW, Y must be HIGH.
    check_y_high_when_agroup_low: assert property (
        @(posedge clk) ((A1 | A2) == 1'b0) |-> (Y == 1'b1)
    );

    // If B-group OR is LOW, Y must be HIGH.
    check_y_high_when_bgroup_low: assert property (
        @(posedge clk) ((B1 | B2) == 1'b0) |-> (Y == 1'b1)
    );

    // If A1 and B1 are HIGH, Y must be LOW.
    check_y_low_when_A1_B1_high: assert property (
        @(posedge clk) ((A1 == 1'b1) && (B1 == 1'b1)) |-> (Y == 1'b0)
    );

    // If A1 and B2 are HIGH, Y must be LOW.
    check_y_low_when_A1_B2_high: assert property (
        @(posedge clk) ((A1 == 1'b1) && (B2 == 1'b1)) |-> (Y == 1'b0)
    );

    // If A2 and B1 are HIGH, Y must be LOW.
    check_y_low_when_A2_B1_high: assert property (
        @(posedge clk) ((A2 == 1'b1) && (B1 == 1'b1)) |-> (Y == 1'b0)
    );

    // If A2 and B2 are HIGH, Y must be LOW.
    check_y_low_when_A2_B2_high: assert property (
        @(posedge clk) ((A2 == 1'b1) && (B2 == 1'b1)) |-> (Y == 1'b0)
    );

    // If all inputs are HIGH, Y must be LOW.
    check_y_low_when_all_ones: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1) && (B2 == 1'b1)) |-> (Y == 1'b0)
    );

    // If all inputs are LOW, Y must be HIGH.
    check_y_high_when_all_zeros: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );

    // If Y is LOW, both OR-groups must be HIGH.
    check_implication_y_low_groups_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1))
    );

    // If Y is HIGH, at least one OR-group must be LOW.
    check_implication_y_high_group_low: assert property (
        @(posedge clk) (Y == 1'b1) |-> (((A1 | A2) == 1'b0) || ((B1 | B2) == 1'b0))
    );
endmodule