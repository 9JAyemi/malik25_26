module sky130_fd_sc_lp__o22ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // No clock or reset exist in the RTL; sample this combinational cell on clk.

    // Y matches the implemented O22AI boolean equation.
    check_o22ai_equation: assert property (
        @(posedge clk) Y == ((~(A1 | A2)) | (~(B1 | B2)))
    );

    // Y is low when both input groups have at least one asserted input.
    check_y_low_when_both_groups_active: assert property (
        @(posedge clk) ((A1 | A2) & (B1 | B2)) |-> (Y == 1'b0)
    );

    // Y is high when the A-input group is fully deasserted.
    check_y_high_when_a_group_low: assert property (
        @(posedge clk) (~(A1 | A2)) |-> (Y == 1'b1)
    );

    // Y is high when the B-input group is fully deasserted.
    check_y_high_when_b_group_low: assert property (
        @(posedge clk) (~(B1 | B2)) |-> (Y == 1'b1)
    );

    // A low output implies both input groups are active.
    check_low_output_implies_both_groups_active: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A1 | A2) & (B1 | B2))
    );

    // A high output implies at least one input group is fully low.
    check_high_output_implies_one_group_low: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((~(A1 | A2)) | (~(B1 | B2)))
    );

endmodule