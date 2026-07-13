module sky130_fd_sc_ls__o32ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // No clock/reset in RTL; purely combinational cell. Function: Y = ~((A1|A2|A3) & (B1|B2)).
    // Assertions are sampled on any input edge.

    // Output equals ~( (A1|A2|A3) & (B1|B2) ).
    check_function_equation: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        Y == ~((A1 | A2 | A3) & (B1 | B2))
    );

    // If both OR groups are HIGH, Y must be LOW.
    check_y_low_when_both_ors_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        ((A1 | A2 | A3) & (B1 | B2)) |-> (Y == 1'b0)
    );

    // If at least one OR group is LOW, Y must be HIGH.
    check_y_high_when_any_or_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        ((~(A1 | A2 | A3)) | (~(B1 | B2))) |-> (Y == 1'b1)
    );

    // If Y is LOW, both OR groups must be HIGH.
    check_y_low_implies_both_ors_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        (Y == 1'b0) |-> (((A1 | A2 | A3) & (B1 | B2)) == 1'b1)
    );

    // If Y is HIGH, at least one OR group must be LOW.
    check_y_high_implies_any_or_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        (Y == 1'b1) |-> (((A1 | A2 | A3) == 1'b0) || ((B1 | B2) == 1'b0))
    );

    // If all A inputs are LOW, Y must be HIGH.
    check_y_high_when_all_a_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (Y == 1'b1)
    );

    // If all B inputs are LOW, Y must be HIGH.
    check_y_high_when_all_b_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        ((B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );

    // If all A and B inputs are HIGH, Y must be LOW.
    check_y_low_when_all_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        ((A1 == 1'b1) && (A2 == 1'b1) && (A3 == 1'b1) && (B1 == 1'b1) && (B2 == 1'b1)) |-> (Y == 1'b0)
    );

endmodule