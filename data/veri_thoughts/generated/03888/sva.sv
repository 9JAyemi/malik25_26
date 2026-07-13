module sky130_fd_sc_hdll__o22ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Exact combinational function of the cell.
    check_output_equation: assert property (
        @(posedge clk) (Y == ((~(A1 | A2)) | (~(B1 | B2))))
    );

    // If both A inputs are low, Y must be high.
    check_output_high_when_a_pair_low: assert property (
        @(posedge clk) ((!A1 && !A2) |-> (Y == 1'b1))
    );

    // If both B inputs are low, Y must be high.
    check_output_high_when_b_pair_low: assert property (
        @(posedge clk) ((!B1 && !B2) |-> (Y == 1'b1))
    );

    // If both input groups have at least one high, Y must be low.
    check_output_low_when_both_groups_active: assert property (
        @(posedge clk) (((A1 || A2) && (B1 || B2)) |-> (Y == 1'b0))
    );

    // A high Y means at least one input pair is all low.
    check_high_output_implies_zero_pair: assert property (
        @(posedge clk) ((Y == 1'b1) |-> ((!A1 && !A2) || (!B1 && !B2)))
    );

    // A low Y means both input groups are active.
    check_low_output_implies_both_groups_active: assert property (
        @(posedge clk) ((Y == 1'b0) |-> ((A1 || A2) && (B1 || B2)))
    );

    // All-zero inputs drive Y high.
    check_all_inputs_low_drive_high: assert property (
        @(posedge clk) ((!A1 && !A2 && !B1 && !B2) |-> (Y == 1'b1))
    );

    // All-one inputs drive Y low.
    check_all_inputs_high_drive_low: assert property (
        @(posedge clk) ((A1 && A2 && B1 && B2) |-> (Y == 1'b0))
    );

endmodule