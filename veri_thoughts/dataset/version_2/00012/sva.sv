module sky130_fd_sc_hd__o22ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y matches the implemented O22AI boolean function.
    check_output_matches_o22ai_function: assert property (
        @(posedge clk) (Y == (((!A1) && (!A2)) || ((!B1) && (!B2))))
    );

    // If both A inputs are low, Y must be high.
    check_a_inputs_low_force_high: assert property (
        @(posedge clk) ((!A1 && !A2) |-> (Y == 1'b1))
    );

    // If both B inputs are low, Y must be high.
    check_b_inputs_low_force_high: assert property (
        @(posedge clk) ((!B1 && !B2) |-> (Y == 1'b1))
    );

    // If either A input and either B input are high, Y must be low.
    check_active_a_and_b_force_low: assert property (
        @(posedge clk) (((A1 || A2) && (B1 || B2)) |-> (Y == 1'b0))
    );

    // A high Y means at least one input pair is all low.
    check_high_output_means_one_pair_low: assert property (
        @(posedge clk) ((Y == 1'b1) |-> ((!A1 && !A2) || (!B1 && !B2)))
    );

    // A low Y means both input pairs have an asserted member.
    check_low_output_means_both_pairs_active: assert property (
        @(posedge clk) ((Y == 1'b0) |-> ((A1 || A2) && (B1 || B2)))
    );

endmodule