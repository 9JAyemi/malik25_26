module my_module_assertions (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Combinational DUT sampled on an external clock; no reset in RTL.

    // Y must match the buffered NAND of the two OR terms and C1.
    check_output_function: assert property (
        @(posedge clk)
        Y === ~(((A2 | A1) & (B2 | B1) & C1))
    );

    // Y must go low when both OR terms are high and C1 is high.
    check_output_low_when_all_terms_true: assert property (
        @(posedge clk)
        (((A2 | A1) == 1'b1) && ((B2 | B1) == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );

    // A low Y implies both OR terms are high and C1 is high.
    check_output_low_only_for_active_inputs: assert property (
        @(posedge clk)
        (Y == 1'b0) |-> (((A2 | A1) == 1'b1) && ((B2 | B1) == 1'b1) && (C1 == 1'b1))
    );

    // C1 low forces the NAND output high.
    check_c1_low_forces_output_high: assert property (
        @(posedge clk)
        (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A inputs low force the NAND output high.
    check_a_group_low_forces_output_high: assert property (
        @(posedge clk)
        ((A2 == 1'b0) && (A1 == 1'b0)) |-> (Y == 1'b1)
    );

    // Both B inputs low force the NAND output high.
    check_b_group_low_forces_output_high: assert property (
        @(posedge clk)
        ((B2 == 1'b0) && (B1 == 1'b0)) |-> (Y == 1'b1)
    );

    // Stable inputs must keep the output stable across cycles.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk)
        $stable({A1, A2, B1, B2, C1}) |-> $stable(Y)
    );

endmodule