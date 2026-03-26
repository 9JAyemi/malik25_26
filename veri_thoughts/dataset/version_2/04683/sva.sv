module light_ctrl_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // X matches the implemented gate-level expression.
    check_x_matches_gate_expression: assert property (
        @(posedge clk)
        X == ((A1 | A2) & (A2 | A3) & (A1 | A3) & B1)
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk)
        !B1 |-> !X
    );

    // X high requires B1 high.
    check_x_requires_b1_high: assert property (
        @(posedge clk)
        X |-> B1
    );

    // A1 and A2 high with B1 high drive X high.
    check_a1_a2_pair_drives_x: assert property (
        @(posedge clk)
        (B1 && A1 && A2) |-> X
    );

    // A1 and A3 high with B1 high drive X high.
    check_a1_a3_pair_drives_x: assert property (
        @(posedge clk)
        (B1 && A1 && A3) |-> X
    );

    // A2 and A3 high with B1 high drive X high.
    check_a2_a3_pair_drives_x: assert property (
        @(posedge clk)
        (B1 && A2 && A3) |-> X
    );

    // Fewer than two asserted A inputs keep X low when B1 is high.
    check_insufficient_a_inputs_keep_x_low: assert property (
        @(posedge clk)
        (B1 && !((A1 & A2) | (A1 & A3) | (A2 & A3))) |-> !X
    );

    // X high requires at least one asserted pair of A inputs.
    check_x_requires_two_a_inputs: assert property (
        @(posedge clk)
        X |-> ((A1 & A2) | (A1 & A3) | (A2 & A3))
    );

endmodule