module sky130_fd_sc_ls__a21boi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // No RTL reset is present; sample this combinational logic on clk.

    // Y matches the implemented not/and/nor function.
    check_y_matches_logic: assert property (
        @(posedge clk) Y == ~(~B1_N | (A1 & A2))
    );

    // Low B1_N forces Y low.
    check_b1n_low_forces_y_low: assert property (
        @(posedge clk) !B1_N |-> (Y == 1'b0)
    );

    // High A1 and A2 force Y low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> (Y == 1'b0)
    );

    // With B1_N high and A1 low, Y must be high.
    check_b1n_high_a1_low_gives_y_high: assert property (
        @(posedge clk) (B1_N && !A1) |-> (Y == 1'b1)
    );

    // With B1_N high and A2 low, Y must be high.
    check_b1n_high_a2_low_gives_y_high: assert property (
        @(posedge clk) (B1_N && !A2) |-> (Y == 1'b1)
    );

    // High Y requires B1_N to be high.
    check_y_high_requires_b1n_high: assert property (
        @(posedge clk) Y |-> B1_N
    );

    // High Y requires the A1/A2 AND term to be low.
    check_y_high_requires_and_term_low: assert property (
        @(posedge clk) Y |-> !(A1 && A2)
    );

    // With B1_N high, low Y implies both A inputs are high.
    check_b1n_high_y_low_requires_a1_a2_high: assert property (
        @(posedge clk) (B1_N && !Y) |-> (A1 && A2)
    );

endmodule