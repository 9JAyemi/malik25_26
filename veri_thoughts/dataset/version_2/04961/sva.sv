module sky130_fd_sc_ls__o2bb2ai_sva (
    input logic clk,
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // Y matches the implemented O2BB2AI boolean function.
    check_y_matches_logic: assert property (
        @(posedge clk) Y == ((A1_N & A2_N) | (~B1 & ~B2))
    );

    // Y is high whenever both B inputs are low.
    check_y_high_when_b_inputs_low: assert property (
        @(posedge clk) (~B1 & ~B2) |-> Y
    );

    // Y is high whenever both A inputs are high.
    check_y_high_when_a_inputs_high: assert property (
        @(posedge clk) (A1_N & A2_N) |-> Y
    );

    // Y is low when any B input is high and at least one A input is low.
    check_y_low_when_b_active_and_a_not_both_high: assert property (
        @(posedge clk) ((B1 | B2) & (~A1_N | ~A2_N)) |-> ~Y
    );

    // A low Y requires at least one B input to be high.
    check_y_low_requires_b_activity: assert property (
        @(posedge clk) (~Y) |-> (B1 | B2)
    );

    // A low Y requires at least one A input to be low.
    check_y_low_requires_one_a_low: assert property (
        @(posedge clk) (~Y) |-> (~A1_N | ~A2_N)
    );

endmodule