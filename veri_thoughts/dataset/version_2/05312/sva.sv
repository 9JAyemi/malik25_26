module and4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // Y equals the AND of all four inputs.
    check_y_matches_and4: assert property (
        @(posedge clk) Y == (A & B & C & D)
    );

    // Y is high when all inputs are high.
    check_all_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A && B && C && D) |-> (Y == 1'b1)
    );

    // Y can only be high when all inputs are high.
    check_y_high_requires_all_inputs_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (A && B && C && D)
    );

    // Y is low when A is low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b0)
    );

    // Y is low when B is low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b0)
    );

    // Y is low when C is low.
    check_c_low_forces_y_low: assert property (
        @(posedge clk) (C == 1'b0) |-> (Y == 1'b0)
    );

    // Y is low when D is low.
    check_d_low_forces_y_low: assert property (
        @(posedge clk) (D == 1'b0) |-> (Y == 1'b0)
    );

endmodule