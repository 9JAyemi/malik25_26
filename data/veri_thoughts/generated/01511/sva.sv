module and4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // Output equals the AND of all four inputs.
    check_y_is_and4: assert property (
        @(posedge clk) Y == (A & B & C & D)
    );

    // Y can be 1 only if all inputs are 1.
    check_y_high_requires_all_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1))
    );

    // A low forces Y low.
    check_a_zero_forces_y_zero: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b0)
    );

    // B low forces Y low.
    check_b_zero_forces_y_zero: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b0)
    );

    // C low forces Y low.
    check_c_zero_forces_y_zero: assert property (
        @(posedge clk) (C == 1'b0) |-> (Y == 1'b0)
    );

    // D low forces Y low.
    check_d_zero_forces_y_zero: assert property (
        @(posedge clk) (D == 1'b0) |-> (Y == 1'b0)
    );

    // All inputs high forces Y high.
    check_all_high_forces_y_high: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1)) |-> (Y == 1'b1)
    );

    // If inputs are stable, output is stable.
    check_stable_inputs_stable_y: assert property (
        @(posedge clk) $stable({A,B,C,D}) |-> $stable(Y)
    );
endmodule