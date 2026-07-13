module xor_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic X,
    input logic VPWR,
    input logic VGND
);

    // X must always equal A XOR B.
    check_x_matches_xor: assert property (
        @(posedge clk) X == (A ^ B)
    );

    // X must be low when both inputs are low.
    check_both_low_output_low: assert property (
        @(posedge clk) (!A && !B) |-> !X
    );

    // X must be high when only B is high.
    check_only_b_high_output_high: assert property (
        @(posedge clk) (!A && B) |-> X
    );

    // X must be high when only A is high.
    check_only_a_high_output_high: assert property (
        @(posedge clk) (A && !B) |-> X
    );

    // X must be low when both inputs are high.
    check_both_high_output_low: assert property (
        @(posedge clk) (A && B) |-> !X
    );

    // X must change when A changes and B stays the same.
    check_a_toggle_flips_output: assert property (
        @(posedge clk) ($changed(A) && $stable(B)) |-> $changed(X)
    );

    // X must change when B changes and A stays the same.
    check_b_toggle_flips_output: assert property (
        @(posedge clk) ($stable(A) && $changed(B)) |-> $changed(X)
    );

    // X must stay the same when both inputs stay the same.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(X)
    );

    // X must stay the same when both inputs toggle together.
    check_dual_toggle_holds_output: assert property (
        @(posedge clk) ($changed(A) && $changed(B)) |-> $stable(X)
    );

endmodule