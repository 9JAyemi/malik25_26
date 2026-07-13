module and_gate_extra_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must equal A & B & ~C.
    check_y_matches_function: assert property (
        @(posedge clk) Y == (A & B & ~C)
    );

    // C high must force Y low.
    check_c_high_forces_y_low: assert property (
        @(posedge clk) C |-> !Y
    );

    // A low must force Y low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !A |-> !Y
    );

    // B low must force Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

    // With C low and both inputs high, Y must be high.
    check_all_inputs_true_drive_y_high: assert property (
        @(posedge clk) (!C && A && B) |-> Y
    );

endmodule