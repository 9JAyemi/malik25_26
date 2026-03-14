module sky130_fd_sc_lp__a41oi_sva (
    input logic clk,   // property clock (no clock/reset in DUT)
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);
    // Y equals ~(B1 | (A1 & A2 & A3 & A4)).
    check_y_functional: assert property (
        @(posedge clk) Y == ~(B1 | (A1 & A2 & A3 & A4))
    );

    // If B1 is HIGH, Y must be LOW.
    check_y_low_when_B1_high: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // If all A inputs are HIGH, Y must be LOW.
    check_y_low_when_all_A_high: assert property (
        @(posedge clk) (A1 & A2 & A3 & A4) |-> !Y
    );

    // If B1 is LOW and not all A are HIGH, Y must be HIGH.
    check_y_high_when_B1_low_and_not_all_A: assert property (
        @(posedge clk) (!B1 && !(A1 & A2 & A3 & A4)) |-> Y
    );

    // Y HIGH implies B1 is LOW and not all A are HIGH.
    check_y_implies_inputs_condition: assert property (
        @(posedge clk) Y |-> (!B1 && !(A1 & A2 & A3 & A4))
    );

    // Rising B1 forces Y LOW in the same cycle.
    check_y_low_on_rose_B1: assert property (
        @(posedge clk) $rose(B1) |-> !Y
    );

    // When A1&A2&A3&A4 rises to 1, Y must be LOW in the same cycle.
    check_y_low_on_rose_all_A_and: assert property (
        @(posedge clk) $rose(A1 & A2 & A3 & A4) |-> !Y
    );

    // If all inputs are stable, Y must remain stable (pure combinational).
    check_y_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A1,A2,A3,A4,B1}) |-> $stable(Y)
    );
endmodule