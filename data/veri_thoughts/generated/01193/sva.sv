module sky130_fd_sc_lp__a41oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);
    // Combinational cell: Y = ~(B1 | (A1&A2&A3&A4)); no clock/reset present.

    // Y matches NOR of B1 and the 4-input AND.
    check_function_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        Y == ~(B1 | (A1 & A2 & A3 & A4))
    );

    // If B1 is HIGH, Y must be LOW (same cycle).
    check_B1_high_forces_Y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        (B1 == 1'b1) |=> (Y == 1'b0)
    );

    // If all A inputs are HIGH, Y must be LOW (same cycle).
    check_allA_high_forces_Y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        ((A1 & A2 & A3 & A4) == 1'b1) |=> (Y == 1'b0)
    );

    // If B1 is LOW and not all A are HIGH, Y must be HIGH (same cycle).
    check_B1_low_and_notAllA_drives_Y_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        ((B1 == 1'b0) && !(A1 & A2 & A3 & A4)) |=> (Y == 1'b1)
    );

    // Y HIGH implies B1 is LOW and not all A are HIGH (same cycle).
    check_Y_high_implies_inputs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        (Y == 1'b1) |=> ((B1 == 1'b0) && !(A1 & A2 & A3 & A4))
    );

    // Y LOW implies B1 is HIGH or all A are HIGH (same cycle).
    check_Y_low_implies_inputs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        (Y == 1'b0) |=> ((B1 == 1'b1) || (A1 & A2 & A3 & A4))
    );

    // If inputs are stable between samples, Y must also be stable.
    check_stability: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        $stable({A1, A2, A3, A4, B1}) |=> $stable(Y)
    );

    // On B1 rising edge, Y must be LOW (same cycle).
    check_Y_on_B1_rise: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        $rose(B1) |=> (Y == 1'b0)
    );

    // On B1 falling edge, Y must equal ~(A1&A2&A3&A4) (same cycle).
    check_Y_on_B1_fall: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        $fell(B1) |=> (Y == ~(A1 & A2 & A3 & A4))
    );

    // When all A rise to 1, Y must be LOW (same cycle).
    check_Y_on_allA_rise: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge A4 or negedge A4 or posedge B1 or negedge B1)
        $rose(A1 & A2 & A3 & A4) |=> (Y == 1'b0)
    );
endmodule