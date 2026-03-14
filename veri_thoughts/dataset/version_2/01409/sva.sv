module sky130_fd_sc_lp__a221o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Analysis: no clock/reset; pure combinational; X = (A1&A2) | (B1&B2) | C1

    // Boolean function: X equals (A1&A2) OR (B1&B2) OR C1.
    check_function_equation: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        X == ((A1 & A2) | (B1 & B2) | C1)
    );

    // If C1 is HIGH, X must be HIGH.
    check_c1_forces_x_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        C1 |-> X
    );

    // If A1&A2 are HIGH, X must be HIGH.
    check_a_pair_forces_x_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (A1 & A2) |-> X
    );

    // If B1&B2 are HIGH, X must be HIGH.
    check_b_pair_forces_x_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (B1 & B2) |-> X
    );

    // If X is LOW, all three OR terms must be LOW.
    check_x_low_implies_terms_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        !X |-> (!C1 && !(A1 & A2) && !(B1 & B2))
    );

    // All inputs LOW imply X is LOW.
    check_all_zero_inputs_yield_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (!A1 && !A2 && !B1 && !B2 && !C1) |-> (!X)
    );

    // With C1 LOW, X reduces to (A1&A2)|(B1&B2).
    check_reduction_when_c1_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (!C1) |-> (X == ((A1 & A2) | (B1 & B2)))
    );

    // With A1 LOW, X reduces to (B1&B2)|C1.
    check_reduction_when_a1_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (!A1) |-> (X == ((B1 & B2) | C1))
    );

    // With A2 LOW, X reduces to (B1&B2)|C1.
    check_reduction_when_a2_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (!A2) |-> (X == ((B1 & B2) | C1))
    );

    // With B1 LOW, X reduces to (A1&A2)|C1.
    check_reduction_when_b1_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (!B1) |-> (X == ((A1 & A2) | C1))
    );

endmodule