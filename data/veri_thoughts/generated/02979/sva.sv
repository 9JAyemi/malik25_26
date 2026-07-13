module sky130_fd_sc_hd__o211ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches NAND of (B1 & C1 & (A1 | A2)) on any input edge.
    check_func_nand_equiv: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1)
        disable iff (1'b0)
        1'b1 |-> ##0 (Y == ~(B1 & C1 & (A1 | A2)))
    );

    // Y equals (~B1) | (~C1) | ((~A1) & (~A2)) on any input edge (De Morgan form).
    check_func_demorgan_equiv: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1)
        disable iff (1'b0)
        1'b1 |-> ##0 (Y == ((~B1) | (~C1) | ((~A1) & (~A2))))
    );

    // If B1 is LOW then Y must be HIGH.
    check_y_high_when_B1_low: assert property (
        @(posedge B1 or negedge B1 or
          posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge C1 or negedge C1)
        disable iff (1'b0)
        (!B1) |-> ##0 (Y == 1'b1)
    );

    // If C1 is LOW then Y must be HIGH.
    check_y_high_when_C1_low: assert property (
        @(posedge C1 or negedge C1 or
          posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1)
        disable iff (1'b0)
        (!C1) |-> ##0 (Y == 1'b1)
    );

    // If both A1 and A2 are LOW then Y must be HIGH.
    check_y_high_when_both_A_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1)
        disable iff (1'b0)
        ((!A1) && (!A2)) |-> ##0 (Y == 1'b1)
    );

    // If B1 and C1 are HIGH and A1 is HIGH then Y must be LOW.
    check_y_low_when_A1_high_with_B1C1_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1 or
          posedge A2 or negedge A2)
        disable iff (1'b0)
        (B1 && C1 && A1) |-> ##0 (Y == 1'b0)
    );

    // If B1 and C1 are HIGH and A2 is HIGH then Y must be LOW.
    check_y_low_when_A2_high_with_B1C1_high: assert property (
        @(posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1 or
          posedge A1 or negedge A1)
        disable iff (1'b0)
        (B1 && C1 && A2) |-> ##0 (Y == 1'b0)
    );

    // If B1 and C1 are HIGH and both A1 and A2 are LOW then Y must be HIGH.
    check_y_high_when_B1C1_high_and_both_A_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1)
        disable iff (1'b0)
        (B1 && C1 && (!A1) && (!A2)) |-> ##0 (Y == 1'b1)
    );

    // A falling edge on Y implies B1 & C1 & (A1 | A2) is true.
    check_y_fall_condition: assert property (
        @(posedge Y or negedge Y or
          posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1)
        disable iff (1'b0)
        $fell(Y) |-> ##0 (B1 && C1 && (A1 || A2))
    );

    // A rising edge on Y implies at least one blocking term is true (~B1 or ~C1 or ~A1&~A2).
    check_y_rise_condition: assert property (
        @(posedge Y or negedge Y or
          posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1)
        disable iff (1'b0)
        $rose(Y) |-> ##0 ((~B1) || (~C1) || ((~A1) && (~A2)))
    );

endmodule