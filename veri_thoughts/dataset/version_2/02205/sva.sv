module sky130_fd_sc_lp__nor3_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);
    // Y equals NOR of A, B, C.
    check_func_nor3_output: assert property (
        @(posedge CLK) Y == ~(A | B | C)
    );

    // Y HIGH implies all inputs LOW.
    check_y_high_implies_all_low: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (!A && !B && !C)
    );

    // All inputs LOW implies Y HIGH.
    check_all_low_implies_y_high: assert property (
        @(posedge CLK) (!A && !B && !C) |-> (Y == 1'b1)
    );

    // Any input HIGH implies Y LOW.
    check_any_high_implies_y_low: assert property (
        @(posedge CLK) (A || B || C) |-> (Y == 1'b0)
    );

    // Rising A forces Y LOW in same cycle.
    check_roseA_causes_y_low: assert property (
        @(posedge CLK) $rose(A) |-> (Y == 1'b0)
    );

    // Rising B forces Y LOW in same cycle.
    check_roseB_causes_y_low: assert property (
        @(posedge CLK) $rose(B) |-> (Y == 1'b0)
    );

    // Rising C forces Y LOW in same cycle.
    check_roseC_causes_y_low: assert property (
        @(posedge CLK) $rose(C) |-> (Y == 1'b0)
    );

    // A falling to 0 with B,C already 0 makes Y HIGH.
    check_fellA_others_zero_causes_y_high: assert property (
        @(posedge CLK) ($fell(A) && !B && !C) |-> (Y == 1'b1)
    );

    // B falling to 0 with A,C already 0 makes Y HIGH.
    check_fellB_others_zero_causes_y_high: assert property (
        @(posedge CLK) ($fell(B) && !A && !C) |-> (Y == 1'b1)
    );

    // C falling to 0 with A,B already 0 makes Y HIGH.
    check_fellC_others_zero_causes_y_high: assert property (
        @(posedge CLK) ($fell(C) && !A && !B) |-> (Y == 1'b1)
    );
endmodule