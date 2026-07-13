module sky130_fd_sc_lp__clkinvlp_sva (
    input logic CLK,
    input logic RESETn,
    input logic Y,
    input logic A
);
    // Y is always the logical inversion of A.
    check_inversion: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == ~A)
    );

    // A rising edge implies Y falls in the same cycle.
    check_a_rise_y_fall: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(A) |-> $fell(Y)
    );

    // A falling edge implies Y rises in the same cycle.
    check_a_fall_y_rise: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(A) |-> $rose(Y)
    );

    // Y rising edge implies A fell in the same cycle.
    check_y_rise_a_fall: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(Y) |-> $fell(A)
    );

    // Y falling edge implies A rose in the same cycle.
    check_y_fall_a_rise: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(Y) |-> $rose(A)
    );

    // Y only changes when A changes.
    check_y_change_requires_a_change: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(Y) |-> $changed(A)
    );

    // If A is stable, Y remains stable.
    check_a_stable_implies_y_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(A) |-> $stable(Y)
    );

    // A and Y are never both HIGH simultaneously.
    check_never_both_high: assert property (
        @(posedge CLK) disable iff (!RESETn) !(A && Y)
    );
endmodule