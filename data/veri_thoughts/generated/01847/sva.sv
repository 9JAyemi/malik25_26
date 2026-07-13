module sky130_fd_sc_lp__clkinvlp_sva (
    input logic Y,
    input logic A
);
    // On A rising edge, output must be inversion of A.
    check_Y_eq_notA_on_A_rise: assert property (
        @(posedge A) (Y === ~A)
    );

    // On A falling edge, output must be inversion of A.
    check_Y_eq_notA_on_A_fall: assert property (
        @(negedge A) (Y === ~A)
    );

    // On A rising edge, Y must fall.
    check_Y_falls_on_A_rise: assert property (
        @(posedge A) $fell(Y)
    );

    // On A falling edge, Y must rise.
    check_Y_rises_on_A_fall: assert property (
        @(negedge A) $rose(Y)
    );

    // On Y rising edge, input must be inversion of Y.
    check_A_eq_notY_on_Y_rise: assert property (
        @(posedge Y) (A === ~Y)
    );

    // On Y falling edge, input must be inversion of Y.
    check_A_eq_notY_on_Y_fall: assert property (
        @(negedge Y) (A === ~Y)
    );

    // Y rising implies A fell in the same cycle.
    check_A_falls_on_Y_rise: assert property (
        @(posedge Y) $fell(A)
    );

    // Y falling implies A rose in the same cycle.
    check_A_rises_on_Y_fall: assert property (
        @(negedge Y) $rose(A)
    );
endmodule