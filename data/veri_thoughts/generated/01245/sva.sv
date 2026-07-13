module sky130_fd_sc_hdll__clkinvlp_sva (
    input logic Y,
    input logic A
);
    // On A rising edge, Y must be low (Y = ~A).
    check_inversion_on_posedge_A: assert property (
        @(posedge A) (Y == 1'b0)
    );

    // On A falling edge, Y must be high (Y = ~A).
    check_inversion_on_negedge_A: assert property (
        @(negedge A) (Y == 1'b1)
    );

    // On Y rising edge, A must be low (Y = ~A).
    check_input_low_on_posedge_Y: assert property (
        @(posedge Y) (A == 1'b0)
    );

    // On Y falling edge, A must be high (Y = ~A).
    check_input_high_on_negedge_Y: assert property (
        @(negedge Y) (A == 1'b1)
    );
endmodule