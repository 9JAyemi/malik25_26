module sky130_fd_sc_ms__clkinv_sva (
    input logic Y,
    input logic A
);
    // On A rising edge, Y must be LOW (inversion of A).
    check_y_low_on_a_rise: assert property (
        @(posedge A) (Y == 1'b0)
    );

    // On A falling edge, Y must be HIGH (inversion of A).
    check_y_high_on_a_fall: assert property (
        @(negedge A) (Y == 1'b1)
    );

    // On Y rising edge, A must be LOW (inverse mapping).
    check_a_low_on_y_rise: assert property (
        @(posedge Y) (A == 1'b0)
    );

    // On Y falling edge, A must be HIGH (inverse mapping).
    check_a_high_on_y_fall: assert property (
        @(negedge Y) (A == 1'b1)
    );
endmodule