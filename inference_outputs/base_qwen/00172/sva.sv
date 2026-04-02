module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
    input logic CLK,
    input logic SLEEP_B,
    output logic X
);
    // SLEEP_B is the sleep signal, active low
    // X is the output, driven by the AND of SLEEP_B and A

    // SLEEP_B should be active low
    sleep_active_low: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP_B == 1'b0
    );

    // X should be driven by the AND of SLEEP_B and A
    x_driven_by_and: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) X == (SLEEP_B & A)
    );

    // SLEEP_B should be driven by the NOT of SLEEP
    sleep_driven_by_not_sleep: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == ~SLEEP_B
    );

    // SLEEP should be active low
    sleep_active_low: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == 1'b0
    );

    // SLEEP_B should be driven by the NOT of SLEEP
    sleep_driven_by_not_sleep: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == ~SLEEP_B
    );

    // SLEEP should be active low
    sleep_active_low: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == 1'b0
    );

    // SLEEP_B should be driven by the NOT of SLEEP
    sleep_driven_by_not_sleep: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == ~SLEEP_B
    );

    // SLEEP should be active low
    sleep_active_low: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == 1'b0
    );

    // SLEEP_B should be driven by the NOT of SLEEP
    sleep_driven_by_not_sleep: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == ~SLEEP_B
    );

    // SLEEP should be active low
    sleep_active_low: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == 1'b0
    );

    // SLEEP_B should be driven by the NOT of SLEEP
    sleep_driven_by_not_sleep: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == ~SLEEP_B
    );

endmodule