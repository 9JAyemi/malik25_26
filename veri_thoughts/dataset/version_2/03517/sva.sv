module clkdlybuf4s_sva #(
    parameter int DELAY_CYCLES = 4
) (
    input logic CLK,
    input logic RST,
    input logic CLK_OUT
);

    // A sampled reset cycle forces CLK_OUT low by the next clock.
    check_reset_forces_low_on_next_clock: assert property (
        @(posedge CLK) disable iff ($initstate)
        RST |=> !CLK_OUT
    );

    // After reset release, the first active clock still sees CLK_OUT low.
    check_clk_out_low_on_first_clock_after_reset_release: assert property (
        @(posedge CLK) disable iff (RST || $initstate)
        $fell(RST) |-> !CLK_OUT
    );

    // After reset release, CLK_OUT stays low for DELAY_CYCLES+1 sampled clocks.
    check_clk_out_low_for_delay_after_reset_release: assert property (
        @(posedge CLK) disable iff (RST || $initstate)
        $fell(RST) |-> (!CLK_OUT)[* (DELAY_CYCLES+1)]
    );

    // After that delay, CLK_OUT rises and remains high on the following clock.
    check_clk_out_rises_and_sticks_after_delay: assert property (
        @(posedge CLK) disable iff (RST || $initstate)
        $fell(RST) |-> ((!CLK_OUT)[* (DELAY_CYCLES+1)] ##1 $rose(CLK_OUT) ##1 CLK_OUT)
    );

endmodule