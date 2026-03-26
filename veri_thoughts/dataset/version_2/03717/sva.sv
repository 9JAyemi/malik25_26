module led_controller_sva(
    input logic clk,
    input logic SW_0,
    input logic SW_1,
    input logic SW_2,
    input logic SW_3,
    input logic LED_0,
    input logic LED_1,
    input logic LED_2,
    input logic LED_3
);

    // DUT is combinational with no reset; clk is the assertion sampling clock.

    // LED_0 is high only when SW_0 is exactly low.
    check_led0_active_low: assert property (
        @(posedge clk) LED_0 === (SW_0 === 1'b0)
    );

    // LED_1 is high only when SW_1 is exactly low.
    check_led1_active_low: assert property (
        @(posedge clk) LED_1 === (SW_1 === 1'b0)
    );

    // LED_2 is high only when SW_2 is exactly low.
    check_led2_active_low: assert property (
        @(posedge clk) LED_2 === (SW_2 === 1'b0)
    );

    // LED_3 is high only when SW_3 is exactly low.
    check_led3_active_low: assert property (
        @(posedge clk) LED_3 === (SW_3 === 1'b0)
    );

endmodule