module infrared_control_sva (
    input logic infrared,
    input logic clk,
    input logic reset,
    input logic led,
    input logic botao_1,
    input logic botao_2,
    input logic botao_3,
    input logic botao_4
);

    // LED follows the previous cycle's infrared value.
    check_led_follows_infrared: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) |-> (led == $past(infrared))
    );

    // botao_1 is asserted only in KEEP1 with count below T_PRESS.
    check_botao_1_decode: assert property (
        @(posedge clk) disable iff (reset)
        botao_1 == ($past(1'b1) && $past(!reset) && $past(KEEP1) && ($past(count) < T_PRESS))
    );

    // botao_2 is asserted only in KEEP2 with count below T_PRESS.
    check_botao_2_decode: assert property (
        @(posedge clk) disable iff (reset)
        botao_2 == ($past(1'b1) && $past(!reset) && $past(KEEP2) && ($past(count) < T_PRESS))
    );

    // botao_3 is asserted only in KEEP3 with count below T_PRESS.
    check_botao_3_decode: assert property (
        @(posedge clk) disable iff (reset)
        botao_3 == ($past(1'b1) && $past(!reset) && $past(KEEP3) && ($past(count) < T_PRESS))
    );

    // botao_4 is asserted only in KEEP4 with count below T_PRESS.
    check_botao_4_decode: assert property (
        @(posedge clk) disable iff (reset)
        botao_4 == ($past(1'b1) && $past(!reset) && $past(KEEP4) && ($past(count) < T_PRESS))
    );

    // botao_1 and botao_2 are never asserted together.
    check_botao_12_mutex: assert property (
        @(posedge clk) disable iff (reset)
        !(botao_1 && botao_2)
    );

    // botao_1 and botao_3 are never asserted together.
    check_botao_13_mutex: assert property (
        @(posedge clk) disable iff (reset)
        !(botao_1 && botao_3)
    );

    // botao_1 and botao_4 are never asserted together.
    check_botao_14_mutex: assert property (
        @(posedge clk) disable iff (reset)
        !(botao_1 && botao_4)
    );

    // botao_2 and botao_3 are never asserted together.
    check_botao_23_mutex: assert property (
        @(posedge clk) disable iff (reset)
        !(botao_2 && botao_3)
    );

    // botao_2 and botao_4 are never asserted together.
    check_botao_24_mutex: assert property (
        @(posedge clk) disable iff (reset)
        !(botao_2 && botao_4)
    );

    // botao_3 and botao_4 are never asserted together.
    check_botao_34_mutex: assert property (
        @(posedge clk) disable iff (reset)
        !(botao_3 && botao_4)
    );

    // botao_1 is a one-cycle pulse.
    check_botao_1_one_cycle: assert property (
        @(posedge clk) disable iff (reset)
        botao_1 |=> !botao_1
    );

    // botao_2 is a one-cycle pulse.
    check_botao_2_one_cycle: assert property (
        @(posedge clk) disable iff (reset)
        botao_2 |=> !botao_2
    );

    // botao_3 is a one-cycle pulse.
    check_botao_3_one_cycle: assert property (
        @(posedge clk) disable iff (reset)
        botao_3 |=> !botao_3
    );

    // botao_4 is a one-cycle pulse.
    check_botao_4_one_cycle: assert property (
        @(posedge clk) disable iff (reset)
        botao_4 |=> !botao_4
    );

endmodule