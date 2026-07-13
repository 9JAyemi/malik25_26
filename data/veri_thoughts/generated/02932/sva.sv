module PruebaSeleccion_sva (
    input  logic        clk,
    input  logic [3:0]  in,
    input  logic        btn0,
    input  logic        btn1,
    input  logic        btn2,
    input  logic        btn3,
    input  logic [6:0]  out,
    input  logic        led0,
    input  logic        led1,
    input  logic        led2,
    input  logic        led3,
    input  logic        ledAux0,
    input  logic        ledAux1,
    input  logic        ledAux2,
    input  logic        ledAux3
);
    // Clock: clk (posedge). No reset in RTL. Sequential logic (posedge-triggered).

    ///// LED outputs mirror internal aux registers /////
    // led0 equals ledAux0 every cycle.
    check_led0_mirrors_aux: assert property (
        @(posedge clk) (led0 == ledAux0)
    );
    // led1 equals ledAux1 every cycle.
    check_led1_mirrors_aux: assert property (
        @(posedge clk) (led1 == ledAux1)
    );
    // led2 equals ledAux2 every cycle.
    check_led2_mirrors_aux: assert property (
        @(posedge clk) (led2 == ledAux2)
    );
    // led3 equals ledAux3 every cycle.
    check_led3_mirrors_aux: assert property (
        @(posedge clk) (led3 == ledAux3)
    );

    ///// Button priority and LED pattern /////
    // If btn0 is high, next cycle LEDs are 0,1,1,1 (highest priority).
    check_btn0_sets_leds: assert property (
        @(posedge clk) (btn0 == 1'b1) |=> (led0 == 1'b0 && led1 == 1'b1 && led2 == 1'b1 && led3 == 1'b1)
    );
    // If btn1 is high and btn0 is low, next cycle LEDs are 1,0,1,1.
    check_btn1_sets_leds_when_btn0_low: assert property (
        @(posedge clk) (btn0 == 1'b0 && btn1 == 1'b1) |=> (led0 == 1'b1 && led1 == 1'b0 && led2 == 1'b1 && led3 == 1'b1)
    );
    // If btn2 is high and higher-priority buttons are low, next cycle LEDs are 1,1,0,1.
    check_btn2_sets_leds_when_higher_low: assert property (
        @(posedge clk) (btn0 == 1'b0 && btn1 == 1'b0 && btn2 == 1'b1) |=> (led0 == 1'b1 && led1 == 1'b1 && led2 == 1'b0 && led3 == 1'b1)
    );
    // If btn3 is high and others are low, next cycle LEDs are 1,1,1,0.
    check_btn3_sets_leds_when_others_low: assert property (
        @(posedge clk) (btn0 == 1'b0 && btn1 == 1'b0 && btn2 == 1'b0 && btn3 == 1'b1) |=> (led0 == 1'b1 && led1 == 1'b1 && led2 == 1'b1 && led3 == 1'b0)
    );

    ///// 7-seg decode mapping (out follows in on next cycle) /////
    // in == 0 -> out = 1000000
    check_decode_out_0: assert property (
        @(posedge clk) (in == 4'h0) |=> (out == 7'b1000000)
    );
    // in == 1 -> out = 1111001
    check_decode_out_1: assert property (
        @(posedge clk) (in == 4'h1) |=> (out == 7'b1111001)
    );
    // in == 2 -> out = 0100100
    check_decode_out_2: assert property (
        @(posedge clk) (in == 4'h2) |=> (out == 7'b0100100)
    );
    // in == 3 -> out = 0110000
    check_decode_out_3: assert property (
        @(posedge clk) (in == 4'h3) |=> (out == 7'b0110000)
    );
    // in == 4 -> out = 0011001
    check_decode_out_4: assert property (
        @(posedge clk) (in == 4'h4) |=> (out == 7'b0011001)
    );
    // in == 5 -> out = 0010010
    check_decode_out_5: assert property (
        @(posedge clk) (in == 4'h5) |=> (out == 7'b0010010)
    );
    // in == 6 -> out = 0000010
    check_decode_out_6: assert property (
        @(posedge clk) (in == 4'h6) |=> (out == 7'b0000010)
    );
    // in == 7 -> out = 1111000
    check_decode_out_7: assert property (
        @(posedge clk) (in == 4'h7) |=> (out == 7'b1111000)
    );
    // in == 8 -> out = 0000000
    check_decode_out_8: assert property (
        @(posedge clk) (in == 4'h8) |=> (out == 7'b0000000)
    );
    // in == 9 -> out = 0010000
    check_decode_out_9: assert property (
        @(posedge clk) (in == 4'h9) |=> (out == 7'b0010000)
    );
    // in == A -> out = 0001000
    check_decode_out_A: assert property (
        @(posedge clk) (in == 4'hA) |=> (out == 7'b0001000)
    );
    // in == B -> out = 0000011
    check_decode_out_B: assert property (
        @(posedge clk) (in == 4'hB) |=> (out == 7'b0000011)
    );
    // in == C -> out = 1000110
    check_decode_out_C: assert property (
        @(posedge clk) (in == 4'hC) |=> (out == 7'b1000110)
    );
    // in == D -> out = 0100001
    check_decode_out_D: assert property (
        @(posedge clk) (in == 4'hD) |=> (out == 7'b0100001)
    );
    // in == E -> out = 0000110
    check_decode_out_E: assert property (
        @(posedge clk) (in == 4'hE) |=> (out == 7'b0000110)
    );
    // in == F -> out = 0001110
    check_decode_out_F: assert property (
        @(posedge clk) (in == 4'hF) |=> (out == 7'b0001110)
    );
endmodule