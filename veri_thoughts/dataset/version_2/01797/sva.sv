module traffic_light_controller_sva (
  input logic clk,
  input logic reset,
  input logic green_led,
  input logic yellow_led,
  input logic red_led,
  input logic [1:0] state,
  input logic [3:0] green_counter,
  input logic [1:0] yellow_counter,
  input logic [4:0] red_counter
);
  // Local copies of state encodings
  localparam logic [1:0] GREEN  = 2'b00;
  localparam logic [1:0] YELLOW = 2'b01;
  localparam logic [1:0] RED    = 2'b10;

  ///// Reset behavior /////
  // On a clock edge while reset is HIGH, state/counters are in reset values.
  reset_state_counters: assert property (
    @(posedge clk) reset |-> (state == GREEN) && (green_counter == 4'd0) && (yellow_counter == 2'd0) && (red_counter == 5'd0)
  );
  // On a clock edge while reset is HIGH, outputs reflect GREEN.
  reset_outputs_green: assert property (
    @(posedge clk) reset |-> (green_led == 1'b1) && (yellow_led == 1'b0) && (red_led == 1'b0)
  );

  ///// State encoding and outputs /////
  // State must always be one of GREEN/YELLOW/RED.
  state_valid_encoding: assert property (
    @(posedge clk) disable iff (reset) (state == GREEN) || (state == YELLOW) || (state == RED)
  );
  // Output decode for GREEN.
  decode_green: assert property (
    @(posedge clk) disable iff (reset) (state == GREEN) |-> (green_led == 1'b1) && (yellow_led == 1'b0) && (red_led == 1'b0)
  );
  // Output decode for YELLOW.
  decode_yellow: assert property (
    @(posedge clk) disable iff (reset) (state == YELLOW) |-> (green_led == 1'b0) && (yellow_led == 1'b1) && (red_led == 1'b0)
  );
  // Output decode for RED.
  decode_red: assert property (
    @(posedge clk) disable iff (reset) (state == RED) |-> (green_led == 1'b0) && (yellow_led == 1'b0) && (red_led == 1'b1)
  );
  // Exactly one LED is ON at a time.
  leds_onehot: assert property (
    @(posedge clk) disable iff (reset) $onehot({green_led, yellow_led, red_led})
  );

  ///// GREEN state behavior /////
  // While in GREEN and count < 10, stay in GREEN and increment green_counter; others unchanged.
  green_count_increments: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset) && (state == GREEN) && (green_counter != 4'd10)
      |=> (state == GREEN)
       && (green_counter == $past(green_counter) + 1)
       && (yellow_counter == $past(yellow_counter))
       && (red_counter == $past(red_counter))
  );
  // When green_counter == 10, transition to YELLOW and clear all counters.
  green_to_yellow_on_10: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset) && (state == GREEN) && (green_counter == 4'd10)
      |=> (state == YELLOW)
       && (green_counter == 4'd0) && (yellow_counter == 2'd0) && (red_counter == 5'd0)
  );
  // In GREEN, green_counter never exceeds 10.
  green_counter_bounded: assert property (
    @(posedge clk) disable iff (reset) (state == GREEN) |-> (green_counter <= 4'd10)
  );

  ///// YELLOW state behavior /////
  // While in YELLOW and count < 2, stay in YELLOW and increment yellow_counter; others unchanged.
  yellow_count_increments: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset) && (state == YELLOW) && (yellow_counter != 2'd2)
      |=> (state == YELLOW)
       && (yellow_counter == $past(yellow_counter) + 1)
       && (green_counter == $past(green_counter))
       && (red_counter == $past(red_counter))
  );
  // When yellow_counter == 2, transition to RED and clear all counters.
  yellow_to_red_on_2: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset) && (state == YELLOW) && (yellow_counter == 2'd2)
      |=> (state == RED)
       && (green_counter == 4'd0) && (yellow_counter == 2'd0) && (red_counter == 5'd0)
  );
  // In YELLOW, yellow_counter never exceeds 2.
  yellow_counter_bounded: assert property (
    @(posedge clk) disable iff (reset) (state == YELLOW) |-> (yellow_counter <= 2'd2)
  );

  ///// RED state behavior /////
  // While in RED and count < 15, stay in RED and increment red_counter; others unchanged.
  red_count_increments: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset) && (state == RED) && (red_counter != 5'd15)
      |=> (state == RED)
       && (red_counter == $past(red_counter) + 1)
       && (green_counter == $past(green_counter))
       && (yellow_counter == $past(yellow_counter))
  );
  // When red_counter == 15, transition to GREEN and clear all counters.
  red_to_green_on_15: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset) && (state == RED) && (red_counter == 5'd15)
      |=> (state == GREEN)
       && (green_counter == 4'd0) && (yellow_counter == 2'd0) && (red_counter == 5'd0)
  );
  // In RED, red_counter never exceeds 15.
  red_counter_bounded: assert property (
    @(posedge clk) disable iff (reset) (state == RED) |-> (red_counter <= 5'd15)
  );

  ///// Counters outside active state /////
  // green_counter is 0 outside GREEN.
  green_zero_outside_green: assert property (
    @(posedge clk) disable iff (reset) (state != GREEN) |-> (green_counter == 4'd0)
  );
  // yellow_counter is 0 outside YELLOW.
  yellow_zero_outside_yellow: assert property (
    @(posedge clk) disable iff (reset) (state != YELLOW) |-> (yellow_counter == 2'd0)
  );
  // red_counter is 0 outside RED.
  red_zero_outside_red: assert property (
    @(posedge clk) disable iff (reset) (state != RED) |-> (red_counter == 5'd0)
  );

endmodule