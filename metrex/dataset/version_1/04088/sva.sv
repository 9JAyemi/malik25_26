// SVA for led_controller
module led_controller_sva (
  input logic        CLOCK,
  input logic        RESET,
  input logic [2:0]  MODE,
  input logic        FAST,
  input logic [7:0]  LED,
  input logic [7:0]  brightness,
  input logic [6:0]  counter
);

  default clocking cb @(posedge CLOCK); endclocking
  default disable iff (RESET);

  function automatic logic [7:0] map_brightness (input logic [2:0] m);
    case (m)
      3'b000: map_brightness = 8'd0;
      3'b001: map_brightness = 8'd8;
      3'b010: map_brightness = 8'd12;
      3'b011: map_brightness = 8'd15;
      default: map_brightness = 8'd0;
    endcase
  endfunction

  sequence term_fast; FAST  && counter == 7'd9;  endsequence
  sequence term_slow; !FAST && counter == 7'd99; endsequence
  sequence term_any;  term_fast or term_slow;    endsequence

  // Reset behavior (synchronous)
  assert property (@(posedge CLOCK) RESET |=> (brightness == 8'd0 && counter == 7'd0));

  // LED reflects brightness
  assert property (LED == brightness);

  // Counter progression
  assert property (FAST  && counter != 7'd9  |=> counter == (($past(counter)==7'd127) ? 7'd0 : $past(counter)+7'd1));
  assert property (!FAST && counter != 7'd99 |=> counter == (($past(counter)==7'd127) ? 7'd0 : $past(counter)+7'd1));

  // Counter reset at terminal counts
  assert property (term_fast |=> counter == 7'd0);
  assert property (term_slow |=> counter == 7'd0);

  // Brightness updates only at terminal counts (and matches MODE map)
  assert property (term_fast |=> brightness == map_brightness($past(MODE)));
  assert property (term_slow |=> brightness == map_brightness($past(MODE)));
  assert property (!(term_fast || term_slow) |=> $stable(brightness));

  // Brightness only takes legal values
  assert property (brightness inside {8'd0, 8'd8, 8'd12, 8'd15});

  // Coverage
  cover property (term_fast);
  cover property (term_slow);
  cover property (term_any |=> brightness == 8'd0);
  cover property (term_any |=> brightness == 8'd8);
  cover property (term_any |=> brightness == 8'd12);
  cover property (term_any |=> brightness == 8'd15);
  cover property ((term_any && (MODE inside {3'b100,3'b101,3'b110,3'b111})) |=> brightness == 8'd0);
  cover property ($rose(FAST) ##[1:200] term_fast);

endmodule

// Bind into DUT
bind led_controller led_controller_sva sva_i (
  .CLOCK(CLOCK),
  .RESET(RESET),
  .MODE(MODE),
  .FAST(FAST),
  .LED(LED),
  .brightness(brightness),
  .counter(counter)
);