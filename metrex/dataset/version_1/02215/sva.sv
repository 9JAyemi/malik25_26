// SVA checker for my_module
module my_module_sva(
  input logic         CLOCK_IN,
  input logic         RESET,
  input logic [2:0]   SWITCH,
  input logic [3:0]   LED
);

  default clocking cb @(posedge CLOCK_IN); endclocking

  // Golden mapping
  function automatic logic [3:0] map_led (input logic [2:0] sw);
    case (sw)
      3'b000: map_led = 4'b0001;
      3'b001: map_led = 4'b0010;
      3'b010: map_led = 4'b0100;
      3'b011: map_led = 4'b1000;
      default: map_led = 4'b1111;
    endcase
  endfunction

  // Sanity: no unknowns on key signals
  assert property (!$isunknown({RESET,SWITCH,LED})));

  // Core functional correctness (synchronous): LED equals spec each cycle
  assert property (LED == (RESET ? 4'b0000 : map_led(SWITCH)));

  // Structural/safety refinements
  // One-hot when SWITCH in 0..3 and not in reset
  assert property ((!RESET && (SWITCH inside {[3'b000:3'b011]})) |-> $onehot(LED));
  // Default branch tightness
  assert property ((!RESET && (SWITCH inside {[3'b100:3'b111]})) |-> (LED == 4'b1111));
  assert property ((LED == 4'b1111) |-> (!RESET && (SWITCH inside {[3'b100:3'b111]})));
  // 0000 only during reset
  assert property ((LED == 4'b0000) |-> RESET);

  // Coverage: reset, each mapping, and default path
  cover property (RESET && LED == 4'b0000);
  cover property (!RESET && SWITCH == 3'b000 && LED == 4'b0001);
  cover property (!RESET && SWITCH == 3'b001 && LED == 4'b0010);
  cover property (!RESET && SWITCH == 3'b010 && LED == 4'b0100);
  cover property (!RESET && SWITCH == 3'b011 && LED == 4'b1000);
  cover property (!RESET && (SWITCH inside {[3'b100:3'b111]}) && LED == 4'b1111);

endmodule

// Bind into DUT (example):
// bind my_module my_module_sva u_my_module_sva(.CLOCK_IN(CLOCK_IN), .RESET(RESET), .SWITCH(SWITCH), .LED(LED));