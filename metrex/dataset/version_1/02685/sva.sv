// SVA checker for led_controller
module led_controller_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic [26:0] counter,
  input  logic [3:0]  leds_0,
  input  logic [3:0]  leds_1,
  input  logic [3:0]  leds_2,
  input  logic [3:0]  leds_3
);
  default clocking @(posedge clk); endclocking

  // Thresholds (match DUT intent)
  localparam longint unsigned T0_ON   = 0;
  localparam longint unsigned T0_OFF  = 25_000_000;
  localparam longint unsigned T1_ON   = 50_000_000;
  localparam longint unsigned T1_OFF  = 100_000_000;
  localparam longint unsigned T2_ON   = 200_000_000;
  localparam longint unsigned T2_OFF  = 400_000_000;
  localparam longint unsigned T3_ON   = 800_000_000;
  localparam longint unsigned T3_OFF  = 1_600_000_000;

  // Guard for $past/$changed
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic known/encoding checks
  ap_known:        assert property ( !$isunknown({counter,leds_0,leds_1,leds_2,leds_3}) );
  ap_led_encoding: assert property ( leds_0 inside {4'h0,4'hF} && leds_1 inside {4'h0,4'hF}
                                   && leds_2 inside {4'h0,4'hF} && leds_3 inside {4'h0,4'hF} );

  // Synchronous reset drives all to zero
  ap_reset: assert property ( rst |-> (counter==0 && leds_0==0 && leds_1==0 && leds_2==0 && leds_3==0) );

  // Counter increments each cycle except wrap at T3_OFF
  ap_inc:  assert property ( disable iff (!past_valid || rst)
                             ($past(!rst) && $past(counter)!=T3_OFF) |-> counter==$past(counter)+1 );
  ap_wrap: assert property ( disable iff (!past_valid || rst)
                             ($past(!rst) && $past(counter)==T3_OFF) |-> (counter==0 && leds_3==0) );

  // Correct LED values at threshold cycles
  ap_l0_on:  assert property ( disable iff (!past_valid || rst) ($past(counter)==T0_ON)  |-> leds_0==4'hF );
  ap_l0_off: assert property ( disable iff (!past_valid || rst) ($past(counter)==T0_OFF) |-> leds_0==4'h0 );
  ap_l1_on:  assert property ( disable iff (!past_valid || rst) ($past(counter)==T1_ON)  |-> leds_1==4'hF );
  ap_l1_off: assert property ( disable iff (!past_valid || rst) ($past(counter)==T1_OFF) |-> leds_1==4'h0 );
  ap_l2_on:  assert property ( disable iff (!past_valid || rst) ($past(counter)==T2_ON)  |-> leds_2==4'hF );
  ap_l2_off: assert property ( disable iff (!past_valid || rst) ($past(counter)==T2_OFF) |-> leds_2==4'h0 );
  ap_l3_on:  assert property ( disable iff (!past_valid || rst) ($past(counter)==T3_ON)  |-> leds_3==4'hF );
  ap_l3_off: assert property ( disable iff (!past_valid || rst) ($past(counter)==T3_OFF) |-> leds_3==4'h0 );

  // LEDs change only at intended thresholds (or under reset)
  ap_l0_only_when: assert property ( disable iff (!past_valid || rst)
                                     $changed(leds_0) |-> $past(counter) inside {T0_ON,T0_OFF} );
  ap_l1_only_when: assert property ( disable iff (!past_valid || rst)
                                     $changed(leds_1) |-> $past(counter) inside {T1_ON,T1_OFF} );
  ap_l2_only_when: assert property ( disable iff (!past_valid || rst)
                                     $changed(leds_2) |-> $past(counter) inside {T2_ON,T2_OFF} );
  ap_l3_only_when: assert property ( disable iff (!past_valid || rst)
                                     $changed(leds_3) |-> $past(counter) inside {T3_ON,T3_OFF} );

  // Coverage: reset, each threshold event, wrap
  cv_reset:  cover property ( rst );
  cv_t0_on:  cover property ( disable iff (!past_valid || rst) $past(counter)==T0_ON  && leds_0==4'hF );
  cv_t0_off: cover property ( disable iff (!past_valid || rst) $past(counter)==T0_OFF && leds_0==4'h0 );
  cv_t1_on:  cover property ( disable iff (!past_valid || rst) $past(counter)==T1_ON  && leds_1==4'hF );
  cv_t1_off: cover property ( disable iff (!past_valid || rst) $past(counter)==T1_OFF && leds_1==4'h0 );
  cv_t2_on:  cover property ( disable iff (!past_valid || rst) $past(counter)==T2_ON  && leds_2==4'hF );
  cv_t2_off: cover property ( disable iff (!past_valid || rst) $past(counter)==T2_OFF && leds_2==4'h0 );
  cv_t3_on:  cover property ( disable iff (!past_valid || rst) $past(counter)==T3_ON  && leds_3==4'hF );
  cv_wrap:   cover property ( disable iff (!past_valid || rst) $past(counter)==T3_OFF ##1 (counter==0 && leds_3==0) );

  // Optional elaboration-time check for reachability vs counter width (warn if unreachable)
  initial begin
    if (T3_OFF > ((1<<$bits(counter))-1))
      $warning("Thresholds exceed counter width: some LED events are unreachable (counter is %0d bits).", $bits(counter));
  end
endmodule

// Bind into DUT
bind led_controller led_controller_sva u_led_controller_sva (
  .clk(clk), .rst(rst), .counter(counter),
  .leds_0(leds_0), .leds_1(leds_1), .leds_2(leds_2), .leds_3(leds_3)
);