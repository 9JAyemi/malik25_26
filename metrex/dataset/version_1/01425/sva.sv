// SVA for RCB_FRL_LED_Clock and RCB_FRL_LED_Clock_DIV
// Concise, high-quality checks and coverage

module rcb_frl_led_clock_sva #(parameter int THR = 448) (
  input  logic        Test_Clock_in,
  input  logic        RST,
  input  logic [9:0]  count1,
  input  logic [9:0]  count2,
  input  logic [9:0]  count3,
  input  logic        LED_Clock_out,
  input  logic        LED_Clock_out_reg
);

  default clocking cb @(posedge Test_Clock_in); endclocking

  // Output equals reg at all times (combinational assign)
  assert property (cb LED_Clock_out == LED_Clock_out_reg);

  // Reset behavior (synchronous hold while RST=1 at clock edge)
  assert property (@(posedge Test_Clock_in)
                   RST |-> (count1==0 && count2==0 && count3==0 &&
                            LED_Clock_out_reg==0 && LED_Clock_out==0));

  // Value ranges
  assert property (cb disable iff (RST) count1 <= 1000);
  assert property (cb disable iff (RST) count2 <= 1000);
  assert property (cb disable iff (RST) count3 <= THR);

  // Count1 increment path
  assert property (cb disable iff (RST)
                   (count3 < THR && count2 < 1000 && count1 < 1000)
                   |=> (count1 == $past(count1)+1 &&
                        count2 == $past(count2)   &&
                        count3 == $past(count3)   &&
                        LED_Clock_out_reg == $past(LED_Clock_out_reg)));

  // Count1 wrap -> Count2 increment
  assert property (cb disable iff (RST)
                   (count3 < THR && count2 < 1000 && count1 == 1000)
                   |=> (count1 == 0 &&
                        count2 == $past(count2)+1 &&
                        count3 == $past(count3)   &&
                        LED_Clock_out_reg == $past(LED_Clock_out_reg)));

  // Count2 wrap -> Count3 increment (Count1 holds)
  assert property (cb disable iff (RST)
                   (count3 < THR && count2 == 1000)
                   |=> (count2 == 0 &&
                        count3 == $past(count3)+1 &&
                        count1 == $past(count1)   &&
                        LED_Clock_out_reg == $past(LED_Clock_out_reg)));

  // LED toggle only when count3 >= THR, and count3 resets; count1/2 hold
  assert property (cb disable iff (RST)
                   (count3 >= THR)
                   |=> (count3 == 0 &&
                        LED_Clock_out_reg == ~$past(LED_Clock_out_reg) &&
                        count1 == $past(count1) &&
                        count2 == $past(count2)));

  // LED must not change otherwise
  assert property (cb disable iff (RST)
                   (count3 < THR) |=> (LED_Clock_out_reg == $past(LED_Clock_out_reg)));

  // Sanity: count1 only changes by +1 or 0/reset
  assert property (cb disable iff (RST)
                   $changed(count1) |-> (count1 == 0 || count1 == $past(count1)+1));
  // Sanity: count2 only changes by +1 or 0/reset
  assert property (cb disable iff (RST)
                   $changed(count2) |-> (count2 == 0 || count2 == $past(count2)+1));
  // Sanity: count3 only changes by +1 or 0/reset
  assert property (cb disable iff (RST)
                   $changed(count3) |-> (count3 == 0 || count3 == $past(count3)+1));

  // Coverage
  cover property (cb disable iff (RST)
                  (count1 == 1000) ##1 (count1 == 0));           // count1 wrap
  cover property (cb disable iff (RST)
                  (count2 == 1000) ##1 (count2 == 0));           // count2 wrap
  cover property (cb disable iff (RST)
                  (count3 == THR) ##1 (count3 == 0 &&
                   LED_Clock_out_reg != $past(LED_Clock_out_reg))); // LED toggle
  cover property (cb disable iff (RST)
                  (count1 == 1000) ##1 (count2 == 1000) ##1
                  (count3 == THR)   ##1 (LED_Clock_out_reg != $past(LED_Clock_out_reg)));
endmodule


// Bind to both modules with appropriate thresholds
bind RCB_FRL_LED_Clock
  rcb_frl_led_clock_sva #(.THR(448))
    RCB_FRL_LED_Clock_sva_i (
      .Test_Clock_in(Test_Clock_in),
      .RST(RST),
      .count1(count1),
      .count2(count2),
      .count3(count3),
      .LED_Clock_out(LED_Clock_out),
      .LED_Clock_out_reg(LED_Clock_out_reg)
    );

bind RCB_FRL_LED_Clock_DIV
  rcb_frl_led_clock_sva #(.THR(56))
    RCB_FRL_LED_Clock_DIV_sva_i (
      .Test_Clock_in(Test_Clock_in),
      .RST(RST),
      .count1(count1),
      .count2(count2),
      .count3(count3),
      .LED_Clock_out(LED_Clock_out),
      .LED_Clock_out_reg(LED_Clock_out_reg)
    );