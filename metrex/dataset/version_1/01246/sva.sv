// SVA for top_module. Bind this onto the DUT.
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  d,
  input  logic        pwm,
  input  logic [7:0]  q,
  input  logic [7:0]  out,
  input  logic [7:0]  counter,
  input  logic [7:0]  adder_out,
  input  logic        pwm_out
);

  default clocking @(posedge clk); endclocking
  default disable iff (reset)

  // Counter behavior
  assert property ( $past(1'b1) && !$past(reset) && ($past(counter)!=8'hff) |-> counter == $past(counter)+8'd1 )
    else $error("Counter failed to increment by 1");
  assert property ( $past(1'b1) && !$past(reset) && ($past(counter)==8'hff) |-> counter == 8'h00 )
    else $error("Counter failed to wrap at 0xFF");

  // Reset effect on counter (not disabled during reset)
  assert property (@(posedge clk) reset |=> counter==8'h00 )
    else $error("Counter not cleared by reset");
  assert property (@(posedge clk) $past(1'b1) && reset && $past(reset) |-> counter==8'h00 )
    else $error("Counter not held at 0 during reset");

  // Adder pipeline: adder_out[n] = counter[n-1] + d[n-1]
  assert property ( $past(1'b1) |-> adder_out == (($past(counter)+$past(d)) & 8'hff) )
    else $error("adder_out mismatch");

  // PWM pipeline and mirroring: pwm_out[n] = (adder_out[n-1] > 0x80); pwm == pwm_out
  assert property ( $past(1'b1) |-> pwm_out == ($past(adder_out) > 8'h80) )
    else $error("pwm_out mismatch vs adder_out");
  assert property ( pwm == pwm_out )
    else $error("pwm != pwm_out");

  // q follows counter: q[n] = counter[n-1]
  assert property ( $past(1'b1) |-> q == $past(counter) )
    else $error("q != $past(counter)");

  // out[n] = pwm_out[n-1] ? q[n-1] : 0
  assert property ( $past(1'b1) |-> out == ( $past(pwm_out) ? $past(q) : 8'h00 ) )
    else $error("out mismatch vs q/pwm_out");

  // Known-value check post-reset
  assert property ( !$isunknown({pwm, q, out, counter, adder_out, pwm_out}) )
    else $error("X/Z detected on key signals");

  // Functional coverage
  cover property ( counter==8'hff ##1 counter==8'h00 );     // rollover
  cover property ( adder_out==8'h80 ##1 !pwm_out );         // threshold low
  cover property ( adder_out==8'h81 ##1 pwm_out );          // threshold high
  cover property ( !pwm_out ##1 pwm_out );                  // PWM 0->1
  cover property ( pwm_out ##1 !pwm_out );                  // PWM 1->0
  cover property ( $past(1'b1) &&  $past(pwm_out) && (out==q) );     // out passes q
  cover property ( $past(1'b1) && !$past(pwm_out) && (out==8'h00) ); // out zeroed
endmodule

bind top_module top_module_sva i_top_module_sva (
  .clk       (clk),
  .reset     (reset),
  .d         (d),
  .pwm       (pwm),
  .q         (q),
  .out       (out),
  .counter   (counter),
  .adder_out (adder_out),
  .pwm_out   (pwm_out)
);