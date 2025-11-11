// SVA for pwm_generator
// Bind this module to the DUT to check and cover key behavior concisely.

module pwm_generator_sva
  (input clk, input rst, input pwm_out, input [1:0] counter);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  property p_reset_clears; $rose(rst) |=> (pwm_out==1'b0 && counter==2'b00); endproperty
  property p_reset_holds;  (rst && $past(rst)) |-> (pwm_out==1'b0 && counter==2'b00); endproperty
  assert property(p_reset_clears);
  assert property(p_reset_holds);

  // No X/Z on key signals once out of reset
  assert property(disable iff (rst || $isunknown(rst)) !$isunknown({pwm_out,counter}));

  // Next-state functional relation
  property p_next_incr;
    disable iff (rst)
    ($past(!rst) && $past(counter)!=2'b11) |-> (counter==$past(counter)+2'b01 && pwm_out==1'b0);
  endproperty
  property p_next_wrap;
    disable iff (rst)
    ($past(!rst) && $past(counter)==2'b11) |-> (counter==2'b00 && pwm_out==1'b1);
  endproperty
  assert property(p_next_incr);
  assert property(p_next_wrap);

  // Output constraints (single-cycle high, otherwise low)
  assert property(disable iff (rst) (counter!=2'b00) |-> (pwm_out==1'b0));
  assert property(disable iff (rst) pwm_out |-> (##1 !pwm_out[*3] ##1 pwm_out));

  // Coverage
  cover property(@(posedge clk) $fell(rst) ##1 !pwm_out ##1 !pwm_out ##1 !pwm_out ##1 pwm_out);
  cover property(disable iff (rst) pwm_out ##1 !pwm_out[*3] ##1 pwm_out);
  cover property(disable iff (rst) ($past(counter)==2'b11 && pwm_out));

endmodule

// Bind into the DUT (place in a package or a separate file compiled with the DUT)
bind pwm_generator pwm_generator_sva sva_i (.clk(clk), .rst(rst), .pwm_out(pwm_out), .counter(counter));