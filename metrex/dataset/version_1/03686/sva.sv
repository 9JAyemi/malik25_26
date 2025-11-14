// SVA for PWM (bindable, concise, and DUT-accurate)
module PWM_sva #(parameter p=8)
(
  input clk,
  input rst,
  input [p-1:0] mod,
  input [p-1:0] counter,
  input pwm,
  input pwm_reg
);

  localparam [p-1:0] MAX = {p{1'b1}};

  default clocking cb @(posedge clk); endclocking

  // Safety / reset
  assert property (disable iff (rst) !$isunknown({counter,pwm}));
  assert property (@(posedge clk) rst |-> (counter==0 && pwm==0));
  assert property (disable iff (rst) counter <= MAX);

  // Counter behavior
  assert property (@(posedge clk) (!rst && !$past(rst)) |-> counter == $past(counter)+1);
  assert property (@(posedge clk) (!rst && !$past(rst) && $past(counter)==MAX) |-> counter==0);

  // PWM function (registered compare vs previous state)
  assert property (@(posedge clk) (!rst && !$past(rst)) |-> pwm == ($past(counter) < $past(mod)));
  assert property (disable iff (rst) pwm == pwm_reg);

  // Corner cases
  assert property (@(posedge clk) (!rst && !$past(rst) && ($past(mod)==0)) |-> pwm==0);
  assert property (@(posedge clk) (!rst && !$past(rst) && ($past(mod)==MAX)) |-> pwm == ($past(counter)!=MAX));

  // Coverage
  cover property (@(posedge clk) !rst && $past(counter)==MAX && counter==0);     // wrap
  cover property (@(posedge clk) !rst && $past(pwm)==0 && pwm==1);               // rising edge
  cover property (@(posedge clk) !rst && $past(pwm)==1 && pwm==0);               // falling edge
  cover property (@(posedge clk) !rst && mod==0 && pwm==0);                      // 0% duty
  cover property (@(posedge clk) !rst && mod==MAX);                              // ~100% duty case exercised
  cover property (@(posedge clk) !rst && $changed(mod));                         // dynamic modulation seen
  if (p>1) cover property (@(posedge clk) !rst && mod==(MAX>>1));                // ~50% duty case

endmodule

// Bind to DUT (accesses internal counter and pwm_reg)
bind PWM PWM_sva #(.p(p)) u_pwm_sva (.*);