// SVA for servo_control
// Bind this module to your DUT: bind servo_control servo_control_sva #(.pwm_period(pwm_period), .pwm_min(pwm_min), .pwm_max(pwm_max)) i_servo_control_sva (.*);

module servo_control_sva #(
  parameter int pwm_period = 20000,
  parameter int pwm_min    = 10,
  parameter int pwm_max    = 90
)(
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  pwm_in,
  input  logic [7:0]  pos_in,
  output logic [7:0]  pwm_out,
  input  logic [7:0]  current_pos,
  input  logic [7:0]  desired_pos,
  input  logic [7:0]  error,
  input  logic [15:0] pwm_counter,
  input  logic        pwm_enable
);

  default clocking cb @ (posedge clk); endclocking

  // Static parameter checks
  initial begin
    assert(pwm_period > 0) else $error("pwm_period must be > 0");
    assert(0 <= pwm_min && pwm_min < pwm_max && pwm_max <= 255) else $error("pwm_min/max out of range or not ordered");
    assert(((pwm_period * pwm_min) / 256) < ((pwm_period * pwm_max) / 256)) else $error("TMIN must be < TMAX");
    assert(((pwm_period * pwm_max) / 256) < pwm_period) else $error("TMAX must be < pwm_period");
  end

  // Helpers computed with full precision
  function automatic int duty_in(input int period, input int val);
    return (period * val) / 256;
  endfunction

  function automatic int calc_pwm_out(input int period, input int minval, input int maxval,
                                      input int cnt, input int in);
    int tmin, tmax, tin, y;
    tmin = (period * minval) / 256;
    tmax = (period * maxval) / 256;
    tin  = (period * in)     / 256;
    if ((cnt < tin) && (cnt < tmax)) y = 255;
    else if (cnt < tmin)             y = 0;
    else                              y = (255 * (cnt - tmin)) / (tmax - tmin);
    if (y < 0)   y = 0;
    if (y > 255) y = 255;
    return y;
  endfunction

  // Reset behavior (synchronous)
  assert property (rst |-> (current_pos==0 && desired_pos==0 && error==0 && pwm_counter==0));

  // Counter bounds and sequence
  assert property (!rst |-> (pwm_counter < pwm_period));
  assert property ($past(!rst) |-> ($past(pwm_counter)==pwm_period-1) -> (pwm_counter==0));
  assert property ($past(!rst) |-> ($past(pwm_counter)!=pwm_period-1) -> (pwm_counter==$past(pwm_counter)+1));

  // pwm_enable correctness
  assert property (pwm_enable == (pwm_counter < duty_in(pwm_period, pwm_in)));

  // Register update semantics
  assert property ($past(rst) -> (current_pos==0))
    else $error("current_pos not reset");
  assert property ($past(!rst) |-> current_pos == ($past(pwm_enable) ? $past(pwm_in) : $past(current_pos)));

  assert property (rst -> (desired_pos==0))
    else $error("desired_pos not reset");
  assert property ($past(!rst) |-> desired_pos == $past(pos_in));

  assert property (error == (desired_pos - current_pos));

  // pwm_out functional equivalence to RTL formula
  assert property (calc_pwm_out(pwm_period, pwm_min, pwm_max, pwm_counter, pwm_in) == pwm_out);

  // Basic sanity (no X/Z after reset deasserted)
  assert property (disable iff (rst) !$isunknown({pwm_in, pos_in, current_pos, desired_pos, error, pwm_counter, pwm_enable, pwm_out}));

  // Coverage
  cover property (pwm_counter==pwm_period-1 ##1 pwm_counter==0);                    // wrap
  cover property (pwm_enable && pwm_out==255);                                      // high segment used
  cover property (!pwm_enable && pwm_counter < ((pwm_period*pwm_min)/256) && pwm_out==0); // low segment used
  cover property ((pwm_counter >= ((pwm_period*pwm_min)/256)) &&
                  (pwm_counter <  ((pwm_period*pwm_max)/256)) &&
                  !((pwm_counter < duty_in(pwm_period,pwm_in)) && (pwm_counter < ((pwm_period*pwm_max)/256))) &&
                  pwm_out inside {[1:254]});                                        // ramp segment observed
  cover property ($changed(pwm_enable));                                            // enable toggles
  cover property ($rose(rst));                                                      // reset seen

endmodule