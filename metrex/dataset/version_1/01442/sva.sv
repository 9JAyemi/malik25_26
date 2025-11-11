// SVA for axi_timer
// Concise, high-value checks + targeted coverage
module axi_timer_sva
  #(parameter WIDTH = 32, parameter TICK_RATE = 1)
  (input  logic                   clk, rst, enable, load,
   input  logic [WIDTH-1:0]       value,
   input  logic [WIDTH-1:0]       timer,
   input  logic                   done,

   // internal DUT state (bound hierarchically)
   input  logic [WIDTH-1:0]       count,
   input  logic [WIDTH-1:0]       load_value
  );

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity (TICK_RATE unused in RTL)
  initial begin
    if (TICK_RATE != 1) $warning("axi_timer: TICK_RATE parameter is unused by RTL (TICK_RATE=%0d)", TICK_RATE);
  end

  // Combinational tie-off
  ap_timer_equals_count: assert property (timer == count);

  // Synchronous reset behavior
  ap_reset: assert property (rst |=> (count == '0 && done == 1'b0));

  // Enable gating: hold count; done forced low
  ap_disable_holds: assert property ((!enable) |=> (count == $past(count) && done == 1'b0));

  // Load behavior: update load_value from value; count takes previous load_value; done low
  ap_load_path: assert property ((enable && load)
                                 |=> (load_value == $past(value)
                                      && count == $past(load_value)
                                      && done == 1'b0));

  // Count-down when enabled and not loading
  ap_decrement: assert property ((enable && !load && count > '0)
                                 |=> (count == $past(count) - 1 && done == 1'b0));

  // Wrap and done pulse when hitting zero (no load)
  ap_wrap_done: assert property ((enable && !load && count == '0)
                                 |=> (done == 1'b1 && count == $past(load_value)));

  // Done implies prior zero-hit under enable and no load
  ap_done_cause: assert property (done |-> $past(enable && !load && ($past(count) == '0)));

  // If period > 0, done is a one-cycle pulse
  ap_done_one_pulse_when_period_nonzero: assert property ((done && $past(load_value) != '0) |-> !done);

  // load_value only changes on (enable && load)
  ap_load_value_stable_otherwise: assert property (!(enable && load) |=> (load_value == $past(load_value)));

  // Basic safety: no underflow on decrement (monotonic non-increase except on reload)
  ap_no_increase_while_counting: assert property ((enable && !load && $past(count) > '0)
                                                  |-> (count <= $past(count)));

  // Coverage
  cp_reset:           cover property (rst);
  cp_load:            cover property ((enable && load) ##1 (load_value == $past(value)) ##1 (count == $past(load_value)));
  cp_decrement:       cover property ((enable && !load && count > 2) ##1 (count == $past(count) - 1));
  cp_wrap_and_done:   cover property ((enable && !load && count == '0) ##1 (done && count == $past(load_value)));
  cp_disable_hold:    cover property ((!enable) ##1 (count == $past(count) && done == 1'b0));
  // Repeated done when period is zero
  cp_zero_periodic:   cover property ((enable && !load && load_value == '0 && count == '0)
                                      ##1 (done && count == '0)
                                      ##1 (done && count == '0));
  // Full-use flow: load -> count down -> done
  cp_full_flow:       cover property ((enable && load)
                                      ##1 (count == $past(load_value))
                                      ##[1:$] (enable && !load && count == '0)
                                      ##1 done);

endmodule

// Bind into DUT; internal regs wired by name
bind axi_timer axi_timer_sva #(.WIDTH(WIDTH), .TICK_RATE(TICK_RATE))
  axi_timer_sva_i (.clk(clk), .rst(rst), .enable(enable), .load(load),
                   .value(value), .timer(timer), .done(done),
                   .count(count), .load_value(load_value));