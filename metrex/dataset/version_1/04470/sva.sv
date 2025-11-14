// SVA for jt51_timers and jt51_timer
// Bind these checkers to the DUT for assertion/coverage

// Top-level IRQ checks
module jt51_timers_sva(
  input clk, rst,
  input flag_A, flag_B,
  input enable_irq_A, enable_irq_B,
  input irq_n
);
  default clocking cb @(posedge clk); endclocking

  // IRQ combinational relation
  assert property (irq_n === ~((flag_A & enable_irq_A) | (flag_B & enable_irq_B)))
    else $error("irq_n mismatch with flags/enables");

  // Simple IRQ coverage
  cover property (!irq_n);
  cover property ( flag_A & enable_irq_A & !irq_n );
  cover property ( flag_B & enable_irq_B & !irq_n );
  cover property ( irq_n );
endmodule

bind jt51_timers jt51_timers_sva timers_sva_i (.*);

// Timer internal behavior checks
module jt51_timer_sva #(
  parameter int counter_width = 10,
  parameter int mult_width    = 6
)(
  input clk, rst,
  input [counter_width-1:0] start_value,
  input load, clr_flag, set_run, clr_run,
  input flag, overflow,
  // internal regs passed in via bind
  input run,
  input [counter_width-1:0] cnt,
  input [mult_width-1:0]    mult
);
  default clocking cb @(posedge clk); endclocking

  // Reset effects (explicitly checked)
  assert property (rst |=> (!flag && !run))
    else $error("flag/run not cleared by rst");

  // run control
  assert property (disable iff (rst) (clr_run |=> !run))
    else $error("run not cleared by clr_run");
  assert property (disable iff (rst) (!clr_run && (set_run || load) |=> run))
    else $error("run not set by set_run/load");
  assert property (disable iff (rst) (!clr_run && !(set_run || load) |=> $stable(run)))
    else $error("run not stable without control");

  // flag control
  assert property (disable iff (rst) (clr_flag |=> !flag))
    else $error("flag not cleared by clr_flag");
  assert property (disable iff (rst) (flag && !clr_flag |=> flag))
    else $error("flag not sticky until clear");
  // overflow sets flag next cycle unless cleared then
  assert property (disable iff (rst) (!clr_flag && overflow |=> (flag || clr_flag)))
    else $error("overflow did not set flag");

  // overflow correctness for +1 carry of {cnt,mult}
  assert property (disable iff (rst) (overflow == &{cnt, mult}))
    else $error("overflow != reduction-AND of {cnt,mult}");

  // load behavior (priority over run/overflow)
  assert property (disable iff (rst) (load |=> (cnt == start_value && mult == '0)))
    else $error("load did not initialize cnt/mult");

  // hold when not running and no load
  assert property (disable iff (rst) (!load && !run |=> $stable({cnt, mult})))
    else $error("{cnt,mult} changed while !run and !load");

  // increment behavior when running, no load
  assert property (disable iff (rst) (!load && run && !overflow |=> {cnt, mult} == $past({cnt, mult}) + 1))
    else $error("{cnt,mult} did not increment");
  // on overflow, reload init next cycle
  assert property (disable iff (rst) (!load && run && overflow |=> (cnt == start_value && mult == '0)))
    else $error("overflow did not reload init");

  // Coverage: key events
  cover property (load);
  cover property (set_run && !clr_run);
  cover property (run && overflow);
  cover property (flag);
  cover property (flag && clr_flag);
endmodule

bind jt51_timer jt51_timer_sva #(.counter_width(counter_width), .mult_width(mult_width)) timer_sva_i (
  .clk(clk), .rst(rst),
  .start_value(start_value),
  .load(load), .clr_flag(clr_flag), .set_run(set_run), .clr_run(clr_run),
  .flag(flag), .overflow(overflow),
  .run(run), .cnt(cnt), .mult(mult)
);