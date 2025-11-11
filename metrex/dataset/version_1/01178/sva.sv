// SVA for timer. Bind this module to the DUT instance(s).

module timer_sva #(
  parameter int W = 32,
  parameter logic [1:0] IDLE    = 2'b00,
  parameter logic [1:0] RUNNING = 2'b01,
  parameter logic [1:0] STOPPED = 2'b10
) (
  input  logic            clk,
  input  logic            rst,
  input  logic            start,
  input  logic            stop,
  input  logic            reset,
  input  logic            load,
  input  logic [W-1:0]    value,
  input  logic            interrupt,

  // internal DUT signals
  input  logic [W-1:0]    counter,
  input  logic [W-1:0]    load_value,
  input  logic [1:0]      state,
  input  logic            interrupt_reg
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Sanity
  assert property (state inside {IDLE, RUNNING, STOPPED});
  assert property (!$isunknown({state, counter, interrupt_reg}));
  assert property (interrupt == interrupt_reg);

  // Synchronous reset behavior
  assert property (rst |=> state == IDLE && counter == '0 && interrupt_reg == 1'b0);

  // IDLE: counter loads from value each cycle
  assert property ($past(state) == IDLE |-> counter == $past(value));

  // IDLE: start moves to RUNNING unless load is asserted (load has priority)
  assert property ($past(state) == IDLE && $past(start) && !$past(load) |-> state == RUNNING && counter == $past(value));
  assert property ($past(state) == IDLE && $past(load) |-> state == IDLE);

  // load_value updates only when load; captures value
  assert property ( load |-> load_value == value );
  assert property (!load |-> load_value == $past(load_value));

  // RUNNING: normal decrement when not stopped and counter > 0
  assert property ($past(state) == RUNNING && !$past(stop) && $past(counter) > 0
                   |-> state == RUNNING && counter == $past(counter) - 1);

  // RUNNING: stop takes priority and holds counter
  assert property ($past(state) == RUNNING && $past(stop)
                   |-> state == STOPPED && counter == $past(counter));

  // RUNNING: timeout (counter==0 and not stopped) -> interrupt rises and go IDLE
  assert property ($past(state) == RUNNING && !$past(stop) && $past(counter) == 0
                   |-> state == IDLE && $rose(interrupt));

  // Interrupt can only rise on timeout from RUNNING (no spurious rises)
  assert property ($rose(interrupt) |-> $past(state) == RUNNING && !$past(stop) && $past(counter) == 0);

  // STOPPED: hold when no start/reset
  assert property ($past(state) == STOPPED && !$past(start) && !$past(reset)
                   |-> state == STOPPED && counter == $past(counter));

  // STOPPED: start resumes RUNNING without changing counter
  assert property ($past(state) == STOPPED && $past(start) && !$past(reset)
                   |-> state == RUNNING && counter == $past(counter));

  // STOPPED: reset goes to IDLE and zeroes counter
  assert property ($past(state) == STOPPED && $past(reset)
                   |-> state == IDLE && counter == '0);

  // Next-state reachability constraints (no illegal transitions)
  assert property ($past(state) == IDLE    |-> state inside {IDLE, RUNNING});
  assert property ($past(state) == RUNNING |-> state inside {RUNNING, STOPPED, IDLE});
  assert property ($past(state) == STOPPED |-> state inside {STOPPED, RUNNING, IDLE});

  // Coverage

  // Basic run-to-timeout (value > 0)
  cover property (state == IDLE && !load && start && value > 0
                  ##1 state == RUNNING ##[1:$] $rose(interrupt));

  // Immediate timeout when starting with value == 0 (no stop)
  cover property (state == IDLE && !load && start && value == 0
                  ##1 !stop ##1 $rose(interrupt));

  // Stop/resume path
  cover property (state == RUNNING ##1 stop ##1 state == STOPPED ##1 start ##1 state == RUNNING);

  // Reset from STOPPED back to IDLE
  cover property (state == RUNNING ##1 stop ##1 state == STOPPED ##1 reset ##1 state == IDLE);

  // load has priority over start in IDLE
  cover property (state == IDLE && load && start ##1 state == IDLE);

  // stop beats zero on the first RUNNING cycle (value==0 + stop)
  cover property (state == IDLE && value == 0 ##1 start ##1 state == RUNNING && stop ##1 state == STOPPED && !$rose(interrupt));

endmodule

// Bind example (place in a pkg or a separate file compiled after the DUT)
bind timer timer_sva #(.W(32), .IDLE(IDLE), .RUNNING(RUNNING), .STOPPED(STOPPED)) u_timer_sva (
  .clk(clk), .rst(rst), .start(start), .stop(stop), .reset(reset), .load(load), .value(value), .interrupt(interrupt),
  .counter(counter), .load_value(load_value), .state(state), .interrupt_reg(interrupt_reg)
);