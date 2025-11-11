// SVA for binary_multiplier_control_unit
// Bind-friendly checker focusing on state machine, outputs, and transitions

module bmc_sva
(
  input logic         clk,
  input logic         start,
  input logic         cnt_done,
  input logic         lsb,
  input logic         start_process,
  input logic         add,
  input logic         shift,
  input logic         count_up,
  input logic         done,
  input logic [2:0]   state
);
  // Mirror DUT encodings
  localparam int off=0, on=1, process=2, finish=3;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (start_process == start);
  assert property (!$isunknown(state));
  assert property (state inside {off,on,process,finish});
  assert property (!$isunknown({add,shift,count_up,done}));

  // Initial state (relies on DUT initial block)
  assert property ($past($initstate) |-> state==off);

  // Pure decode checks
  assert property (shift    == (state==process));
  assert property (count_up == (state==process));
  assert property (shift == count_up);
  assert property (done     == (state==finish));
  assert property (add      == ((state==on) && lsb));
  assert property (done |-> !shift && !count_up);

  // Next-state function (sampled on clk edges)
  assert property ($past(state==off && !start) |=> state==off);
  assert property ($past(state==off &&  start) |=> state==on);
  assert property ($past(state==on)             |=> state==process);
  assert property ($past(state==process && !cnt_done) |=> state==on);
  assert property ($past(state==process &&  cnt_done) |=> state==finish);
  assert property ($past(state==finish)        |=> state==off);

  // Output timing around transitions
  assert property ($past(state==process && cnt_done) |=> state==finish && done);
  assert property ($past(state==finish)              |=> state==off && !done);

  // Coverage
  cover property ($past(state==off && start)        |=> state==on);
  cover property ($past(state==on &&  lsb)          |=> state==process && add);
  cover property ($past(state==on && !lsb)          |=> state==process && !add);
  cover property ($past(state==process && !cnt_done)|=> state==on);
  cover property ($past(state==process &&  cnt_done)|=> state==finish && done);
  // Full-cycle cover: off -> on -> process -> finish -> off (with eventual cnt_done)
  sequence full_cycle;
    state==off && start ##1
    state==on ##1
    state==process ##[0:$] (state==process && cnt_done) ##1
    state==finish ##1
    state==off;
  endsequence
  cover property (full_cycle);

endmodule

// Bind example (instantiate per DUT instance; adjust instance path as needed):
// bind binary_multiplier_control_unit bmc_sva bmc_chk (.* , .state(state));