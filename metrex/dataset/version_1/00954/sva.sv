// SVA for rotator_nand_gate
// Bindable, concise, and focused on functional checking and coverage.

module rotator_nand_gate_sva (
  input logic         clk,
  input logic         reset,
  input logic         load,
  input logic [1:0]   ena,
  input logic [49:0]  data,
  input logic [49:0]  q,
  input logic [49:0]  shift_reg,
  input logic [1:0]   state
);

  // Default clocking and disable
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Asynchronous reset effect (override default disable)
  a_reset_drives_known: assert property (@(posedge clk) disable iff (1'b0)
    reset |-> (state == 2'b00 && shift_reg == 50'b0));

  // State coding is legal (no 2'b11)
  a_state_legal: assert property (state inside {2'b00,2'b01,2'b10});

  // No X/Z on key state/outputs after reset deasserted
  a_no_x: assert property (!$isunknown({state, shift_reg, q}));

  // q mirrors shift_reg combinationally (sampled on clk)
  a_q_equals_shift_reg: assert property (q == shift_reg);

  // Load has priority: captures data and goes idle
  a_load_capture: assert property (load |=> (shift_reg == data && state == 2'b00));

  // Idle behavior: hold data; next-state depends on ena
  a_idle_hold:       assert property ((state == 2'b00 && !load) |=> shift_reg == $past(shift_reg));
  a_idle_to_left:    assert property ((state == 2'b00 && !load && ena == 2'b01) |=> state == 2'b01);
  a_idle_to_right:   assert property ((state == 2'b00 && !load && ena == 2'b10) |=> state == 2'b10);
  a_idle_stay:       assert property ((state == 2'b00 && !load && !(ena inside {2'b01,2'b10})) |=> state == 2'b00);

  // Rotate-left behavior: update and next-state rules
  a_rl_update: assert property ((state == 2'b01 && !load) |=> 
    shift_reg == { $past(shift_reg)[48:0], $past(shift_reg)[49] });
  a_rl_to_idle: assert property ((state == 2'b01 && !load && ena == 2'b00) |=> state == 2'b00);
  a_rl_stay:    assert property ((state == 2'b01 && !load && ena != 2'b00) |=> state == 2'b01);

  // Rotate-right behavior: update and next-state rules
  a_rr_update: assert property ((state == 2'b10 && !load) |=> 
    shift_reg == { $past(shift_reg)[0], $past(shift_reg)[49:1] });
  a_rr_to_idle: assert property ((state == 2'b10 && !load && ena == 2'b00) |=> state == 2'b00);
  a_rr_stay:    assert property ((state == 2'b10 && !load && ena != 2'b00) |=> state == 2'b10);

  // Coverage: exercise key flows and corner-cases
  c_load_left_idle:  cover property (load ##1 (state==2'b00 && ena==2'b01) ##1 state==2'b01 ##1
                                     (ena==2'b00) ##1 state==2'b00);
  c_load_right_idle: cover property (load ##1 (state==2'b00 && ena==2'b10) ##1 state==2'b10 ##1
                                     (ena==2'b00) ##1 state==2'b00);
  c_idle_ena_11_holds: cover property ((state==2'b00 && !load && ena==2'b11) ##1 state==2'b00);
  c_left_ignore_right_req:  cover property ((state==2'b01 && !load && ena==2'b10) ##1 state==2'b01);
  c_right_ignore_left_req:  cover property ((state==2'b10 && !load && ena==2'b01) ##1 state==2'b10);
  c_left_wrap_bit:   cover property ((state==2'b01 && !load) |=> (q[0] == $past(q[49])));
  c_right_wrap_bit:  cover property ((state==2'b10 && !load) |=> (q[49] == $past(q[0])));

endmodule

// Bind to DUT (example)
// Place this in a package or a testbench file after DUT is compiled.
bind rotator_nand_gate rotator_nand_gate_sva i_rotator_nand_gate_sva (
  .clk(clk),
  .reset(reset),
  .load(load),
  .ena(ena),
  .data(data),
  .q(q),
  .shift_reg(shift_reg),
  .state(state)
);