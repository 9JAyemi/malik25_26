// SVA for top_module and submodules. Bind these into the design.

/////////////////////////////////////////////
// Top-level assertions (bind to top_module)
/////////////////////////////////////////////
module top_module_sva;
  // Use top_module scope signals directly
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Structural/glue checks
  // q is pure concat of adder and rotator
  assert property (q == {adder_out, rotator_out});

  // Adder correctness (also checks cout consistency)
  assert property ({cout, adder_out} == a + b + cin);

  // Known-value checks (post-reset)
  assert property (!$isunknown({q, adder_out, rotator_out, cout, shift_en, q_adder, q_rotator, shift_reg})));

  // shift_en capture from ena
  assert property (shift_en == $past(ena));

  // q_adder pipe behavior
  assert property (q_adder == $past(adder_out));

  // q_rotator behavior
  // load takes precedence
  assert property ($past(!reset && load) |-> (q_rotator == $past(data)));
  // shift right
  assert property ($past(!reset && !load && (shift_en == 2'b01))
                   |-> (q_rotator == { $past(shift_reg)[0],  $past(shift_reg)[99:1]}));
  // shift left
  assert property ($past(!reset && !load && (shift_en == 2'b10))
                   |-> (q_rotator == { $past(shift_reg)[98:0], $past(shift_reg)[99]}));
  // else: mirror rotator_out
  assert property ($past(!reset && !load && (shift_en == 2'b00))
                   |-> (q_rotator == $past(rotator_out)));

  // Asynchronous reset effect visible at assertion event
  assert property (@(posedge reset) (shift_en == 2'b00 && q_adder == '0 && q_rotator == '0));

  // Coverage
  cover property (@(posedge reset) 1); // reset observed
  cover property (disable iff (reset) (ena == 2'b01));
  cover property (disable iff (reset) (ena == 2'b10));
  cover property (disable iff (reset) (ena == 2'b11)); // corner mode
  cover property (disable iff (reset) (load ##1 !load && (shift_en == 2'b01) ##1 (shift_en == 2'b10)));
  cover property (disable iff (reset) ({cout,adder_out} == a + b + cin && cout)); // carry-out set
  cover property (disable iff (reset) ({cout,adder_out} == a + b + cin && !cout)); // carry-out clear
endmodule

bind top_module top_module_sva();


/////////////////////////////////////////////
// rotator_module assertions
/////////////////////////////////////////////
module rotator_module_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Known-value check
  assert property (!$isunknown({q, ena, data, shift_reg, shift_en})));

  // Hold when no load and no shift
  assert property (!load && (shift_en == 2'b00) |=> q == $past(q));

  // Load
  assert property ($past(!reset && load) |-> (q == $past(data)));

  // Shift right
  assert property ($past(!reset && !load && (shift_en == 2'b01))
                   |-> (q == { $past(shift_reg)[0],  $past(data)[99:1]}));

  // Shift left
  assert property ($past(!reset && !load && (shift_en == 2'b10))
                   |-> (q == { $past(data)[98:0], $past(shift_reg)[99]}));

  // 2'b11 behaves like "update with data"
  assert property ($past(!reset && !load && (shift_en == 2'b11))
                   |-> (q == $past(data)));

  // Async reset drives q to 0
  assert property (@(posedge reset) q == '0);

  // Coverage
  cover property (disable iff (reset) (load));
  cover property (disable iff (reset) (!load && (shift_en == 2'b01)));
  cover property (disable iff (reset) (!load && (shift_en == 2'b10)));
  cover property (disable iff (reset) (!load && (shift_en == 2'b11)));
endmodule

bind rotator_module rotator_module_sva();


/////////////////////////////////////////////
// shift_reg_module assertions
/////////////////////////////////////////////
module shift_reg_module_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Known-value check
  assert property (!$isunknown({shift_reg, shift_en, data})));

  // Load
  assert property ($past(!reset && load) |-> (shift_reg == $past(data)));

  // Shift right
  assert property ($past(!reset && !load && (shift_en == 2'b01))
                   |-> (shift_reg == { $past(shift_reg)[0],  $past(shift_reg)[99:1]}));

  // Shift left
  assert property ($past(!reset && !load && (shift_en == 2'b10))
                   |-> (shift_reg == { $past(shift_reg)[98:0], $past(shift_reg)[99]}));

  // Hold
  assert property ($past(!reset && !load && (shift_en == 2'b00))
                   |-> (shift_reg == $past(shift_reg)));

  // Async reset drives shift_reg to 0
  assert property (@(posedge reset) shift_reg == '0);

  // Coverage
  cover property (disable iff (reset) (load));
  cover property (disable iff (reset) ((shift_en == 2'b01)));
  cover property (disable iff (reset) ((shift_en == 2'b10)));
endmodule

bind shift_reg_module shift_reg_module_sva();