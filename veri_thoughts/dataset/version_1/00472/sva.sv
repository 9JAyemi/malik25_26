// Interface-only SVA (bindable), covers and asserts core behavior concisely
module shift_register_sva (
  input logic        CLK,
  input logic        SHIFT_EN,
  input logic        LOAD_EN,
  input logic [3:0]  DATA_IN,
  input logic [3:0]  DATA_OUT
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff ($initstate);

  // Basic hygiene
  a_ctrl_known:       assert property (!$isunknown({LOAD_EN, SHIFT_EN}));
  a_datain_known_on_load: assert property (LOAD_EN |-> !$isunknown(DATA_IN));

  // Functional correctness
  a_load:     assert property (LOAD_EN |=> DATA_OUT == $past(DATA_IN));
  a_shift:    assert property ((SHIFT_EN && !LOAD_EN) |=> DATA_OUT == {$past(DATA_OUT)[2:0], $past(DATA_OUT)[3]});
  a_hold:     assert property ((!LOAD_EN && !SHIFT_EN) |=> DATA_OUT == $past(DATA_OUT));
  a_priority: assert property ((LOAD_EN && SHIFT_EN) |=> DATA_OUT == $past(DATA_IN)); // LOAD dominates SHIFT

  // Useful functional coverages
  c_load:          cover property (LOAD_EN);
  c_shift:         cover property (SHIFT_EN && !LOAD_EN);
  c_idle:          cover property (!LOAD_EN && !SHIFT_EN);
  c_both:          cover property (LOAD_EN && SHIFT_EN); // priority case seen
  c_wrap_msb2lsb:  cover property ((SHIFT_EN && !LOAD_EN && $past(DATA_OUT[3])) |=> DATA_OUT[0]);

endmodule

// Bind example:
// bind shift_register shift_register_sva sva_i (.*);