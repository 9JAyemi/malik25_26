// SVA for shift_register
`ifndef SHIFT_REGISTER_SVA_SV
`define SHIFT_REGISTER_SVA_SV

module shift_register_sva (
  input logic        clk,
  input logic        load,
  input logic        shift,
  input logic [3:0]  data_in,
  input logic [3:0]  data_out,
  input logic [3:0]  shift_reg
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  // Sanity/mapping
  a_map_out_to_reg:      assert property (data_out == shift_reg);
  a_no_x_ctrl:           assert property (!$isunknown({load,shift}));
  a_no_x_on_load_data:   assert property (load |-> !$isunknown(data_in));

  // Functionality
  a_load_updates:        assert property (disable iff (!past_valid)
                                          load |=> data_out == $past(data_in));

  a_shift_updates:       assert property (disable iff (!past_valid)
                                          (shift && !load) |=> data_out == {$past(data_out[2:0]), 1'b0});

  a_hold_when_idle:      assert property (disable iff (!past_valid)
                                          (!load && !shift) |=> data_out == $past(data_out));

  a_load_overrides:      assert property (disable iff (!past_valid)
                                          (load && shift) |=> data_out == $past(data_in));

  a_bit0_zero_on_shift:  assert property ((shift && !load) |=> data_out[0] == 1'b0);

  a_four_shifts_zero:    assert property (((shift && !load))[*4] |=> data_out == 4'b0000);

  a_zero_sticky_no_load: assert property ((data_out == 4'b0000 && !load) |=> data_out == 4'b0000);

  // Coverage
  c_load:                    cover property (load);
  c_shift:                   cover property (shift && !load);
  c_hold:                    cover property (!load && !shift);
  c_both_load_and_shift:     cover property (load && shift);
  c_load_then_shift4_to_0:   cover property (load && (data_in != 4'b0000)
                                             ##1 (shift && !load)[*4]
                                             ##1 (data_out == 4'b0000));
endmodule

// Bind to DUT
bind shift_register shift_register_sva shift_register_sva_i (
  .clk(clk),
  .load(load),
  .shift(shift),
  .data_in(data_in),
  .data_out(data_out),
  .shift_reg(shift_reg)
);
`endif