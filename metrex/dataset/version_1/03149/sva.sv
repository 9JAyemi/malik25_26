// SVA for shift_register
// Bind this file to the DUT
// bind shift_register shift_register_sva sva (.*);

module shift_register_sva (
  input  logic [3:0] data_in,
  input  logic       shift_en,
  input  logic       load_en,
  input  logic [3:0] data_out,
  input  logic       empty
);

  // Use shift_en as the clock; guard first cycle for $past()
  default clocking cb @(posedge shift_en); endclocking
  bit past_valid;
  always_ff @(posedge shift_en) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Combinational relationships
  ap_empty_consistent:   assert property (empty === ~|data_out);

  // Update behavior on each shift_en edge
  ap_load_update:        assert property (load_en  |-> data_out == {data_in[2:0], 1'b0});
  ap_shift_update:       assert property (!load_en |-> data_out == {$past(data_out)[2:0], 1'b0});

  // Structural invariants
  ap_lsb_zero:           assert property (1'b1 |-> data_out[0] == 1'b0);

  // Once empty, shifting keeps it empty (no load)
  ap_empty_stays_empty:  assert property (empty && !load_en |-> $stable(data_out));

  // 4 consecutive shifts (no loads) always clear the register
  ap_clear_in_4_shifts:  assert property ((!load_en)[*4] |=> data_out == 4'b0000);

  // No X/Z on key signals at update edges
  ap_ctrl_known:         assert property (!$isunknown({load_en, data_in}));
  ap_out_known:          assert property (!$isunknown({data_out, empty}));

  // Coverage
  cp_load:               cover property (load_en && (data_in[2:0] != 3'b000));
  cp_shift_nonempty:     cover property (!load_en && !$past(empty));
  cp_drop_din3_on_load:  cover property (load_en && data_in[3]); // MSB of data_in is intentionally dropped
  cp_load_then_drain:    cover property (load_en && (data_in[2:0] != 3'b000)
                                         ##1 (!load_en)[*1:4] ##1 (data_out == 4'b0000));
  cp_load_zero_keeps_empty: cover property (load_en && (data_in[2:0] == 3'b000) ##1 empty);

endmodule