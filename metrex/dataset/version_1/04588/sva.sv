// SVA for crc_generator_checker
// Bind-friendly checker that references key internals and I/Os

module crc_generator_checker_sva #(
  parameter data_width = 8,
  parameter crc_width  = 16
)(
  input                    clk,
  input                    reset,
  input  [data_width-1:0]  data_in,
  input  [crc_width-1:0]   crc_in,
  input  [crc_width-1:0]   crc_out,
  input                    error,

  // Internals (matched by bind .*)
  input  [crc_width-1:0]   crc_out_int,
  input  [crc_width-1:0]   crc_in_shifted,
  input  [data_width-1:0]  data_in_shifted,
  input  [crc_width-1:0]   crc_gen_shifted,
  input  [crc_width-1:0]   crc_check_shifted,
  input                    error_temp,

  input  [crc_width-1:0]   crc_reg,
  input  [data_width-1:0]  data_reg,
  input  [crc_width-1:0]   crc_gen,
  input  [crc_width-1:0]   crc_check
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset drives flops to 0 by the next cycle
  property p_reset_to_zero;
    reset |-> ##1 (data_reg==0 && crc_check==0 && crc_gen==0 && crc_reg==0);
  endproperty
  a_reset_to_zero: assert property (p_reset_to_zero);

  // Sequential updates (one-cycle latency)
  a_data_reg_update:    assert property (!reset |-> ##1 data_reg == $past(data_in_shifted));
  a_crc_check_update:   assert property (!reset |-> ##1 crc_check == $past(crc_in_shifted));
  a_crc_gen_update:     assert property (!reset |-> ##1 crc_gen   == $past(crc_gen_shifted));
  a_crc_reg_update:     assert property (!reset |-> ##1 crc_reg   == $past(crc_gen_shifted ^ crc_in_shifted ^ data_in_shifted));

  // Combinational mappings to outputs
  a_crc_out_map:        assert property (crc_out == crc_out_int && crc_out_int == crc_reg);
  a_error_map:          assert property (error == error_temp && error_temp == (crc_check_shifted != crc_out_int));

  // No X/Z on key outputs and state after reset deasserts
  a_no_x_after_reset:   assert property (!$isunknown({crc_out, error, crc_reg, crc_check, crc_gen, data_reg,
                                                      crc_out_int, error_temp, data_in_shifted, crc_in_shifted,
                                                      crc_gen_shifted, crc_check_shifted})));

  // Optional consistency checks derived from current RTL structure
  a_crc_check_shift_passthru: assert property (crc_check_shifted == crc_check);

  // Coverage
  c_reset_seq:          cover property (reset ##1 !reset);
  c_crc_change:         cover property (!reset and $changed(crc_out));
  c_error_low:          cover property (!reset and (error==0));
  c_error_high:         cover property (!reset and (error==1));
  c_error_toggle:       cover property (!reset and (error==0) ##1 (error==1));
endmodule

// Bind into the DUT
bind crc_generator_checker
  crc_generator_checker_sva #(.data_width(data_width), .crc_width(crc_width))
  u_crc_generator_checker_sva (.*);