// SVA for system_axi_iic_0_0_filter and submodules
// Focused, bound, concise checks and coverage

// SCL debounce assertions
module sva_debounce_scl();
  // Bound into scope of system_axi_iic_0_0_debounce
  // Accesses internal regs by name via portless bind
  logic [2:0] init;
  always @(posedge s_axi_aclk) init <= {init[1:0], 1'b1};
  wire ready = init[2];

  default clocking cb @(posedge s_axi_aclk); endclocking
  default disable iff (!ready);

  // Shift register correctness
  a_scl_shift_hi: assert property (scl_rin_d1_d[1] == $past(scl_rin_d1));
  a_scl_shift_lo: assert property (scl_rin_d1_d[0] == $past(scl_rin_d1_d[1]));

  // Output register delay (2-cycle)
  a_scl_reg_delay2: assert property (scl_rin_d1_reg == $past(scl_rin_d1,2));

  // Rising-edge detect correctness and 1-cycle pulse
  a_scl_edge_fwd:  assert property ($rose(scl_rin_d1) |=> scl_rising_edge0);
  a_scl_edge_rev:  assert property (scl_rising_edge0 |-> $past(scl_rin_d1) && !$past(scl_rin_d1,2));
  a_scl_edge_1cyc: assert property (scl_rising_edge0 |=> !scl_rising_edge0);

  // Coverage
  c_scl_edge_seen:  cover property ($rose(scl_rin_d1) ##1 scl_rising_edge0);
  c_scl_pulse:      cover property (scl_rising_edge0);
  c_scl_reg_moves:  cover property (scl_rin_d1_reg != $past(scl_rin_d1_reg));
endmodule

bind system_axi_iic_0_0_debounce sva_debounce_scl asrt_scl();

// SDA debounce assertions
module sva_debounce_sda();
  // Bound into scope of system_axi_iic_0_0_debounce_3
  logic [3:0] init;
  always @(posedge s_axi_aclk) init <= {init[2:0], 1'b1};
  wire ready = init[3];

  default clocking cb @(posedge s_axi_aclk); endclocking
  default disable iff (!ready);

  // 3-deep shift correctness
  a_sda_shift_2: assert property (sda_rin_d3_d[2] == $past(sda_rin_d1));
  a_sda_shift_1: assert property (sda_rin_d3_d[1] == $past(sda_rin_d3_d[2]));
  a_sda_shift_0: assert property (sda_rin_d3_d[0] == $past(sda_rin_d3_d[1]));

  // Registered copy relationship
  a_sda_d3_follow: assert property (sda_rin_d3 == $past(sda_rin_d3_d));

  // scndry_out equals rising edge of delayed samples and is 1-cycle pulse
  a_sda_scndry_eq:   assert property (scndry_out == (sda_rin_d3[2] & ~sda_rin_d3[1]));
  a_sda_scndry_inp:  assert property (scndry_out == ($past(sda_rin_d1,2) & ~$past(sda_rin_d1,3)));
  a_sda_scndry_1cyc: assert property (scndry_out |=> !scndry_out);
  a_sda_scndry_lat:  assert property ($rose(sda_rin_d1) |=> ##2 scndry_out);

  // detect_stop_b_reg matches comparator and input history
  a_stop_eq_local: assert property (detect_stop_b_reg == (sda_rin_d3 == 3'b100));
  a_stop_eq_inp:   assert property (detect_stop_b_reg ==
                                    ($past(sda_rin_d1,2) && !$past(sda_rin_d1,3) && !$past(sda_rin_d1,4)));

  // Coverage
  c_sda_scndry: cover property (scndry_out);
  c_sda_stop:   cover property (detect_stop_b_reg);
  c_sda_pattern: cover property (sda_rin_d3 == 3'b100);
endmodule

bind system_axi_iic_0_0_debounce_3 sva_debounce_sda asrt_sda();