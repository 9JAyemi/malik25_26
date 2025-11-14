// SVA for r_DEVICE_CAPABILITIES_1_HIGH
module r_DEVICE_CAPABILITIES_1_HIGH_sva(
  input logic        clk,
  input logic        reset,
  input logic        wenb,
  input logic [7:0]  in_data,
  input logic [7:0]  reg_0x25
);
  default clocking cb @(posedge clk); endclocking

  // Reset clears
  a_25_reset: assert property (reset |=> reg_0x25 == 8'h00);

  // Write on !wenb
  a_25_write: assert property (disable iff (reset) (!wenb) |=> reg_0x25 == $past(in_data));

  // Hold on wenb
  a_25_hold:  assert property (disable iff (reset) (wenb)  |=> reg_0x25 == $past(reg_0x25));

  // Changes only when allowed
  a_25_change_en: assert property ((reg_0x25 != $past(reg_0x25)) |-> $past(reset) || !$past(wenb));

  // Coverage
  c_25_write:       cover property (disable iff (reset) !wenb);
  c_25_b2b_writes:  cover property (disable iff (reset) (!wenb ##1 !wenb));
  c_25_hold_2cyc:   cover property (disable iff (reset) (wenb ##1 wenb));
endmodule

// SVA for r_DEVICE_CAPABILITIES_2_HIGH
module r_DEVICE_CAPABILITIES_2_HIGH_sva(
  input logic        clk,
  input logic        reset,
  input logic        wenb,
  input logic        select,
  input logic [7:0]  in_data,
  input logic [7:0]  reg_0x25,
  input logic [7:0]  reg_0x2A
);
  default clocking cb @(posedge clk); endclocking

  // Reset clears
  a_2A_reset: assert property (reset |=> reg_0x2A == 8'h00);

  // Source select on write
  a_2A_write_sel0: assert property (disable iff (reset) (!wenb && !select) |=> reg_0x2A == $past(in_data));
  a_2A_write_sel1: assert property (disable iff (reset) (!wenb &&  select) |=> reg_0x2A == $past(reg_0x25));

  // Hold on wenb
  a_2A_hold:  assert property (disable iff (reset) (wenb) |=> reg_0x2A == $past(reg_0x2A));

  // Changes only when allowed
  a_2A_change_en: assert property ((reg_0x2A != $past(reg_0x2A)) |-> $past(reset) || !$past(wenb));

  // Submodule consistency (seen from top)
  a_25_write_seen_here: assert property (disable iff (reset) (!wenb) |=> reg_0x25 == $past(in_data));

  // Coverage: both data paths, hold, and mixed back-to-back writes
  c_2A_sel0_write:  cover property (disable iff (reset) (!wenb && !select));
  c_2A_sel1_write:  cover property (disable iff (reset) (!wenb &&  select));
  c_2A_b2b_mixed:   cover property (disable iff (reset) (!wenb && !select ##1 !wenb && select));
  c_2A_hold_2cyc:   cover property (disable iff (reset) (wenb ##1 wenb));
endmodule

// Binds
bind r_DEVICE_CAPABILITIES_1_HIGH r_DEVICE_CAPABILITIES_1_HIGH_sva u_sva_1 (
  .clk(clk), .reset(reset), .wenb(wenb), .in_data(in_data), .reg_0x25(reg_0x25)
);

bind r_DEVICE_CAPABILITIES_2_HIGH r_DEVICE_CAPABILITIES_2_HIGH_sva u_sva_2 (
  .clk(clk), .reset(reset), .wenb(wenb), .select(select),
  .in_data(in_data), .reg_0x25(reg_0x25), .reg_0x2A(reg_0x2A)
);