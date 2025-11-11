// SVA checker for system_axi_quad_spi_shield_0_wr_status_flags_as
module system_axi_quad_spi_shield_0_wr_status_flags_as_sva
(
  input logic                     s_axi_aclk,
  input logic                     Bus_RNW_reg,
  input logic                     out,
  input logic                     p_6_in,
  input logic                     ip2Bus_WrAck_core_reg_1,
  input logic [0:0]               E,
  input logic                     \gic0.gc1.count_reg[0] ,
  input logic                     \gic0.gc1.count_d2_reg[0] ,
  input logic                     ram_full_i,
  input logic                     ram_full_fb_i,
  input logic                     ram_full_i_reg0,
  input logic                     ram_full_i_reg1,
  input logic                     ram_full_i_reg2,
  input logic [255:0]             ram [0:0]
);

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge s_axi_aclk) past_valid <= 1'b1;

  default clocking cb @(posedge s_axi_aclk); endclocking
  default disable iff (!past_valid);

  // Sanity: no X on key controls/outputs
  assert property (!$isunknown({Bus_RNW_reg, out, p_6_in, ip2Bus_WrAck_core_reg_1, E[0], \gic0.gc1.count_reg[0] }));

  // Constant output
  assert property (E[0] == 1'b0);

  // ram_full_i load/hold behavior
  assert property (Bus_RNW_reg |-> ram_full_i == $past(out));
  assert property (!Bus_RNW_reg |-> ram_full_i == $past(ram_full_i));

  // Feedback generation
  assert property (Bus_RNW_reg |-> ram_full_fb_i == 1'b0);
  assert property (!Bus_RNW_reg |-> ram_full_fb_i == $past(ram_full_i));

  // 3-stage shift chain
  assert property (ram_full_i_reg0 == $past(ram_full_fb_i));
  assert property (ram_full_i_reg1 == $past(ram_full_i_reg0));
  assert property (ram_full_i_reg2 == $past(ram_full_i_reg1));

  // Output mapping
  assert property (\gic0.gc1.count_reg[0]  == ram_full_i_reg2);

  // RAM write side-effects
  assert property (p_6_in |=> ram[0][$past(ip2Bus_WrAck_core_reg_1)] == 1'b1);
  assert property (!p_6_in |=> ram[0] === $past(ram[0]));

  // Key functional covers
  cover property (Bus_RNW_reg ##1 !Bus_RNW_reg); // exercise both branches

  // Propagation: capture out=1, then drive output to 1 after pipeline delay
  cover property (Bus_RNW_reg && out ##1 !Bus_RNW_reg ##3 \gic0.gc1.count_reg[0] );

  // Propagation: capture out=0, then drive output to 0 after pipeline delay
  cover property (Bus_RNW_reg && !out ##1 !Bus_RNW_reg ##3 !\gic0.gc1.count_reg[0] );

  // Exercise both RAM bit indices
  cover property (p_6_in && !ip2Bus_WrAck_core_reg_1);
  cover property (p_6_in &&  ip2Bus_WrAck_core_reg_1);

  // Output edges observed
  cover property ($rose(\gic0.gc1.count_reg[0] ));
  cover property ($fell(\gic0.gc1.count_reg[0] ));

endmodule

// Bind into DUT
bind system_axi_quad_spi_shield_0_wr_status_flags_as
  system_axi_quad_spi_shield_0_wr_status_flags_as_sva i_wr_status_flags_as_sva
  (
    .s_axi_aclk(s_axi_aclk),
    .Bus_RNW_reg(Bus_RNW_reg),
    .out(out),
    .p_6_in(p_6_in),
    .ip2Bus_WrAck_core_reg_1(ip2Bus_WrAck_core_reg_1),
    .E(E),
    .\gic0.gc1.count_reg[0] (\gic0.gc1.count_reg[0] ),
    .\gic0.gc1.count_d2_reg[0] (\gic0.gc1.count_d2_reg[0] ),
    .ram_full_i(ram_full_i),
    .ram_full_fb_i(ram_full_fb_i),
    .ram_full_i_reg0(ram_full_i_reg0),
    .ram_full_i_reg1(ram_full_i_reg1),
    .ram_full_i_reg2(ram_full_i_reg2),
    .ram(ram)
  );