// SVA for system_auto_cc_0_rd_status_flags_as_19
// Bind into the DUT to access internal regs
module system_auto_cc_0_rd_status_flags_as_19_sva;
  // These names are resolved in the bound scope
  // m_aclk, rd_rst_reg_reg, count_d1_reg, out, ram_empty_i, ram_empty_fb_i

  default clocking cb @(posedge m_aclk); endclocking

  // 1) All three flops take value 1 on the cycle after reset is sampled high
  assert property (rd_rst_reg_reg |=> {out, ram_empty_i, ram_empty_fb_i} == 3'b111)
    else $error("Reset behavior: flops must be 1 one cycle after rd_rst_reg_reg=1");

  // 2) When not in reset, all three flops follow count_d1_reg[1] with 1-cycle latency
  assert property (!rd_rst_reg_reg |=> {out, ram_empty_i, ram_empty_fb_i} == {3{$past(count_d1_reg[1])}})
    else $error("Update behavior: flops must equal prior cycle count_d1_reg[1] when not in reset");

  // 3) The three flops must always be equal to each other
  assert property ((out === ram_empty_i) && (out === ram_empty_fb_i))
    else $error("Coherency: out, ram_empty_i, ram_empty_fb_i must be equal");

  // 4) When not in reset, the driving input bit must be known
  assert property (!rd_rst_reg_reg |-> !$isunknown(count_d1_reg[1]))
    else $error("Input X/Z: count_d1_reg[1] unknown while used");

  // 5) Independence: bit[0] must not affect outputs
  assert property (!rd_rst_reg_reg && $stable(count_d1_reg[1]) &&
                   (count_d1_reg[0] != $past(count_d1_reg[0])) |=> $stable({out, ram_empty_i, ram_empty_fb_i}))
    else $error("Functional independence: count_d1_reg[0] must not influence outputs");

  // Coverage
  cover property (rd_rst_reg_reg ##1 {out, ram_empty_i, ram_empty_fb_i} == 3'b111);
  cover property (!rd_rst_reg_reg && $rose(count_d1_reg[1]) ##1 (out && ram_empty_i && ram_empty_fb_i));
  cover property (!rd_rst_reg_reg && $fell(count_d1_reg[1]) ##1 (!out && !ram_empty_i && !ram_empty_fb_i));
endmodule

bind system_auto_cc_0_rd_status_flags_as_19 system_auto_cc_0_rd_status_flags_as_19_sva sva_i();