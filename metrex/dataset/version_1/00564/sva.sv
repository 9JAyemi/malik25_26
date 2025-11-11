// SVA checker for regfile (bind this into the DUT). Provide a sampling clk/rst_n.
module regfile_sva #(parameter int DW=8, AW=3, NREG=(1<<AW)) (input logic clk, rst_n);
  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Combinational read correctness
  ap_read1: assert property (data_out1 == regs[addr1]);
  ap_read2: assert property (data_out2 == regs[addr2]);

  // Write-through behavior and forwarding
  ap_wr_effect:     assert property (write_en |-> regs[addr1] == data_in);
  ap_wr_forward1:   assert property (write_en |-> data_out1 == data_in);
  ap_wr_forward2:   assert property (write_en && (addr2 == addr1) |-> data_out2 == data_in);

  // No unintended register modifications
  genvar i;
  generate
    for (i=0; i<NREG; i++) begin : g_reg_chk
      ap_no_spurious_when_no_write: assert property (!write_en |=> regs[i] == $past(regs[i]));
      ap_only_target_changes:       assert property (write_en && (addr1 != i) |-> regs[i] == $past(regs[i]));
    end
  endgenerate

  // data_out2 stability when writing a different address (addr2 held)
  ap_dout2_stable_other_addr: assert property (write_en && (addr2 != addr1) && $stable(addr2) |=> data_out2 == $past(data_out2));

  // X-propagation checks
  ap_x_data_out1: assert property (!$isunknown(addr1) |-> !$isunknown(data_out1));
  ap_x_data_out2: assert property (!$isunknown(addr2) |-> !$isunknown(data_out2));
  ap_x_write_dst: assert property (!$isunknown({write_en,addr1,data_in}) |-> !$isunknown(regs[addr1]));

  // Coverage
  genvar j;
  generate
    for (j=0; j<NREG; j++) begin : g_cov
      cp_write_each: cover property (write_en && addr1 == j);
    end
  endgenerate
  cp_same_addr_rw:   cover property (write_en && (addr2 == addr1));
  cp_diff_addr_rw:   cover property (addr1 != addr2);
  cp_b2b_wr_diff:    cover property (write_en ##1 (write_en && (addr1 != $past(addr1))));
endmodule

// Bind example (replace <clk> and <rst_n> with your env signals)
bind regfile regfile_sva #(.DW(8), .AW(3)) u_regfile_sva (.clk(<clk>), .rst_n(<rst_n>));