// SVA for regfile
// Bind this file to the DUT with the bind statement at the end.

module regfile_sva;
  // This module is bound into regfile's scope; it can see its signals/array.
  default clocking cb @(posedge clk); endclocking

  // Basic sanity: controls/addresses not X; write data not X when used
  a_no_x_ctrls: assert property (!$isunknown({resetn, RegWrite, regA, regB, regW, regTEST}));
  a_no_x_wdat:  assert property ((!resetn && RegWrite && (regW!=5'd0)) |-> !$isunknown(Wdat));

  // Combinational read correctness (post-sequential updates)
  a_readA_comb: assert property (1'b1 |-> ##0 (Adat    == regfile[regA]));
  a_readB_comb: assert property (1'b1 |-> ##0 (Bdat    == regfile[regB]));
  a_readT_comb: assert property (1'b1 |-> ##0 (TESTdat == regfile[regTEST]));

  // Zero register is hard-wired to 0 at all times
  a_x0_always_zero: assert property (1'b1 |-> ##0 (regfile[0] == 32'h0));

  // Reset behavior: when resetn is 1 on a clock, all entries become 0 after that edge
  genvar ri;
  generate
    for (ri = 0; ri < 32; ri++) begin : G_RST_ZERO
      a_reset_clears_all: assert property (resetn |-> ##0 (regfile[ri] == 32'h0));
    end
  endgenerate

  // Write behavior (when not in reset):
  // - Selected entry is updated with Wdat (or 0 if regW==0) after the edge
  a_write_updates_selected: assert property ((!resetn && RegWrite)
                                            |-> ##0 (regfile[regW] == ((regW==5'd0) ? 32'h0 : Wdat)));

  // - Non-selected entries do not change on a write
  generate
    for (ri = 0; ri < 32; ri++) begin : G_WRITE_PRESERVE_OTHERS
      a_preserve_others: assert property ((!resetn && RegWrite && (regW != ri))
                                          |-> ##0 (regfile[ri] == $past(regfile[ri])));
    end
  endgenerate

  // - No write: array stable (when not in reset)
  generate
    for (ri = 0; ri < 32; ri++) begin : G_NO_WRITE_STABLE
      a_no_spurious_updates: assert property ((!resetn && !RegWrite)
                                              |-> ##0 (regfile[ri] == $past(regfile[ri])));
    end
  endgenerate

  // Coverage
  // - See a reset
  c_reset:              cover property (resetn);
  // - Any write when not in reset
  c_write:              cover property (!resetn && RegWrite);
  // - Attempted write to x0
  c_write_x0:           cover property (!resetn && RegWrite && (regW==5'd0));
  // - Write to each register at least once
  generate
    for (ri = 0; ri < 32; ri++) begin : G_COV_WR_EACH
      c_write_each: cover property (!resetn && RegWrite && (regW==ri));
    end
  endgenerate
  // - RAW same-cycle on each read port (excluding x0)
  c_raw_A: cover property (!resetn && RegWrite && (regW==regA) && (regW!=5'd0));
  c_raw_B: cover property (!resetn && RegWrite && (regW==regB) && (regW!=5'd0));
  c_raw_T: cover property (!resetn && RegWrite && (regW==regTEST) && (regW!=5'd0));
endmodule

bind regfile regfile_sva u_regfile_sva();