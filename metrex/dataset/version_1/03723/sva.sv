// Bind this SVA module to rj_memory:
// bind rj_memory rj_memory_sva sva_inst();

module rj_memory_sva;
  // Access DUT signals directly via bind scope
  // DUT signals: wr_en, rd_en, Sclk, rj_wr_addr, rj_rd_addr, data_in, rj_data, rj_mem

  // Lightweight reference model (scoreboard) to validate read behavior
  logic [15:0] ref_mem   [0:15];
  logic [15:0] wrote_mask;

  initial begin
    wrote_mask = '0;
    // ref_mem content is don't-care until written; no init needed
  end

  // Update reference model on writes (at negedge like DUT)
  always @(negedge Sclk) begin
    if (wr_en && !$isunknown({rj_wr_addr, data_in})) begin
      ref_mem[rj_wr_addr]  <= data_in;
      wrote_mask[rj_wr_addr] <= 1'b1;
    end
  end

  // Basic X checks
  assert property (@(negedge Sclk) !$isunknown(wr_en))
    else $error("wr_en X/Z at negedge");
  assert property (@(posedge Sclk or negedge Sclk) !$isunknown(rd_en))
    else $error("rd_en X/Z");
  assert property (@(negedge Sclk) wr_en |-> !$isunknown({rj_wr_addr, data_in}))
    else $error("X/Z on write address/data when wr_en");
  assert property (@(posedge Sclk or negedge Sclk) rd_en |-> !$isunknown(rj_rd_addr))
    else $error("X/Z on read address when rd_en");

  // WRITE: correct update on next negedge (safe from delta races)
  assert property (@(negedge Sclk)
                   wr_en && !$isunknown({rj_wr_addr, data_in})
                   |=> rj_mem[$past(rj_wr_addr)] == $past(data_in))
    else $error("Memory write did not take effect on next negedge");

  // WRITE: no unintended writes
  genvar a;
  generate
    for (a=0; a<16; a++) begin : g_hold
      assert property (@(negedge Sclk) !wr_en |=> $stable(rj_mem[a]))
        else $error("Memory changed with wr_en=0 at address %0d", a);
      assert property (@(negedge Sclk) wr_en && (rj_wr_addr != a) |=> $stable(rj_mem[a]))
        else $error("Memory changed at non-target address %0d", a);
    end
  endgenerate

  // READ: disabled read drives zero
  assert property (@(posedge Sclk or negedge Sclk) !rd_en |-> rj_data == 16'd0)
    else $error("rj_data not zero when rd_en=0");

  // READ: data matches model when address has been written
  assert property (@(posedge Sclk or negedge Sclk)
                   rd_en && !$isunknown(rj_rd_addr) && wrote_mask[rj_rd_addr]
                   |-> rj_data == ref_mem[rj_rd_addr])
    else $error("rj_data mismatch vs reference model");

  // READ: data not X when reading a known-written address
  assert property (@(posedge Sclk or negedge Sclk)
                   rd_en && !$isunknown(rj_rd_addr) && wrote_mask[rj_rd_addr]
                   |-> !$isunknown(rj_data))
    else $error("rj_data X/Z on valid read");

  // READ-WRITE same address in same cycle: output should reflect new data immediately
  assert property (@(negedge Sclk)
                   wr_en && rd_en && !$isunknown({rj_wr_addr, rj_rd_addr, data_in}) &&
                   (rj_wr_addr == rj_rd_addr)
                   |-> ##0 (rj_data === data_in))
    else $error("Read-during-write (same addr) did not return newly written data");

  // ------------- Coverage -------------
  // Basic write/read activity
  cover property (@(negedge Sclk) wr_en);
  cover property (@(posedge Sclk or negedge Sclk) rd_en);

  // Per-address write coverage
  generate
    for (a=0; a<16; a++) begin : g_cov_addr
      cover property (@(negedge Sclk) wr_en && (rj_wr_addr == a));
      cover property (@(posedge Sclk or negedge Sclk) rd_en && (rj_rd_addr == a));
    end
  endgenerate

  // Corner cases
  cover property (@(negedge Sclk) wr_en && rd_en && (rj_wr_addr == rj_rd_addr));              // RW same address
  cover property (@(negedge Sclk) wr_en ##1 wr_en && ($past(rj_wr_addr) == rj_wr_addr));      // back-to-back write same addr
  cover property (@(negedge Sclk) wr_en ##1 rd_en && (rj_rd_addr == $past(rj_wr_addr)));      // read-after-write next cycle

endmodule