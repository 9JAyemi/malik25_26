// SVA checker for ram_rw
module ram_rw_sva (ram_rw dut);

  localparam int ADDR_W = 4;
  localparam int DATA_W = 8;
  localparam int DEPTH  = 16;

  bit started;
  initial started = 0;
  always @(posedge dut.clk) started <= 1;

  logic [DATA_W-1:0] model_mem [0:DEPTH-1];
  bit                model_val [0:DEPTH-1];

  default clocking cb @(posedge dut.clk); endclocking

  // Basic sanity (no X/Z on key controls/data when used)
  a_no_x_ctrl:            assert property (disable iff (!started) !$isunknown({dut.wen, dut.raddr, dut.waddr}));
  a_no_x_wdata_on_wen:    assert property (disable iff (!started) dut.wen |-> !$isunknown(dut.wdata));
  a_no_x_rdata_when_valid:assert property (disable iff (!started) model_val[dut.raddr] |-> !$isunknown(dut.rdata));

  // Functional: synchronous read of previous-cycle memory contents
  a_read_matches_model: assert property (disable iff (!started || !model_val[dut.raddr])
                                         dut.rdata == model_mem[dut.raddr]);

  // Same-address read-during-write uses old data; 1-cycle later readback equals written data
  a_write_readback_1cycle: assert property (disable iff (!started)
                                            dut.wen ##1 (dut.raddr == $past(dut.waddr)) |-> (dut.rdata == $past(dut.wdata)));

  // If raddr stable and no write to that address, rdata holds
  a_hold_when_no_write: assert property (disable iff (!started)
                                         $stable(dut.raddr) && !(dut.wen && (dut.waddr==dut.raddr))
                                         |-> dut.rdata == $past(dut.rdata));

  // Scoreboard to model DUT memory (learns by writes and first-time reads)
  always @(posedge dut.clk) begin
    if (dut.wen) begin
      model_mem[dut.waddr] <= dut.wdata;
      model_val[dut.waddr] <= 1'b1;
    end
    if (!model_val[dut.raddr]) begin
      model_mem[dut.raddr] <= dut.rdata;
      model_val[dut.raddr] <= 1'b1;
    end
  end

  // Functional coverage
  cover property (dut.wen);                               // any write
  cover property (dut.wen && dut.waddr==dut.raddr);       // same-cycle RAW collision
  cover property (dut.wen ##1 (dut.raddr==$past(dut.waddr)) && (dut.rdata==$past(dut.wdata))); // 1-cycle readback

  genvar ai;
  generate
    for (ai=0; ai<DEPTH; ai++) begin: C_ADDRS
      cover property (dut.wen && dut.waddr==ai);          // wrote each address
      cover property (model_val[ai] && dut.raddr==ai);     // read observed each address
    end
  endgenerate

  cover property (dut.wen && dut.wdata=='0);
  cover property (dut.wen && dut.wdata=={DATA_W{1'b1}});

endmodule

// Bind into the DUT
bind ram_rw ram_rw_sva sva_inst(.dut);