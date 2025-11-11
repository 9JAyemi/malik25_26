// SVA for sync_ram
// Bind this file to the DUT:  bind sync_ram sync_ram_sva sva_inst();

module sync_ram_sva;

  // Access DUT scope directly (bind into sync_ram)
  // Default clocking/reset for synchronous properties
  default clocking cb @(posedge clk); endclocking
  default disable iff (write_reset);

  localparam int DEPTH = 6;

  // -------------------------
  // Combinational correctness
  // -------------------------

  // data_reg function: per-bit write datapath
  genvar gi;
  generate
    for (gi = 0; gi < DEPTH; gi++) begin : G_DATAREG
      assert property (@(posedge clk)
        data_reg[gi] == ((waddr == gi[2:0]) ? datain : ram_q[gi]))
      else $error("data_reg[%0d] mismatch", gi);
    end
  endgenerate

  // ram_d mux to data_reg/ram_q based on we
  assert property (@(posedge clk) (we === 1'b1) |-> (ram_d == data_reg))
    else $error("ram_d not equal to data_reg when we===1");

  assert property (@(posedge clk) (we !== 1'b1) |-> (ram_d == ram_q))
    else $error("ram_d not equal to ram_q when we!==1");

  // Read datapath: dataout reflects selected ram_q (or 0 for invalid raddr)
  assert property (@(posedge clk) (raddr inside {3'd0,3'd1,3'd2,3'd3,3'd4,3'd5}) |-> (dataout == ram_q[raddr]))
    else $error("dataout != ram_q[raddr] for valid raddr");

  assert property (@(posedge clk) (raddr inside {3'd6,3'd7}) |-> (dataout == 1'b0))
    else $error("dataout not 0 for invalid raddr");

  // No write-through on same-cycle read when raddr==waddr
  assert property (@(posedge clk)
      (we === 1'b1 && (raddr == waddr) && (raddr inside {3'd0,3'd1,3'd2,3'd3,3'd4,3'd5}) &&
       ($past(ram_q[raddr]) !== datain)) |-> (dataout == $past(ram_q[raddr])))
    else $error("Unexpected write-through to dataout");

  // -------------------------
  // Reset behavior
  // -------------------------

  // Async clear: on posedge write_reset, all locations clear immediately
  assert property (@(posedge write_reset) (ram_q == 6'b0))
    else $error("ram_q not cleared on async write_reset");

  // While reset is asserted, memory remains cleared
  assert property (@(posedge clk) write_reset |-> (ram_q == 6'b0))
    else $error("ram_q changed while write_reset asserted");

  // During reset and valid raddr, dataout must be 0 (since ram_q is 0)
  assert property (@(posedge clk) write_reset && (raddr inside {3'd0,3'd1,3'd2,3'd3,3'd4,3'd5}) |-> (dataout == 1'b0))
    else $error("dataout not 0 during reset with valid raddr");

  // -------------------------
  // Sequential write semantics
  // -------------------------

  // Commit on write: after a write, exactly one addressed bit takes datain; others hold
  generate
    for (gi = 0; gi < DEPTH; gi++) begin : G_WRITE_COMMIT
      assert property (@(posedge clk)
        (we === 1'b1) |=> (ram_q[gi] == (($past(waddr) == gi[2:0]) ? $past(datain) : $past(ram_q[gi]))))
      else $error("ram_q[%0d] wrong after write", gi);
    end
  endgenerate

  // No change when not writing (we!==1 covers 0, X, Z behavior of DUT)
  assert property (@(posedge clk) (we !== 1'b1) |=> (ram_q == $past(ram_q)))
    else $error("ram_q changed without write");

  // Writes to invalid addresses (6 or 7) must not change memory
  assert property (@(posedge clk) (we === 1'b1 && (waddr inside {3'd6,3'd7})) |=> (ram_q == $past(ram_q)))
    else $error("ram_q changed on invalid waddr");

  // -------------------------
  // Coverage
  // -------------------------

  // Reset event
  cover property (@(posedge write_reset) 1);

  // Cover writes to each valid address
  generate
    for (gi = 0; gi < DEPTH; gi++) begin : G_CVR_WR
      cover property (@(posedge clk) (!write_reset && we === 1'b1 && waddr == gi[2:0]));
    end
  endgenerate

  // Write followed by readback next cycle
  cover property (@(posedge clk)
    !write_reset && we === 1'b1 ##1 (raddr == $past(waddr)) && (dataout == $past(datain)));

  // Back-to-back writes to different addresses
  cover property (@(posedge clk)
    !write_reset && we === 1'b1 && (waddr inside {3'd0,3'd1,3'd2,3'd3,3'd4,3'd5})
    ##1 !write_reset && we === 1'b1 && (waddr inside {3'd0,3'd1,3'd2,3'd3,3'd4,3'd5}) && (waddr != $past(waddr)));

endmodule