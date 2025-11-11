// SVA for MIB
// Bind these checkers to the DUT:  bind MIB MIB_sva #(.data_width(data_width), .addr_width(addr_width)) u_mib_sva();

module MIB_sva #(parameter int data_width = 32, parameter int addr_width = 8) ();
  // Assertions are bound into MIB's scope; the following names resolve in the bound instance:
  // clk, rst, addr, wr_en, wr_data, rd_en, rd_data, mem, state, burst_addr, burst_count,
  // IDLE, READ, WRITE, BURST_IDLE, BURST_READ, BURST_WRITE

  localparam int BURST_INIT = addr_width/2 - 1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Static design sanity checks
  initial begin
    assert (READ == BURST_READ && WRITE == BURST_WRITE && IDLE == BURST_IDLE)
      else $error("State encodings for BURST_* must match base states");
    assert (state inside {IDLE, READ, WRITE})
      else $error("State can only be IDLE/READ/WRITE");
    assert (BURST_INIT >= 0) else $error("BURST_INIT must be non-negative");
    assert (BURST_INIT < (1 << $bits(burst_count)))
      else $error("BURST_INIT=%0d does not fit in burst_count width=%0d", BURST_INIT, $bits(burst_count));
  end

  // X/validity checks
  assert property (!$isunknown({rd_en, wr_en, addr, wr_data, state, burst_count, burst_addr})))
    else $error("Unknown/X detected on control/data");

  // Mutual exclusion of rd and wr
  assert property (!(rd_en && wr_en)) else $error("rd_en and wr_en high simultaneously");

  // Reset behavior
  assert property (@(posedge clk) rst |=> (state == IDLE && burst_count == '0 && rd_data == '0))
    else $error("Reset did not initialize correctly");

  // State transitions (single transfer mode)
  assert property ((state == IDLE && rd_en && !wr_en) |=> state == READ)
    else $error("IDLE->READ transition failed");
  assert property ((state == IDLE && wr_en && !rd_en) |=> state == WRITE)
    else $error("IDLE->WRITE transition failed");

  assert property ((state == READ  && rd_en)  |=> state == READ)
    else $error("READ should hold while rd_en");
  assert property ((state == READ  && !rd_en) |=> state == IDLE)
    else $error("READ should return to IDLE when rd_en deasserts");

  assert property ((state == WRITE && wr_en)  |=> state == WRITE)
    else $error("WRITE should hold while wr_en");
  assert property ((state == WRITE && !wr_en) |=> state == IDLE)
    else $error("WRITE should return to IDLE when wr_en deasserts");

  // Functional data checks (single transfer mode)
  // Read: next-cycle rd_data reflects memory at prior-cycle address
  assert property ((rd_en && burst_count == 0) |=> rd_data == $past(mem[$past(addr)]))
    else $error("rd_data mismatch on read");

  // Write: memory updates at next cycle
  assert property ((wr_en && burst_count == 0) |=> mem[$past(addr)] == $past(wr_data))
    else $error("mem not updated by write");

  // Burst start behavior
  assert property ((rd_en && burst_count == 0) |=> (burst_count == BURST_INIT && burst_addr == $past(addr) + 1 && state == READ))
    else $error("Burst-read start incorrect");

  assert property ((wr_en && burst_count == 0) |=> (burst_count == BURST_INIT && burst_addr == $past(addr) + 1 && state == WRITE && mem[$past(addr)] == $past(wr_data)))
    else $error("Burst-write start incorrect");

  // In-burst step behavior (when burst_count != 0)
  // Read step: decrement count, increment address, rd_data reflects prior burst_addr
  assert property ((burst_count != 0 && rd_en) |=> (burst_count == $past(burst_count) - 1
                                                 && burst_addr == $past(burst_addr) + 1
                                                 && rd_data == $past(mem[$past(burst_addr)])))
    else $error("Burst-read step incorrect");

  // Write step: decrement count, increment address, memory writes prior burst_addr
  assert property ((burst_count != 0 && wr_en) |=> (burst_count == $past(burst_count) - 1
                                                 && burst_addr == $past(burst_addr) + 1
                                                 && mem[$past(burst_addr)] == $past(wr_data)))
    else $error("Burst-write step incorrect");

  // While in a READ-encoded state, deasserting rd_en returns to IDLE (covers BURST_READ as well)
  assert property ((state == READ && !rd_en) |=> state == IDLE)
    else $error("Deassert rd_en should return to IDLE");

  // While in a WRITE-encoded state, deasserting wr_en returns to IDLE (covers BURST_WRITE as well)
  assert property ((state == WRITE && !wr_en) |=> state == IDLE)
    else $error("Deassert wr_en should return to IDLE");

  // Optional: forbid illegal state encoding 2'b11
  assert property (state != 2'b11) else $error("Illegal state encoding 2'b11 observed");

  // Coverage
  cover property (state == IDLE && rd_en ##1 state == READ ##1 !rd_en ##1 state == IDLE);
  cover property (state == IDLE && wr_en ##1 state == WRITE ##1 !wr_en ##1 state == IDLE);

  // Cover a short burst read (start + 2 steps)
  cover property ((burst_count == 0 && rd_en)
                  ##1 (burst_count == BURST_INIT && rd_en)
                  ##1 (rd_en && burst_count == BURST_INIT-1)
                  ##1 (!rd_en && state == IDLE));

  // Cover a short burst write (start + 2 steps)
  cover property ((burst_count == 0 && wr_en)
                  ##1 (burst_count == BURST_INIT && wr_en)
                  ##1 (wr_en && burst_count == BURST_INIT-1)
                  ##1 (!wr_en && state == IDLE));
endmodule