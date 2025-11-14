// SVA for limbus_cpu_cpu_nios2_oci_dtrace
// Bind this file to the DUT (bind statement at bottom)

module limbus_cpu_cpu_nios2_oci_dtrace_sva (
  input logic                 clk,
  input logic                 jrst_n,
  input logic [21:0]          cpu_d_address,
  input logic                 cpu_d_read,
  input logic [31:0]          cpu_d_readdata,
  input logic                 cpu_d_wait,
  input logic                 cpu_d_write,
  input logic [31:0]          cpu_d_writedata,
  input logic [35:0]          atm,
  input logic [35:0]          dtm,
  input logic                 dummy_tie_off
);

  default clocking cb @(posedge clk); endclocking

  // Async reset comes on negedge jrst_n
  property p_async_reset_now;
    @(negedge jrst_n) 1 |-> ##0 (atm == 36'd0 && dtm == 36'd0);
  endproperty
  assert property (p_async_reset_now);

  // While reset is low, outputs must hold at zero
  property p_hold_during_reset;
    @(posedge clk) (!jrst_n) |-> (atm == 36'd0 && dtm == 36'd0);
  endproperty
  assert property (p_hold_during_reset);

  // No X on outputs in active mode
  assert property (disable iff (!jrst_n) !$isunknown({atm,dtm}));

  // Read updates have priority; outputs reflect inputs (with zero-extension) same cycle
  assert property (disable iff (!jrst_n)
    cpu_d_read |-> ##0 (atm[21:0] == cpu_d_address &&
                        dtm[31:0] == cpu_d_readdata &&
                        atm[35:22] == '0 &&
                        dtm[35:32] == '0)
  );

  // Write updates when no read; outputs reflect inputs (with zero-extension) same cycle
  assert property (disable iff (!jrst_n)
    (cpu_d_write && !cpu_d_read) |-> ##0 (atm[21:0] == cpu_d_address &&
                                          dtm[31:0] == cpu_d_writedata &&
                                          atm[35:22] == '0 &&
                                          dtm[35:32] == '0)
  );

  // Wait clears when no read/write
  assert property (disable iff (!jrst_n)
    (cpu_d_wait && !cpu_d_read && !cpu_d_write) |-> ##0 (atm == 36'd0 && dtm == 36'd0)
  );

  // Idle holds (no activity => outputs stable)
  assert property (disable iff (!jrst_n)
    (!cpu_d_read && !cpu_d_write && !cpu_d_wait) |-> $stable({atm,dtm})
  );

  // Priority checks for overlaps
  assert property (disable iff (!jrst_n)
    (cpu_d_read && cpu_d_write) |-> ##0 (atm[21:0] == cpu_d_address &&
                                         dtm[31:0] == cpu_d_readdata)
  );

  assert property (disable iff (!jrst_n)
    (cpu_d_read && cpu_d_wait) |-> ##0 (atm[21:0] == cpu_d_address &&
                                        dtm[31:0] == cpu_d_readdata)
  );

  assert property (disable iff (!jrst_n)
    (cpu_d_write && cpu_d_wait && !cpu_d_read) |-> ##0 (atm[21:0] == cpu_d_address &&
                                                        dtm[31:0] == cpu_d_writedata)
  );

  // Tie-off correctness
  assert property (disable iff (!jrst_n)
    dummy_tie_off == (cpu_d_wait | cpu_d_read | cpu_d_write) && !$isunknown(dummy_tie_off)
  );

  // Basic functional coverage
  cover property (disable iff (!jrst_n) cpu_d_read ##0 (atm[21:0]==cpu_d_address && dtm[31:0]==cpu_d_readdata));
  cover property (disable iff (!jrst_n) cpu_d_write && !cpu_d_read ##0 (atm[21:0]==cpu_d_address && dtm[31:0]==cpu_d_writedata));
  cover property (disable iff (!jrst_n) cpu_d_wait && !cpu_d_read && !cpu_d_write ##0 (atm==36'd0 && dtm==36'd0));
  cover property (disable iff (!jrst_n) cpu_d_read && cpu_d_write); // overlap exercised
  cover property (disable iff (!jrst_n) cpu_d_read ##1 cpu_d_write ##1 cpu_d_wait); // sequence mix
  cover property (@(negedge jrst_n) 1); // reset asserted at least once

endmodule

bind limbus_cpu_cpu_nios2_oci_dtrace
  limbus_cpu_cpu_nios2_oci_dtrace_sva
  sva_i (
    .clk(clk),
    .jrst_n(jrst_n),
    .cpu_d_address(cpu_d_address),
    .cpu_d_read(cpu_d_read),
    .cpu_d_readdata(cpu_d_readdata),
    .cpu_d_wait(cpu_d_wait),
    .cpu_d_write(cpu_d_write),
    .cpu_d_writedata(cpu_d_writedata),
    .atm(atm),
    .dtm(dtm),
    .dummy_tie_off(dummy_tie_off)
  );