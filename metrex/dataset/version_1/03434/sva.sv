// SVA for dmem: concise, quality-focused
// Bind these assertions to the DUT (accesses internal RAM)
`ifndef DMEM_SVA
`define DMEM_SVA

module dmem_sva;
  // This module is bound into dmem's scope; unqualified names refer to dmem signals/regs

  // Clock/past guard
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Inputs sanity on write
  ap_write_inputs_known: assert property ( WE |-> (!$isunknown(A) && !$isunknown(WD)) );

  // Combinational read behavior
  ap_rd_zero_on_A0:      assert property ( (A == 32'h0) |-> (RD == 32'h0) );
  ap_rd_eq_mem_on_Ane0:  assert property ( (A != 32'h0) |-> (RD == RAM[A[7:0]]) );

  // Write updates the targeted location (1-cycle later)
  ap_write_updates_mem:  assert property ( WE |=> (RAM[$past(A)[7:0]] == $past(WD)) );

  // No unintended update to previously addressed location when !WE
  ap_no_write_when_WE0:  assert property ( !WE |=> $stable(RAM[$past(A)[7:0]]) );

  // Read-after-write (same address, nonzero address)
  ap_raw_same_addr:      assert property ( (WE && (A != 32'h0)) |=> (A == $past(A)) |-> (RD == $past(WD)) );

  // Basic coverage
  cp_read_zero:          cover property ( A == 32'h0 );
  cp_read_nonzero:       cover property ( A != 32'h0 );
  cp_write_zero_addr:    cover property ( WE && (A[7:0] == 8'h00) );
  cp_write_nonzero_addr: cover property ( WE && (A[7:0] != 8'h00) );
  cp_raw_flow:           cover property ( (WE && (A != 32'h0)) ##1 (A == $past(A)) ##0 (RD == $past(WD)) );

endmodule

bind dmem dmem_sva dmem_sva_i();

`endif