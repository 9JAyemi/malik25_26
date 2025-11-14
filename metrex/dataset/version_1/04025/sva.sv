// SVA for synchronous_block_ram
// Concise checks and coverage; bind into DUT to see internals (addr_reg, mem)
`ifndef SYNTHESIS
module synchronous_block_ram_sva #(parameter aw=9, dw=32) ();
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic X checks
  assert property (past_valid |-> !$isunknown({ce,we,oe,addr}));
  assert property (past_valid && we && ce |-> !$isunknown(di));

  // Address register behavior
  assert property (past_valid && ce  |-> addr_reg == $past(addr));
  assert property (past_valid && !ce |-> $stable(addr_reg));

  // doq stability and functional relation
  assert property (past_valid && !ce |-> $stable(doq));
  assert property (doq == mem[addr_reg]);  // structural equivalence

  // doq only changes when CE is asserted (addr_reg/mem can only change then)
  assert property (past_valid && (doq != $past(doq)) |-> ce);

  // Write semantics: write hits memory next cycle
  property p_write_effect;
    logic [aw-1:0] a; logic [dw-1:0] d;
    (we && ce, a=addr, d=di) |=> (mem[a] == d);
  endproperty
  assert property (past_valid |-> p_write_effect);

  // Read data semantics
  // After a write cycle, next-cycle doq must reflect the written data
  assert property (past_valid && $past(we && ce)    |-> doq == $past(di));
  // After a pure read cycle, next-cycle doq must reflect prior mem at that addr
  assert property (past_valid && $past(ce && !we)   |-> doq == $past(mem[$past(addr)]));

  // No write when !(we&&ce): selected location (prev addr_reg) unchanged
  assert property (past_valid && !$past(we && ce)   |-> mem[$past(addr_reg)] == $past(mem[$past(addr_reg)]));

  // Coverage
  cover property (past_valid && we && ce);                  // write
  cover property (past_valid && ce && !we);                 // read
  cover property (past_valid && !ce [*3]);                  // hold
  cover property (past_valid && $past(we && ce) && we && ce && addr == $past(addr)); // back-to-back write same addr
  cover property (past_valid && $past(we && ce) && ce && !we && addr == $past(addr)); // write then read same addr
endmodule

bind synchronous_block_ram synchronous_block_ram_sva #(.aw(aw), .dw(dw)) u_synchronous_block_ram_sva ();
`endif