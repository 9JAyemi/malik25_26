// SystemVerilog Assertions for prefetch
// Concise, high-coverage checks focused on protocol, state updates, and data/flag semantics.
// Bind these to the DUT (uses hierarchical port to access internal "invalid").

module prefetch_sva (prefetch dut);

  default clocking cb @(posedge dut.i_clk); endclocking
  default disable iff (dut.i_rst);

  // Basic invariants and wiring
  assert property (cb dut.o_wb_we   == 1'b0);
  assert property (cb dut.o_wb_data == 32'h0000);
  assert property (cb dut.o_pc == dut.o_wb_addr);

  // Wishbone-lite protocol
  assert property (cb dut.o_wb_stb |-> dut.o_wb_cyc);
  assert property (cb dut.i_wb_ack |-> dut.o_wb_cyc);
  assert property (cb dut.i_wb_err |-> dut.o_wb_cyc);
  assert property (cb !(dut.i_wb_ack && dut.i_wb_err)); // no simultaneous ack+err
  assert property (@(posedge dut.i_clk) $rose(dut.o_wb_cyc) |-> dut.o_wb_stb);

  // Cycle control: drop on ack/err/reset; start when allowed
  assert property (@(posedge dut.i_clk)
                   $past(dut.i_rst || dut.i_wb_ack || dut.i_wb_err)
                   |-> (!dut.o_wb_cyc && !dut.o_wb_stb));
  assert property (cb $past(!dut.o_wb_cyc && (dut.i_stalled_n || !dut.o_valid || dut.i_new_pc) && !dut.i_rst)
                      |-> (dut.o_wb_cyc && dut.o_wb_stb));

  // Strobe behavior vs stall
  assert property (cb (dut.o_wb_cyc && dut.i_wb_stall) |-> dut.o_wb_stb);
  assert property (cb $past(dut.o_wb_cyc && !dut.i_wb_stall) |-> !dut.o_wb_stb);

  // Address sequencing
  assert property (cb $past(dut.i_new_pc) |-> (dut.o_wb_addr == $past(dut.i_pc)));
  assert property (cb $past(!dut.o_wb_cyc && dut.i_stalled_n && !dut.invalid && !dut.i_new_pc)
                      |-> (dut.o_wb_addr == $past(dut.o_wb_addr)+1));
  assert property (cb $past(dut.o_wb_cyc && !dut.i_new_pc)
                      |-> (dut.o_wb_addr == $past(dut.o_wb_addr)));

  // invalid flag semantics
  assert property (cb dut.invalid |-> dut.o_wb_cyc);
  assert property (@(posedge dut.i_clk) $past(!dut.o_wb_cyc) |-> (dut.invalid == 1'b0));
  assert property (cb $past(dut.o_wb_cyc && (dut.i_new_pc || dut.i_clear_cache)) |-> dut.invalid);

  // Instruction capture
  assert property (cb $past(dut.o_wb_cyc && dut.i_wb_ack) |-> (dut.o_i == $past(dut.i_wb_data)));
  assert property (cb $past(!(dut.o_wb_cyc && dut.i_wb_ack)) |-> $stable(dut.o_i));

  // Output flags (valid/illegal)
  assert property (@(posedge dut.i_clk) $past(dut.i_rst || dut.i_new_pc) |-> (dut.o_valid==0 && dut.o_illegal==0));
  assert property (cb $past(dut.o_wb_cyc && (dut.i_wb_ack || dut.i_wb_err) && !dut.i_rst && !dut.i_new_pc)
                      |-> (dut.o_valid == !$past(dut.invalid) &&
                           dut.o_illegal == ($past(dut.i_wb_err) && !$past(dut.invalid))));
  assert property (cb $past((dut.i_stalled_n || dut.i_clear_cache || dut.i_new_pc) &&
                            !(dut.o_wb_cyc && (dut.i_wb_ack || dut.i_wb_err)) && !dut.i_rst)
                      |-> (dut.o_valid==0 && dut.o_illegal==0));
  assert property (cb dut.o_illegal |-> dut.o_valid);

  // Coverage
  cover property (cb
    $rose(dut.o_wb_cyc)
    ##[1:5] (dut.o_wb_cyc && dut.i_wb_stall)[*1:3]
    ##1 (dut.o_wb_cyc && !dut.i_wb_stall)
    ##1 dut.i_wb_ack ##1 (dut.o_valid && !dut.o_illegal));

  cover property (cb
    $rose(dut.o_wb_cyc) ##[1:5] dut.i_wb_err ##1 (dut.o_illegal && dut.o_valid));

  cover property (cb
    $rose(dut.o_wb_cyc) ##[1:5] (dut.i_clear_cache || dut.i_new_pc)
    ##1 dut.invalid ##[1:5] dut.i_wb_ack ##1 (!dut.o_valid));

  cover property (cb
    !dut.o_wb_cyc && dut.i_stalled_n && !dut.invalid && !dut.i_new_pc
    ##1 (dut.o_wb_addr == $past(dut.o_wb_addr)+1));

endmodule

// Bind into the DUT
bind prefetch prefetch_sva sva_i();