// SVA checker for pfpu_prog
// Bind into the DUT; accesses internals by name
module pfpu_prog_sva;

  default clocking cb @(posedge sys_clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge sys_clk) past_valid <= 1'b1;

  // Counter behavior
  assert property (count_rst |-> counter == 11'd0);
  assert property (past_valid |-> ($past(count_rst) ? (counter == 11'd0)
                                                   : (counter == $past(counter) + 11'd1)));

  // Program counter output
  assert property (pc == counter);

  // Address muxing to memory
  assert property (c_en |-> mem_a == {c_page, c_offset});
  assert property (!c_en |-> mem_a == counter);

  // Write-enable and data path to memory
  assert property (mem_we == (c_en & c_w_en));
  assert property (mem_di == c_di[24:0]);

  // Data out packing from memory
  assert property (c_do[31:25] == 7'd0);
  assert property (c_do[24:0]  == mem_do);

  // Field decoding from instruction word
  assert property ({a_addr, b_addr, opcode, w_addr} == mem_do);
  assert property ({a_addr, b_addr, opcode, w_addr} == c_do[24:0]);

  // Write then readback: write at A with D, next cycle read A (no write) returns D
  assert property (past_valid && $past(mem_we) && !mem_we &&
                   (mem_a == $past(mem_a)) |-> (mem_do == $past(mem_di)));

  // -------------------
  // Lightweight coverage
  // -------------------
  // Both access modes
  cover property (past_valid && !c_en);
  cover property (c_en && !mem_we);
  cover property (c_en && mem_we);

  // Address extremes in both modes
  cover property (c_en && {c_page, c_offset} == 11'd0);
  cover property (c_en && {c_page, c_offset} == 11'd2047);
  cover property (!c_en && counter == 11'd0);
  cover property ($past(counter) == 11'd2047 && !$past(count_rst) && counter == 11'd0);

  // Reset event
  cover property (count_rst && counter == 11'd0);

  // Non-zero decoded fields observed
  cover property ({a_addr, b_addr, opcode, w_addr} != 25'd0);

endmodule

bind pfpu_prog pfpu_prog_sva pfpu_prog_sva_i();