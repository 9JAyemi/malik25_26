// SVA for fifo_async_4bit_wr_logic
// Bind into the DUT; concise, high-signal-coverage checks and key covers.

module fifo_async_4bit_wr_logic_sva (fifo_async_4bit_wr_logic dut);

  default clocking cb @(posedge dut.wr_clk); endclocking
  // Disable checks during synchronous reset; explicit reset-effect assertions below
  default disable iff (dut.rst_d2);

  // ----------------------
  // Reset effects (rst_d2 and I3)
  // ----------------------
  // Synchronous reset port
  assert property (dut.rst_d2 |=> dut.count==3'd0 && dut.wr_ptr==3'd0 && dut.rd_ptr==3'd0
                              && dut.full==1'b0 && dut.prog_full==1'b0 && dut.empty==1'b1);

  // In-module synchronous reset I3
  assert property ($past(dut.I3) |-> dut.count==3'd0 && dut.wr_ptr==3'd0 && dut.rd_ptr==3'd0
                               && dut.full==1'b0 && dut.prog_full==1'b0 && dut.empty==1'b1);

  // ----------------------
  // Output mapping/comb relationships
  // ----------------------
  assert property (dut.Q == dut.count);
  assert property (dut.O2 == {dut.count[2], dut.count[1], 1'b0});
  assert property (dut.E[0] == dut.empty);
  // Data output must reflect current rd_ptr contents
  assert property (dut.O3 == dut.ram[dut.rd_ptr]);

  // ----------------------
  // Write path (wr_en && !full)
  // ----------------------
  // wr_ptr advances by +1 modulo 8 on accepted write
  assert property ($past(dut.wr_en && !dut.full)
                   |-> dut.wr_ptr == (($past(dut.wr_ptr)+3'd1) & 3'd7));
  // No wr_ptr movement when write attempted while full
  assert property ($past(dut.wr_en && dut.full)
                   |-> dut.wr_ptr == $past(dut.wr_ptr));
  // Memory write: last cycle's write data stored at last cycle's wr_ptr
  assert property ($past(dut.wr_en && !dut.full)
                   |-> dut.ram[$past(dut.wr_ptr)] == $past(dut.O1));

  // ----------------------
  // Read path (I2 && !empty)
  // ----------------------
  // rd_ptr advances by +1 modulo 8 on accepted read
  assert property ($past(dut.I2 && !dut.empty)
                   |-> dut.rd_ptr == (($past(dut.rd_ptr)+3'd1) & 3'd7));
  // No rd_ptr movement when read attempted while empty
  assert property ($past(dut.I2 && dut.empty)
                   |-> dut.rd_ptr == $past(dut.rd_ptr));

  // ----------------------
  // Count update semantics
  // ----------------------
  // Shorthands for prior-cycle events
  function automatic bit pw; pw = $past(dut.wr_en && !dut.full); endfunction
  function automatic bit pr; pr = $past(dut.I2 && !dut.empty);  endfunction
  function automatic bit pi1; pi1 = $past(dut.I1 && !dut.full); endfunction
  function automatic bit rst_like; rst_like = $past(dut.rst_d2) || $past(dut.I3); endfunction

  // If I1 took priority last cycle: count increments by accepted write (if any)
  assert property (!rst_like() && pi1()
                   |-> dut.count == ($past(dut.count) + (pw ? 3'd1 : 3'd0)));

  // If read took effect (no I1): count = count + write(0/1) - 1
  assert property (!rst_like() && pr() && !pi1()
                   |-> dut.count == ($past(dut.count) + (pw ? 3'd1 : 3'd0) - 3'd1));

  // If neither I1 nor read: count increments by accepted write (if any)
  assert property (!rst_like() && !pi1() && !pr()
                   |-> dut.count == ($past(dut.count) + (pw ? 3'd1 : 3'd0)));

  // ----------------------
  // Flag update semantics
  // ----------------------
  // prog_full updates only when I1 branch taken
  assert property (pi1()
                   |-> dut.prog_full == (($past(dut.count) + (pw ? 3'd1 : 3'd0)) == 3'd7));
  assert property (!rst_like() && !pi1()
                   |-> dut.prog_full == $past(dut.prog_full));

  // full updates only when I1 branch taken; expression as implemented in RTL
  // Note: count is 3-bit; this condition is structurally false -> full should remain 0.
  assert property (pi1()
                   |-> dut.full == (({1'b0,$past(dut.count)} + (pw ? 4'd1 : 4'd0)) == 4'd8));
  assert property (!rst_like() && !pi1()
                   |-> dut.full == $past(dut.full));

  // empty updates only when read branch taken
  assert property (pr()
                   |-> dut.empty == (($past(dut.count) + (pw ? 3'd1 : 3'd0)) == 3'd1));
  assert property (!rst_like() && !pr()
                   |-> dut.empty == $past(dut.empty));

  // ----------------------
  // Sanity: outputs not X after reset released
  // ----------------------
  assert property (!$isunknown({dut.Q, dut.O2, dut.E, dut.O3, dut.full, dut.prog_full}));

  // ----------------------
  // Targeted covers
  // ----------------------
  // Accepted write, accepted read, and simultaneous read+write
  cover property (dut.wr_en && !dut.full);
  cover property (dut.I2 && !dut.empty);
  cover property ((dut.wr_en && !dut.full) && (dut.I2 && !dut.empty));

  // wr_ptr wrap-around on accepted writes
  cover property ($past(dut.wr_en && !dut.full) && $past(dut.wr_ptr)==3'd7 && dut.wr_ptr==3'd0);

  // prog_full assertion via I1 path
  cover property ($past(dut.I1 && !dut.full) &&
                  (($past(dut.count) + ($past(dut.wr_en && !dut.full)?3'd1:3'd0)) == 3'd7) &&
                  dut.prog_full);

  // empty assertion via read path
  cover property ($past(dut.I2 && !dut.empty) &&
                  (($past(dut.count) + ($past(dut.wr_en && !dut.full)?3'd1:3'd0)) == 3'd1) &&
                  dut.empty);

  // I3 reset observed
  cover property ($past(dut.I3) && dut.count==0 && dut.wr_ptr==0 && dut.rd_ptr==0 && dut.empty);

endmodule

bind fifo_async_4bit_wr_logic fifo_async_4bit_wr_logic_sva sva_inst(.*);