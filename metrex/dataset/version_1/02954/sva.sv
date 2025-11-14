// SVA for fifo4: concise, high‑value checks + coverage
// Bind this file to the DUT:  bind fifo4 fifo4_asserts u_fifo4_asserts();

module fifo4_asserts;

  // Access DUT signals directly via bind scope
  // clk, rst, clr, din, we, dout, re, full, empty
  // mem, wp, rp, wp_p1, rp_p1, gb

  // Clocking
  default clocking cb @(posedge clk); endclocking

  // 1) Reset/clear behavior (explicit, not disabled)
  // After async reset low or clr high, pointers/gb clear next cycle
  assert property (@(posedge clk) !rst |=> (wp==2'h0 && rp==2'h0 && gb==1'b0));
  assert property (@(posedge clk)  clr |=> (wp==2'h0 && rp==2'h0 && gb==1'b0));

  // Disable assertions during reset/clear for the rest
  default disable iff (!rst || clr);

  // 2) Combinational relations
  assert property (wp_p1 == wp + 2'h1);
  assert property (rp_p1 == rp + 2'h1);

  // 3) Pointer step semantics
  assert property (we  |=> wp == $past(wp_p1));
  assert property (!we |=> wp == $past(wp));
  assert property (re  |=> rp == $past(rp_p1));
  assert property (!re |=> rp == $past(rp));

  // 4) Flag correctness and exclusivity
  assert property (full  == ((wp == rp) && gb));
  assert property (empty == ((wp == rp) && !gb));
  assert property (!(full && empty));

  // 5) gb transition correctness (set on fill boundary, clear on read)
  assert property ($rose(gb) |-> $past((wp_p1 == rp) && we));
  assert property ($fell(gb) |-> $past(re));

  // 6) Memory write takes effect next cycle at the written address
  assert property (we |=> mem[$past(wp)] == $past(din));

  // 7) Protocol assumptions (legal FIFO use)
  // - No write when full unless simultaneous read
  // - No read when empty unless simultaneous write
  assume property (!(full  && we && !re));
  assume property (!(empty && re && !we));

  // 8) Data integrity: first read of a written slot returns that data
  //    (relies on protocol assumptions to prevent overwrite)
  property p_data_integrity;
    logic [dw:1] v; logic [1:0] a;
    (we, v = din, a = wp)
      |-> ##[1:$] (re && (rp == a)) ##0 (dout == v);
  endproperty
  assert property (p_data_integrity);

  // 9) Simultaneous read/write keeps occupancy stable (flags not both asserted)
  assert property (we && re && !(wp_p1==rp)
                   |=> !(full || empty));

  // ----------------
  // Coverage
  // ----------------

  // Fill from empty to full with 4 writes (no reads)
  cover property (empty ##1 (we && !re)[*4] ##1 full);

  // Drain from full to empty with 4 reads (no writes)
  cover property (full ##1 (re && !we)[*4] ##1 empty);

  // Pointer wrap-around on write and read
  cover property (wp==2'h3 && we ##1 wp==2'h0);
  cover property (rp==2'h3 && re ##1 rp==2'h0);

  // Full/empty transitions observed
  cover property ($rose(full));
  cover property ($rose(empty));

  // Simultaneous read and write (steady-state transfer)
  cover property (we && re && !(wp_p1==rp));

endmodule

// Bind example (put in a separate file or your testbench):
// bind fifo4 fifo4_asserts u_fifo4_asserts();