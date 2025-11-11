// SVA for sfifo_nto8
// Bind this file to the DUT: bind sfifo_nto8 sfifo_nto8_sva u_sfifo_nto8_sva();

module sfifo_nto8_sva;

  localparam int MAX = 24;

  // Default clocking/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (!nrst);

  // --------------------
  // Basic correctness
  // --------------------
  // Async reset holds state at 0 whenever nrst==0
  assert property (!nrst |-> (cnt==0 && buffer==0));

  // Sync reset clears on next active clock when ce
  assert property (ce && reset |=> (cnt==0 && buffer==0));

  // Hold when ce==0 (no state change)
  assert property (!ce && !reset |=> (cnt==$past(cnt) && buffer==$past(buffer)));

  // No-op when neither wr nor rd while enabled
  assert property (ce && !reset && !wr && !rd |=> (cnt==$past(cnt) && buffer==$past(buffer)));

  // --------------------
  // Counter semantics
  // --------------------
  assert property (ce && !reset && wr &&  rd |=> cnt == $unsigned($past(cnt)) + $unsigned($past(nsin)) - $unsigned($past(nsout)));
  assert property (ce && !reset && wr && !rd |=> cnt == $unsigned($past(cnt)) + $unsigned($past(nsin)));
  assert property (ce && !reset && !wr && rd |=> cnt == $unsigned($past(cnt)) - $unsigned($past(nsout)));

  // Range safety on cnt (no under/overflow)
  assert property (ce && !reset |-> $unsigned(cnt) <= MAX);

  // Prevent underflow/overflow on operations
  assert property (ce && !reset && rd && !wr |-> $unsigned($past(cnt)) >= $unsigned($past(nsout)));
  assert property (ce && !reset && wr && !rd |-> ($unsigned($past(cnt)) + $unsigned($past(nsin))) <= MAX);
  assert property (ce && !reset && wr &&  rd |-> ($unsigned($past(cnt)) >= $unsigned($past(nsout))) &&
                                            ($unsigned($past(cnt)) + $unsigned($past(nsin)) - $unsigned($past(nsout)) <= MAX));

  // --------------------
  // Flag correctness
  // --------------------
  assert property (full  == ($unsigned(cnt) + $unsigned(nsin) > MAX));
  assert property (empty == ($unsigned(cnt) <  $unsigned(nsout)));

  // --------------------
  // Datapath/transform correctness
  // --------------------
  // Combinational relations
  assert property (shift_out == ({8'h0, buffer} << nsout));
  assert property (space_left == (rd ? (MAX - $unsigned(cnt) + $unsigned(nsout))
                                     : (MAX - $unsigned(cnt))));
  assert property (dout == (({8'h0, buffer} << nsout)[31:24]));

  // Next-state buffer updates
  assert property (ce && !reset && wr &&  rd |=> buffer ==
                   (({8'h0, $past(buffer)} << $past(nsout))[23:0]) |
                   (({24'h0, $past(din)}   << $past(space_left))[31:8]));

  assert property (ce && !reset && wr && !rd |=> buffer ==
                   ($past(buffer) | ({24'h0, $past(din)} << $past(space_left))[31:8]));

  assert property (ce && !reset && !wr && rd |=> buffer ==
                   (({8'h0, $past(buffer)} << $past(nsout))[23:0]));

  // Outputs are known when out of reset
  assert property (!$isunknown({full, empty, dout}));

  // --------------------
  // Targeted coverage
  // --------------------
  cover property (ce && !reset && wr && !rd && ($unsigned(cnt) + $unsigned(nsin) == MAX)); // reach full on write
  cover property (ce && !reset && rd && !wr && ($unsigned(cnt) == $unsigned(nsout)));      // reach empty on read
  cover property (ce && !reset && wr &&  rd && ($unsigned(nsin) == $unsigned(nsout)));     // balanced w/r
  cover property (ce && !reset && wr &&  rd && ($unsigned(nsin) >  $unsigned(nsout)));     // net increase
  cover property (ce && !reset && wr &&  rd && ($unsigned(nsin) <  $unsigned(nsout)));     // net decrease
  cover property (ce && !reset && cnt == 0);
  cover property (ce && !reset && cnt == MAX);
  cover property (!ce);
  cover property (full);
  cover property (empty);

endmodule