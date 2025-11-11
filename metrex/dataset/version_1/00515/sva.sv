// SVA checker for fifo. Bind this to the DUT.
// Focuses on flag correctness, pointer/count updates, bounds, and data integrity.
module fifo_sva #(parameter WIDTH=8, DEPTH=4, ADDR_W=2) ();

  default clocking cb @(posedge clk_i); endclocking
  default disable iff (rst_i);

  // Flag equivalence
  assert property (valid_o == (count_q != 0));
  assert property (accept_o == (count_q != DEPTH));

  // Bounds and domain
  assert property (count_q <= DEPTH);
  assert property (wr_ptr_q < DEPTH);
  assert property (rd_ptr_q < DEPTH);

  // Output equals selected RAM word
  assert property (data_out_o == ram_q[rd_ptr_q]);

  // Pointer updates and stability
  assert property ((push_i && accept_o) |=> wr_ptr_q == $past(wr_ptr_q) + 1);
  assert property (!(push_i && accept_o) |=> $stable(wr_ptr_q));

  assert property ((pop_i && valid_o) |=> rd_ptr_q == $past(rd_ptr_q) + 1);
  assert property (!(pop_i && valid_o) |=> $stable(rd_ptr_q));

  // Count updates
  assert property (((push_i && accept_o) && !(pop_i && valid_o)) |=> count_q == $past(count_q) + 1);
  assert property ((!(push_i && accept_o) && (pop_i && valid_o)) |=> count_q == $past(count_q) - 1);
  assert property ((((push_i && accept_o) == (pop_i && valid_o))) |=> count_q == $past(count_q));

  // No X on key state/outputs
  assert property (!$isunknown({valid_o, accept_o, rd_ptr_q, wr_ptr_q, count_q}));

  // Data integrity: the word written at wr_ptr must be observed when rd_ptr first reaches that slot
  property p_data_integrity;
    logic [WIDTH-1:0] d;
    logic [ADDR_W-1:0] pw;
    (push_i && accept_o, d = data_in_i, pw = wr_ptr_q)
      |->
    ##1 first_match (##[0:$] (rd_ptr_q == pw))
    ##0 (data_out_o == d);
  endproperty
  assert property (p_data_integrity);

  // Asynchronous reset state
  assert property (@(posedge clk_i)
                   rst_i |-> (count_q == 0 && rd_ptr_q == 0 && wr_ptr_q == 0
                              && valid_o == 0 && accept_o == 1 && data_out_o == 0));

  // Coverage
  cover property ((count_q == 0) ##1 (push_i && accept_o)[*DEPTH] ##1 (count_q == DEPTH));   // empty->full
  cover property ((count_q == DEPTH) ##1 (pop_i && valid_o)[*DEPTH] ##1 (count_q == 0));     // full->empty
  cover property ((count_q > 0 && count_q < DEPTH) && (push_i && accept_o) && (pop_i && valid_o)); // sim push/pop
  cover property ((push_i && !accept_o)); // push blocked when full
  cover property ((pop_i && !valid_o));   // pop blocked when empty
  cover property ((push_i && accept_o && $past(wr_ptr_q) == DEPTH-1) |=> (wr_ptr_q == 0));  // wr wrap
  cover property ((pop_i && valid_o && $past(rd_ptr_q) == DEPTH-1) |=> (rd_ptr_q == 0));    // rd wrap
  cover property (p_data_integrity);

endmodule

bind fifo fifo_sva #(.WIDTH(WIDTH), .DEPTH(DEPTH), .ADDR_W(ADDR_W)) fifo_sva_b();