// SVA for fifo_data_info
// Bind-in module so we can reference internal signals directly.
module fifo_data_info_sva;

  // Default clock
  default clocking cb @ (posedge clk); endclocking

  // 1) Reset behavior and basic gating
  // Registers hold while reset is low
  assert property (@(cb) !reset_n |-> $stable({write_ptr, read_ptr, count}));
  // readdata is 0 whenever not actively reading or during reset low
  assert property (@(cb) (!(re && reset_n)) |-> readdata == 32'b0);

  // 2) Derived enables and bounds
  assert property (@(cb) we == (count < 4'd14));
  assert property (@(cb) re == (count > 4'd0));
  assert property (@(cb) disable iff (!reset_n) count inside {[4'd0:4'd14]});

  // No out-of-bounds FIFO indexing when used
  assert property (@(cb) (we && reset_n) |-> (write_ptr < 4'd14));
  assert property (@(cb) (re && reset_n) |-> (read_ptr  < 4'd14));

  // 3) Sequential updates (one-step behavior)
  // Pointers only increment by 1 when enabled, else hold
  assert property (@(cb) write_ptr == $past(write_ptr) + (($past(we) && $past(reset_n)) ? 4'd1 : 4'd0));
  assert property (@(cb) read_ptr  == $past(read_ptr)  + (($past(re) && $past(reset_n)) ? 4'd1 : 4'd0));

  // Count update should reflect (+we) - (re)
  // Note: if both we and re are true, this expects no net change.
  assert property (@(cb) count == $past(count)
                              + (($past(we) && $past(reset_n)) ? 4'd1 : 4'd0)
                              - (($past(re) && $past(reset_n)) ? 4'd1 : 4'd0));

  // 4) Data path checks
  // A committed write updates the targeted FIFO location by next cycle
  assert property (@(cb) $past(we && reset_n) |-> (fifo[$past(write_ptr)] == $past(in_port)));
  // On a read, readdata reflects selected entry, zero-extended to 32 bits
  assert property (@(cb) (re && reset_n) |-> (readdata[13:0]  == fifo[read_ptr] &&
                                              readdata[31:14] == '0));

  // 5) Sanity: no underflow/overflow handshakes
  assert property (@(cb) !(reset_n && (re && (count == 4'd0))));
  assert property (@(cb) !(reset_n && (we && (count == 4'd14))));

  // 6) Functional coverage
  cover property (@(cb) disable iff (!reset_n) (count == 4'd0));
  cover property (@(cb) disable iff (!reset_n) (count == 4'd14));
  cover property (@(cb) disable iff (!reset_n) we);
  cover property (@(cb) disable iff (!reset_n) re);
  cover property (@(cb) disable iff (!reset_n) (we && re));          // simultaneous read/write
  cover property (@(cb) disable iff (!reset_n) (write_ptr == 4'd14)); // pointer hitting OOB boundary
  cover property (@(cb) disable iff (!reset_n) (read_ptr  == 4'd14));

endmodule

bind fifo_data_info fifo_data_info_sva sva_inst();