// Assertions for axi_traffic_gen_v2_0_7_axis_fifo
// Paste inside the module or bind externally. Concise, high-value checks.

`ifdef AXIS_FIFO_SVA
  default clocking cb @(posedge Clk); endclocking
  // Disable checks while in reset (Rst_n==0)
  default disable iff (!Rst_n);

  // 1) Synchronous reset behavior (checked at the cycle after reset is sampled low)
  property p_sync_reset;
    !Rst_n |=> (in_ptr_ff=='0
             && out_ptr_ff==((HEADREG)?'h1:'h0)
             && depth_ff=='0
             && valid_ff==0
             && valid_filt_ff==0
             && full_ff==0
             && notfull_ff==0
             && headreg_ff=='0);
  endproperty
  assert property (p_sync_reset);

  // 2) Registered state matches next-state combinational functions (1-cycle latency)
  assert property ($past(Rst_n) |-> in_ptr_ff    == $past(in_ptr));
  assert property ($past(Rst_n) |-> out_ptr_ff   == $past(out_ptr));
  assert property ($past(Rst_n) |-> depth_ff     == $past(depth));
  assert property ($past(Rst_n) |-> valid_ff     == $past(valid));
  assert property ($past(Rst_n) |-> valid_filt_ff== $past(valid_filt));
  assert property ($past(Rst_n) |-> full_ff      == $past(full));
  assert property ($past(Rst_n) |-> notfull_ff   == $past(~full));
  assert property ($past(Rst_n) |-> headreg_ff   == $past(headreg));

  // 3) Key invariants
  assert property (valid_ff == (depth_ff != '0));
  assert property (full_ff == ~notfull_ff);
  assert property (out_overflow == depth_ff[DEPTHBITS]);
  assert property (out_depth == depth_ff[DEPTHBITS-1:0]);
  assert property (out_valid == valid_filt_ff);
  assert property (out_notfull == notfull_ff);

  // 4) Depth counter update rules and safety
  assert property ($past(Rst_n) && $past(in_push)  && !$past(do_pop) |-> depth_ff == $past(depth_ff)+1);
  assert property ($past(Rst_n) && !$past(in_push) &&  $past(do_pop) |-> depth_ff == $past(depth_ff)-1);
  assert property ($past(Rst_n) && ($past(in_push) == $past(do_pop))  |-> depth_ff == $past(depth_ff));
  // No pop when empty
  assert property (depth_ff=='0 |-> !do_pop);

  // 5) Pointer update rules
  assert property ($past(Rst_n) && $past(in_push)  |-> in_ptr_ff  == $past(in_ptr_ff) + 1);
  assert property ($past(Rst_n) && !$past(in_push) |-> in_ptr_ff  == $past(in_ptr_ff));
  assert property ($past(Rst_n) && $past(do_pop)   |-> out_ptr_ff == $past(out_ptr_ff) + 1);
  assert property ($past(Rst_n) && !$past(do_pop)  |-> out_ptr_ff == $past(out_ptr_ff));

  // 6) Output-data mux correctness
  if (ZERO_INVALID) begin
    assert property (!valid_filt_ff |-> out_data == in_invalid_data);
    assert property ( valid_filt_ff |-> out_data == out_data_pre);
  end else begin
    assert property (out_data == out_data_pre);
  end
  if (HEADREG) begin
    assert property (out_data_pre == headreg_ff);
  end else begin
    assert property (out_data_pre == raw_data);
  end

  // 7) Out-valid gating behavior (cannot newly assert while blocked)
  // valid_filt_ff follows valid_filt 1 cycle later (already checked). Add semantic check:
  assert property ($past(in_block_outvalid) && !$past(valid_filt_ff) |-> !valid_filt_ff);
  assert property ($past(in_block_outvalid) && $past(valid) && $past(valid_filt_ff) && !$past(do_pop) |-> valid_filt_ff);

  // 8) Data integrity at head: first word after empty stays until popped
  property p_first_word_stable_until_pop;
    (in_push && (depth_ff=='0)) |=> (out_data_pre == $past(in_data)) until_with (do_pop);
  endproperty
  assert property (p_first_word_stable_until_pop);

  // 9) Simultaneous push+pop at depth==1 picks incoming as next head (HEADREG path)
  if (HEADREG) begin
    assert property ($past(depth_ff)==1 && $past(in_push) && $past(do_pop) |-> headreg_ff == $past(in_data));
  end

  // 10) Parameter sanity (static)
  initial begin
    assert (DEPTH == (1<<DEPTHBITS))
      else $error("DEPTH must equal 2**DEPTHBITS");
    assert (FULL_LEVEL <= DEPTH)
      else $error("FULL_LEVEL must be <= DEPTH");
  end

  // Coverage
  cover property (in_push ##1 in_push [*FULL_LEVEL] ##1 full_ff);                    // reach full threshold
  cover property (full_ff ##1 !full_ff);                                             // full to not-full transition
  cover property (depth_ff=='0 ##1 in_push ##1 do_pop);                              // push then pop from 1->0
  cover property (depth_ff==1 && in_push && do_pop);                                 // sim push+pop at 1
  cover property (!valid_filt_ff ##1 in_block_outvalid ##1 !valid_filt_ff);          // block keeps out_valid low
  cover property (out_overflow);                                                     // overflow observed
`endif