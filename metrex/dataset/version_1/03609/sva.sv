// SVA for hpdmc_banktimer
// Bind this module to the DUT:  bind hpdmc_banktimer hpdmc_banktimer_sva sva();

// Notes:
// - Uses portless bind; properties reference DUT internals directly (counter, precharge_safe).

module hpdmc_banktimer_sva;

  // Default clocking/reset
  default clocking cb @(posedge sys_clk); endclocking
  default disable iff (sdram_rst);

  // Convenience
  wire idle = !read && !write;

  // Reset behavior (explicit, not disabled)
  assert property (@(posedge sys_clk) sdram_rst |-> (precharge_safe && counter==3'd0))
    else $error("Reset state mismatch");

  // Command load behavior and priority
  assert property (read |=> (precharge_safe==1'b0 && counter==3'd4))
    else $error("READ did not load 4 and deassert precharge_safe");
  assert property (write && !read |=> (precharge_safe==1'b0 && counter=={1'b1,tim_wr}))
    else $error("WRITE did not load {1,tim_wr} and deassert precharge_safe");
  assert property (read && write |=> (precharge_safe==1'b0 && counter==3'd4))
    else $error("READ/WRITE priority violated (READ must win)");

  // Safety encoding/consistency
  assert property (precharge_safe |-> counter==3'd0)
    else $error("precharge_safe implies counter!=0");
  assert property (!precharge_safe |-> (counter inside {[3'd1:3'd7]}))
    else $error("Counter out of range while unsafe");

  // Idle behavior: monotonic and stable
  // When previously unsafe and idle now: decrement and possibly release safe
  assert property ( idle && !$past(precharge_safe,1,sdram_rst)
                    |-> ( counter == $past(counter,1,sdram_rst) - 3'd1
                          && precharge_safe == ($past(counter,1,sdram_rst)==3'd1) ) )
    else $error("Idle-unsafe decrement/transition violated");

  // When previously safe and idle now: hold safe and zero
  assert property ( idle &&  $past(precharge_safe,1,sdram_rst)
                    |-> (precharge_safe && counter==3'd0) )
    else $error("Idle-safe stability violated");

  // No spurious changes on a no-op cycle (covers both safe/unsafe via above, but keep concise check)
  assert property ( idle |-> $stable(read) && $stable(write) ) else $error("Idle defined as !read&&!write");

  // Functional timing coverage
  // READ completes to safe after exactly 4 cycles if no new commands
  cover property ( read
                   ##1 (!read && !write && !precharge_safe)[*3]
                   ##1 (precharge_safe && counter==3'd0) );

  // WRITE completes to safe for each tim_wr value if no new commands (length varies by tim_wr)
  genvar i;
  generate for (i=0;i<4;i++) begin : CWR
    cover property ( write && !read && (tim_wr==i[1:0])
                     ##1 (!read && !write && !precharge_safe)[*]
                     ##1 (precharge_safe && counter==3'd0) );
  end endgenerate

  // Priority/use-cases coverage
  cover property (read && write ##1 (counter==3'd4 && !precharge_safe));
  cover property (read ##1 !precharge_safe ##1 write);  // back-to-back commands while unsafe

endmodule