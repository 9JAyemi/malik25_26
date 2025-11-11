// SVA for rst_generator
module rst_generator_sva (
  input        clk,
  input        rst_i,
  input        rst_o,
  input  [6:0] counter_r,
  input        rst_i_sync_0,
  input        rst_i_sync_1
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // 2-flop synchronizer pipeline checks
  assert property (cb disable iff (!past_valid)
    rst_i_sync_0 == $past(rst_i)
  );
  assert property (cb disable iff (!past_valid)
    rst_i_sync_1 == $past(rst_i_sync_0)
  );

  // Counter update rules
  assert property (cb disable iff (!past_valid)
    $past(rst_o != rst_i_sync_1) && $past(counter_r) != 7'h7F |-> counter_r == $past(counter_r) + 7'd1
  );
  assert property (cb disable iff (!past_valid)
    $past(rst_o != rst_i_sync_1) && $past(counter_r) == 7'h7F |-> counter_r == 7'h00
  );
  assert property (cb disable iff (!past_valid)
    $past(rst_o == rst_i_sync_1) |-> counter_r == 7'h00
  );

  // rst_o toggle gating: only on count==127, and always on count==127
  assert property (cb disable iff (!past_valid)
    (rst_o ^ $past(rst_o)) |-> $past(counter_r) == 7'h7F
  );
  assert property (cb disable iff (!past_valid)
    $past(counter_r) == 7'h7F |-> rst_o != $past(rst_o)
  );
  assert property (cb disable iff (!past_valid)
    $past(counter_r) != 7'h7F |-> rst_o == $past(rst_o)
  );

  // Progress: 128-cycle stable mismatch forces a toggle
  cover property (cb disable iff (!past_valid)
    (rst_o != rst_i_sync_1)[*128] |=> (rst_o != $past(rst_o))
  );

  // Cover both polarities on rst_o
  cover property (cb $rose(rst_o));
  cover property (cb $fell(rst_o));

  // Cover counter hitting terminal count under mismatch
  cover property (cb disable iff (!past_valid)
    $past(rst_o != rst_i_sync_1) && $past(counter_r)==7'h7E |-> counter_r==7'h7F
  );

  // Cover abort: mismatch period <128 then re-align without toggle
  cover property (cb disable iff (!past_valid)
    (rst_o != rst_i_sync_1)[*1:20] ##1 (rst_o == rst_i_sync_1) ##1 (rst_o == $past(rst_o))
  );

endmodule

bind rst_generator rst_generator_sva sva (
  .clk         (clk),
  .rst_i       (rst_i),
  .rst_o       (rst_o),
  .counter_r   (counter_r),
  .rst_i_sync_0(rst_i_sync_0),
  .rst_i_sync_1(rst_i_sync_1)
);