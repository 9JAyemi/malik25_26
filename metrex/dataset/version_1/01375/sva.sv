// SVA for averager_counter
// Bind this file to the DUT: bind averager_counter averager_counter_sva sva_averager_counter();

module averager_counter_sva;

  // Infer N from wen_cnt width (N must be power of 2)
  localparam int WIDTH_L = $bits(wen_cnt);
  localparam int N_L     = 1 << WIDTH_L;

  default clocking cb @(posedge clk); endclocking

  // Combinational mappings/invariants
  assert property (address == count);
  assert property (clr_fback == (count == count_max));
  assert property (next_count == ((count == count_max) ? 32'd0 : count + 32'd1));
  assert property (max_count == count_max);
  assert property (wen_int == (wen_cnt < N_L));
  assert property (ready_int == (wen_cnt == N_L));
  assert property (wen == (wen_int && avg_on_reg));
  assert property (ready == ready_int);
  assert property (avg_on_out == avg_on_reg);
  assert property (n_avg == avg[N_L-1:0]);

  // Counter behavior
  assert property (restart |-> count == 32'd0);
  assert property (!$past(restart) && $past(!clken) |-> count == $past(count));
  assert property (!$past(restart) && $past(clken) && ($past(count) != $past(count_max)) |-> count == $past(count) + 32'd1);
  assert property (!$past(restart) && $past(clken) && ($past(count) == $past(count_max)) |-> count == 32'd0);

  // avg_on_reg capture/hold
  assert property (restart |-> avg_on_reg == 1'b0);
  assert property (!$past(restart) && $past(clken) |-> avg_on_reg == $past(avg_on));
  assert property (!$past(restart) && $past(!clken) |-> avg_on_reg == $past(avg_on_reg));

  // wen_cnt and index update protocol
  assert property (restart |-> (wen_cnt == '0 && index == '0));
  assert property (!$past(restart) && $past(clken) && $past(wen_int) |-> (wen_cnt == $past(wen_cnt)+1 && index == $past(index)+1));
  assert property (!$past(restart) && (!$past(clken) || !$past(wen_int)) |-> (wen_cnt == $past(wen_cnt) && index == $past(index)));
  assert property (wen_cnt <= N_L);
  assert property ($past(!restart) && $past(wen_cnt) == N_L |-> wen_cnt == N_L);
  assert property (ready -> !wen_int);

  // sum update
  assert property (restart |-> sum == 32'd0);
  assert property (!$past(restart) && $past(!clken) |-> sum == $past(sum));
  assert property (!$past(restart) && $past(clken) && ($past(count) == $past(count_max)) |-> sum == 32'd0);
  assert property (!$past(restart) && $past(clken) && ($past(count) != $past(count_max)) |->
                   sum == $past(sum) + $past(count) - ($past(wen_int) ? $past(avg[N_L-1]) : 32'd0));

  // avg update
  assert property (restart |-> avg == '0);
  assert property (!$past(restart) && $past(!clken) |-> avg == $past(avg));
  assert property (!$past(restart) && $past(clken) && ($past(count) == $past(count_max)) |-> avg == '0);
  assert property (!$past(restart) && $past(clken) && $past(wen_int) && ($past(count) != $past(count_max)) |-> 
                   avg == { $past(sum[N_L-1:0]), $past(wen_cnt), $past(count) });

  // Useful coverage
  cover property (restart ##1 !restart);
  cover property ($past(!restart && clken) && $past(count) == $past(count_max) && count == 32'd0 && clr_fback);
  cover property ($past(!restart && clken && wen_int) [*N_L] ##1 ready);
  cover property ($past(!restart && clken && wen_int) ##1 wen);
  cover property ($past(!restart && clken) && $rose(avg_on) ##1 avg_on_reg);

endmodule

bind averager_counter averager_counter_sva sva_averager_counter();