module test_in_sva (
  input  logic         clk,
  input  logic         rst,
  input  logic         enable,
  input  logic [1:0]   ready,
  input  logic [23:0]  size,
  input  logic [1:0]   activate,
  input  logic [31:0]  data,
  input  logic         strobe,
  input  logic [23:0]  count // internal signal from RTL
);

  ///// Reset behavior /////
  // On reset, outputs and internal count are cleared to zero.
  check_reset_clears_outputs: assert property (
    @(posedge clk) rst |-> (activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0)
  );

  ///// Activate encoding /////
  // activate is always at most one-hot (00,01,10).
  check_activate_onehot0: assert property (
    @(posedge clk) disable iff (rst) $onehot0(activate)
  );

  ///// Start selection /////
  // When idle and enabled with ready[0], next cycle activate[0]=1 and count reset.
  check_start_pick0: assert property (
    @(posedge clk) disable iff (rst)
      ((ready > 2'd0) && (activate == 2'b00) && enable && ready[0]) |=> (activate == 2'b01) && (count == 24'd0)
  );
  // When idle and enabled with only ready[1], next cycle activate[1]=1 and count reset.
  check_start_pick1: assert property (
    @(posedge clk) disable iff (rst)
      ((ready > 2'd0) && (activate == 2'b00) && enable && (ready[0] == 1'b0)) |=> (activate == 2'b10) && (count == 24'd0)
  );
  // activate[0] can only rise from idle with enable and ready[0].
  check_activate0_rise_requires_cond: assert property (
    @(posedge clk) disable iff (rst)
      $rose(activate[0]) |-> $past((activate == 2'b00) && enable && ready[0])
  );
  // activate[1] can only rise from idle with enable, ready[0]==0, and ready[1]==1.
  check_activate1_rise_requires_cond: assert property (
    @(posedge clk) disable iff (rst)
      $rose(activate[1]) |-> $past((activate == 2'b00) && enable && (ready[0] == 1'b0) && (ready[1] == 1'b1))
  );

  ///// Streaming behavior /////
  // While active and count < size, strobe must be 1 in that cycle.
  check_streaming_implies_strobe: assert property (
    @(posedge clk) disable iff (rst)
      ((activate > 2'd0) && (count < size)) |-> (strobe == 1'b1)
  );
  // strobe can only be 1 during cycles with activate > 0 and count < size.
  check_strobe_implies_streaming: assert property (
    @(posedge clk) disable iff (rst)
      (strobe == 1'b1) |-> ((activate > 2'd0) && (count < size))
  );
  // If previously streaming, count increments by 1.
  check_count_increments_while_streaming: assert property (
    @(posedge clk) disable iff (rst)
      $past((activate > 2'd0) && (count < size)) |-> (count == $past(count) + 24'd1)
  );
  // If previously streaming, data equals the count from two cycles ago.
  check_data_matches_prev_count_on_stream: assert property (
    @(posedge clk) disable iff (rst)
      $past((activate > 2'd0) && (count < size)) |-> ($past(data) == $past($past(count)))
  );
  // If previously streaming, upper data bits [31:24] are zero (zero-extended count).
  check_data_upper_zero_on_stream: assert property (
    @(posedge clk) disable iff (rst)
      $past((activate > 2'd0) && (count < size)) |-> ($past(data[31:24]) == 8'h00)
  );

  ///// Termination /////
  // When active and count >= size, deactivate on the next cycle.
  check_deactivate_on_done: assert property (
    @(posedge clk) disable iff (rst)
      ((activate > 2'd0) && (count >= size)) |=> (activate == 2'b00)
  );
  // A transition from active to idle only occurs when the prior count >= size.
  check_deactivate_only_when_done: assert property (
    @(posedge clk) disable iff (rst)
      ((activate == 2'b00) && $past(activate > 2'd0)) |-> $past(count >= size)
  );

endmodule