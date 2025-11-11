// SVA for sync_gray
// Bind this checker to the RTL: 
// bind sync_gray sync_gray_sva #(.DATA_WIDTH(DATA_WIDTH), .CLK_ASYNC(CLK_ASYNC)) u_sync_gray_sva();

module sync_gray_sva #(parameter int DATA_WIDTH = 1,
                       parameter bit CLK_ASYNC = 1);

  // Basic parameter sanity
  initial begin
    assert (DATA_WIDTH >= 1) else $error("sync_gray: DATA_WIDTH must be >= 1");
  end

  // No-X on resets
  assert property (@(posedge in_clk)  !$isunknown(in_resetn));
  assert property (@(posedge out_clk) !$isunknown(out_resetn));

  // in-domain reset behavior and mapping
  assert property (@(posedge in_clk)
                   !in_resetn |-> (in_count_gray == '0));

  assert property (@(posedge in_clk)
                   disable iff (!in_resetn)
                   in_count_gray == b2g(in_count));

  // Function round-trip (observed arguments)
  assert property (@(posedge in_clk)
                   disable iff (!in_resetn)
                   g2b(b2g(in_count)) == in_count);

  // out-domain reset behavior and pipeline relations
  assert property (@(posedge out_clk)
                   !out_resetn |-> (out_count_gray_m1 == '0 && out_count_gray_m2 == '0 && out_count_m == '0));

  assert property (@(posedge out_clk)
                   disable iff (!out_resetn)
                   out_count_gray_m1 == in_count_gray); // sampled async bus

  assert property (@(posedge out_clk)
                   disable iff (!out_resetn)
                   out_count_gray_m2 == $past(out_count_gray_m1));

  assert property (@(posedge out_clk)
                   disable iff (!out_resetn)
                   out_count_m == g2b(out_count_gray_m2));

  // Function round-trip (observed arguments in out domain)
  assert property (@(posedge out_clk)
                   disable iff (!out_resetn)
                   b2g(g2b(out_count_gray_m2)) == out_count_gray_m2);

  // Output mux behavior per CLK_ASYNC
  generate
    if (CLK_ASYNC) begin : g_async
      assert property (@(posedge out_clk)
                       out_count == out_count_m);
      assert property (@(posedge out_clk)
                       out_count == g2b(out_count_gray_m2));
    end else begin : g_sync
      // Combinational tie-through; check on both clocks
      assert property (@(posedge in_clk)  out_count == in_count);
      assert property (@(posedge out_clk) out_count == in_count);
    end
  endgenerate

  // No-X on key state/outputs when released from reset
  assert property (@(posedge in_clk)
                   disable iff (!in_resetn)
                   !$isunknown(in_count_gray));
  assert property (@(posedge out_clk)
                   disable iff (!out_resetn)
                   (!$isunknown(out_count_gray_m1) && !$isunknown(out_count_gray_m2) &&
                    !$isunknown(out_count_m) && !$isunknown(out_count)));

  // Gray property when source increments by +1 (optional, no assumption about environment beyond the antecedent)
  assert property (@(posedge in_clk)
                   disable iff (!in_resetn)
                   ($past(in_count,1,'0) + 1 == in_count) |-> $onehot(in_count_gray ^ $past(in_count_gray)));

  // Stability mapping: if in_count stable, gray stable
  assert property (@(posedge in_clk)
                   disable iff (!in_resetn)
                   (in_count == $past(in_count)) |-> (in_count_gray == $past(in_count_gray)));

  // Optional stronger CDC checks under a standard counter-use assumption
`ifdef ASSERT_CDC_STRONG
  // Assume source is a free-running +1 counter with wrap
  assume property (@(posedge in_clk)
                   disable iff (!in_resetn)
                   (in_count == $past(in_count)) ||
                   (in_count == $past(in_count) + 1) ||
                   ($past(in_count) == {DATA_WIDTH{1'b1}} && in_count == '0));

  // Then decoded out_count_m is monotonic non-decreasing with wrap
  assert property (@(posedge out_clk)
                   disable iff (!out_resetn)
                   (out_count_m >= $past(out_count_m)) ||
                   ($past(out_count_m) == {DATA_WIDTH{1'b1}} && out_count_m == '0));
`endif

  // Lightweight coverage
  cover property (@(posedge in_clk)  disable iff (!in_resetn) $changed(in_count) && $changed(in_count_gray));
  cover property (@(posedge out_clk) disable iff (!out_resetn) $changed(out_count_gray_m1) ##1 $changed(out_count_gray_m2) ##1 $changed(out_count_m));
  cover property (@(posedge out_clk) disable iff (!out_resetn) $changed(out_count));

endmodule