// SVA checker for top_module
module top_module_sva (
  input              clk,
  input              reset,
  input  [7:0]       sel,
  input  [1023:0]    in,
  input  [3:0]       out,
  input  [15:0]      Q,
  // internal DUT signals (bound)
  input  [3:0]       mux_out,
  input  [3:0]       mux_out_delayed,
  input  [15:0]      Q_delayed,
  input  [19:0]      final_output
);

  default clocking cb @(posedge clk); endclocking

  // Track a valid past cycle outside of reset for safe $past usage
  bit past_valid;
  always @(posedge clk) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // -------------------------
  // Multiplexer correctness
  // -------------------------
  // Known-ness checks (sampled on clock)
  a_sel_known:      assert property (cb !$isunknown(sel))
                    else $error("sel has X/Z");
  a_out_known:      assert property (cb !$isunknown(out))
                    else $error("out has X/Z");
  a_in_slice_known: assert property (cb !$isunknown(in[sel*4 +: 4]))
                    else $error("Selected in slice has X/Z");

  // Combinational mux mapping (sampled on clock to avoid races)
  a_mux_map:        assert property (cb out == in[sel*4 +: 4])
                    else $error("out != in[sel*4 +:4]");

  // Registered pipeline of mux_out
  a_mux_delay:      assert property (cb past_valid |-> mux_out_delayed == $past(in[sel*4 +: 4]))
                    else $error("mux_out_delayed != $past(mux_out)");

  // -------------------------
  // Counter behavior and reset semantics
  // -------------------------
  // Q must be 0 on any clock edge when reset is asserted (synchronous effect on Q)
  a_rst_hold_zero:  assert property (cb reset |-> Q == 16'h0000)
                    else $error("Q not zero while reset is asserted");

  // Q only changes on the active clock edge (no async glitches)
  a_no_async_Q:     assert property (@(negedge clk) $stable(Q))
                    else $error("Q changed outside posedge clk");

  // Next-state relation when not coming out of reset this cycle
  a_Q_next:         assert property (cb !reset && !$past(reset) && past_valid
                                     |-> Q == { $past(Q)[14:0], $past(Q)[15] ^ $past(Q)[14] })
                    else $error("Q next-state relation violated");

  // Registered copy Q_delayed
  a_Q_delay:        assert property (cb past_valid |-> Q_delayed == $past(Q))
                    else $error("Q_delayed != $past(Q)");

  // -------------------------
  // Final concatenation logic
  // -------------------------
  a_final_concat:   assert property (cb final_output == {mux_out_delayed, Q_delayed})
                    else $error("final_output != {mux_out_delayed, Q_delayed}");
  a_final_upper_is_past_out:
                    assert property (cb past_valid |-> final_output[19:16] == $past(out))
                    else $error("final_output[19:16] != $past(out)");

  // -------------------------
  // Targeted functional coverage
  // -------------------------
  c_reset_seen:     cover property (cb $rose(reset));
  c_sel_min:        cover property (cb !reset && sel == 8'h00);
  c_sel_max:        cover property (cb !reset && sel == 8'hFF);
  c_sel_changes:    cover property (cb !reset && $changed(sel));
  c_Q_changes:      cover property (cb !reset && $changed(Q));
  c_Q_nonzero:      cover property (cb !reset && (Q != 16'h0000));

endmodule

// Bind the checker to the DUT, including internal signals needed for checks
bind top_module top_module_sva u_top_module_sva (
  .clk            (clk),
  .reset          (reset),
  .sel            (sel),
  .in             (in),
  .out            (out),
  .Q              (Q),
  .mux_out        (mux_out),
  .mux_out_delayed(mux_out_delayed),
  .Q_delayed      (Q_delayed),
  .final_output   (final_output)
);