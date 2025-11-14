// SVA for the provided design. Bind these checkers to the DUT.

module shift_register_sva (
  input clk, input reset, input load, input [7:0] data_in, input [15:0] q
);
  // Async reset clears immediately
  a_shreg_async_reset: assert property (@(posedge reset) ##0 (q == 16'h0));
  // While reset is high at clk edge, q is 0
  a_shreg_sync_clear:  assert property (@(posedge clk) reset |-> ##0 (q == 16'h0));

  // Load path: q <= {data_in, old_q[15:8]}
  a_shreg_load: assert property (@(posedge clk) disable iff (reset)
                                 $past(!reset) && load |-> ##0
                                 q == {data_in, $past(q)[15:8]});

  // Rotate-left path when !load: q <= {old_q[14:0], old_q[15]}
  a_shreg_shift: assert property (@(posedge clk) disable iff (reset)
                                  $past(!reset) && !load |-> ##0
                                  q == {$past(q)[14:0], $past(q)[15]});

  // Knownness on active cycles
  a_shreg_known: assert property (@(posedge clk) disable iff (reset)
                                  $past(!reset) |-> ! $isunknown({load, data_in, q}));

  // Coverage
  c_shreg_load:            cover property (@(posedge clk) disable iff (reset) load);
  c_shreg_shift:           cover property (@(posedge clk) disable iff (reset) !load);
  c_shreg_load_then_shift: cover property (@(posedge clk) disable iff (reset) load ##1 !load);
  c_shreg_wrap:            cover property (@(posedge clk) disable iff (reset)
                                           (!load && $past(q)==16'h8000) ##0 (q==16'h0001));
endmodule


module d_flip_flop_sva (
  input clk, input reset, input d, input q
);
  a_dff_async_reset: assert property (@(posedge reset) ##0 (q == 1'b0));
  a_dff_sync_clear:  assert property (@(negedge clk) reset |-> ##0 (q == 1'b0));
  // Capture on negedge
  a_dff_capture:     assert property (@(negedge clk) disable iff (reset)
                                      1'b1 |-> ##0 (q == $sampled(d)));
  a_dff_known:       assert property (@(negedge clk) disable iff (reset)
                                      ! $isunknown({d,q}));

  // Coverage
  c_dff_cap0: cover property (@(negedge clk) disable iff (reset) (d==0) ##0 (q==0));
  c_dff_cap1: cover property (@(negedge clk) disable iff (reset) (d==1) ##0 (q==1));
endmodule


module functional_module_sva (
  input [15:0] shift_register_out,
  input [0:0]  d_flip_flop_out,
  input [15:0] q
);
  // Enforce intended truncation of {16b,1b} -> 16b
  a_func_concat_trunc: assert property ( q == {shift_register_out[14:0], d_flip_flop_out} );
  a_func_known:        assert property ( ! $isunknown({shift_register_out, d_flip_flop_out, q}) );

  // Simple coverage of LSB mapping
  c_func_lsb_map: cover property ( q[0] == d_flip_flop_out );
endmodule


module top_module_sva (
  input clk, input reset, input load, input [7:0] data_in, input d,
  input [15:0] q,
  input [15:0] shift_register_out,
  input [0:0]  d_flip_flop_out
);
  // Top-level connectivity/intent
  a_top_q_matches: assert property ( q == {shift_register_out[14:0], d_flip_flop_out} );

  // Coverage: load reflects in output upper byte immediately
  c_top_load_vis: cover property (@(posedge clk) disable iff (reset)
                                  load ##0 (q[15:8] == data_in));
endmodule


// Bind checkers to DUT
bind shift_register    shift_register_sva    u_shift_register_sva(.clk(clk), .reset(reset), .load(load), .data_in(data_in), .q(q));
bind d_flip_flop       d_flip_flop_sva       u_d_flip_flop_sva(.clk(clk), .reset(reset), .d(d), .q(q));
bind functional_module functional_module_sva u_functional_module_sva(.shift_register_out(shift_register_out), .d_flip_flop_out(d_flip_flop_out), .q(q));
bind top_module        top_module_sva        u_top_module_sva(.clk(clk), .reset(reset), .load(load), .data_in(data_in), .d(d),
                                                              .q(q), .shift_register_out(shift_register_out), .d_flip_flop_out(d_flip_flop_out));