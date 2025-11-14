// SVA for top_module
// Bind in your environment: bind top_module top_module_sva u_top_module_sva();

module top_module_sva;

  // Sample on both edges (combinational invariants are true at either edge)
  default clocking cb @(posedge clk or negedge clk); endclocking

  // Basic X-checks on primary inputs when evaluating functional checks
  ap_no_x_inputs: assert property (!$isunknown({sel,in}));

  // Multiplexer structural behavior:
  // - High bits of mux_out must be zero due to 1-bit RHS assignment widening
  ap_mux_high_zero: assert property (mux_out[15:1] == '0);
  // - LSB of mux_out equals selected input bit
  ap_mux_bit0_sel:  assert property (!$isunknown(sel) |-> mux_out[0] == in[sel]);

  // Dual-edge flip-flop behavior (use cross-edge sampling to avoid NBA races)
  // d_ff_out captures selected input at posedge
  ap_pos_cap: assert property (@(negedge clk)
                               d_ff_out == $past(in[$past(sel,0, posedge clk)], 0, posedge clk));
  // d_ff_out_r updates from d_ff_out at negedge
  ap_neg_transfer: assert property (@(negedge clk)
                                    d_ff_out_r == $past(d_ff_out, 0, posedge clk));

  // Logical OR network and output
  ap_or_in_def: assert property (or_in == (d_ff_out_r ? 16'hFFFF : in));
  ap_q_def:     assert property (q == (d_ff_out_r | (|in)));
  // If d_ff_out_r is 1, q must be 1 on the next sample as well
  ap_q_forced_when_r1: assert property (d_ff_out_r |-> q);

  // Coverage
  // - Exercise all select values
  genvar i;
  generate
    for (i=0;i<16;i++) begin : CSEL
      cover property (@(posedge clk) sel==i);
    end
  endgenerate
  // - See both values of the registered output
  cover_dff_r0: cover property (@(negedge clk) d_ff_out_r==0);
  cover_dff_r1: cover property (@(negedge clk) d_ff_out_r==1);
  // - Observe q both 0 and 1
  cover_q0: cover property (q==0);
  cover_q1: cover property (q==1);
  // - Corner cases for q composition
  cover_forced_q:     cover property (@(negedge clk) d_ff_out_r==1 && in==16'h0000 ##0 q==1);
  cover_input_only_q: cover property (@(negedge clk) d_ff_out_r==0 && (|in)==1'b1 && q==1);
  cover_all_zero_q0:  cover property (@(negedge clk) d_ff_out_r==0 && in==16'h0000 ##0 q==0);

endmodule