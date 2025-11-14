// SVA for red_pitaya_iq_hpf_block
// Bind this file to the DUT:
//   bind red_pitaya_iq_hpf_block rp_iq_hpf_sva #(.ALPHABITS(ALPHABITS), .HIGHESTALPHABIT(HIGHESTALPHABIT), .LPFBITS(LPFBITS)) rp_iq_hpf_sva_i();

module rp_iq_hpf_sva #(parameter int ALPHABITS=25, HIGHESTALPHABIT=18, LPFBITS=14) ();

  localparam signed [LPFBITS-1:0] MAXP = {1'b0,{LPFBITS-1{1'b1}}};
  localparam signed [LPFBITS-1:0] MINN = {1'b1,{LPFBITS-1{1'b0}}};

  default clocking cb @(posedge clk_i); endclocking

  // Reset clears in 1 cycle
  assert property (@(posedge clk_i) reset_i |=> (y==0 && delta==0 && delta_out==0 && signal_o==0));

  // No X after reset deassert
  assert property (@(posedge clk_i) disable iff (reset_i)
                   !$isunknown({y, delta, delta_out, signal_o, diff, y_out, alpha_i, signal_i}));

  // Output mirror
  assert property (@(posedge clk_i) disable iff (reset_i) signal_o == delta_out);

  // y_out slice/sign consistency
  assert property (@(posedge clk_i) y_out == y[ALPHABITS+LPFBITS-1:ALPHABITS]);
  assert property (@(posedge clk_i) y_out[LPFBITS-1] == y[ALPHABITS+LPFBITS-1]);

  // diff computed with proper sign-extension to LPFBITS+1
  assert property (@(posedge clk_i) disable iff (reset_i)
                   diff == $signed({signal_i[LPFBITS-1],signal_i})
                         - $signed({y_out[LPFBITS-1],y_out}));

  // Pipeline: delta and accumulator y
  assert property (@(posedge clk_i) disable iff (reset_i)
                   !$past(reset_i) |-> delta == $signed($past(diff)) * $signed($past(alpha_i)));
  assert property (@(posedge clk_i) disable iff (reset_i)
                   !$past(reset_i) |-> y == $past(y) + $past(delta));

  // Saturator behavior
  assert property (@(posedge clk_i) disable iff (reset_i)
                   (diff[LPFBITS:LPFBITS-1]==2'b01) |-> (delta_out==MAXP));
  assert property (@(posedge clk_i) disable iff (reset_i)
                   (diff[LPFBITS:LPFBITS-1]==2'b10) |-> (delta_out==MINN));
  assert property (@(posedge clk_i) disable iff (reset_i)
                   (diff[LPFBITS]==diff[LPFBITS-1]) |-> (delta_out==diff[LPFBITS-1:0]));

  // Coverage
  cover property (@(posedge clk_i) reset_i ##1 !reset_i);
  cover property (@(posedge clk_i) disable iff (reset_i) (diff[LPFBITS:LPFBITS-1]==2'b01));
  cover property (@(posedge clk_i) disable iff (reset_i) (diff[LPFBITS:LPFBITS-1]==2'b10));
  cover property (@(posedge clk_i) disable iff (reset_i) (diff[LPFBITS]==diff[LPFBITS-1]) && (diff!=0));
  cover property (@(posedge clk_i) disable iff (reset_i) $changed(y) && $past(delta)!=0);

endmodule