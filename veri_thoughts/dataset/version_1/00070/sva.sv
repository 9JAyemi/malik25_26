// SVA for bidirectional_data_port
module bidirectional_data_port_sva (
  input logic        clk,
  input logic        reset,   // active-low
  input logic [3:0]  in,
  input logic        dir,
  input logic [3:0]  out,
  input logic [3:0]  dout
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [3:0] rev4 (input logic [3:0] v);
    return {v[0], v[1], v[2], v[3]};
  endfunction

  // Asynchronous reset drives zeros immediately
  ap_async_reset_zero: assert property (@(negedge reset) (out == 4'b0 && dout == 4'b0));

  // While in reset, outputs are held at zero
  ap_reset_hold: assert property (cb !reset |-> (out == 4'b0 && dout == 4'b0));

  // No X/Z on outputs when not in reset
  ap_no_unknowns: assert property (cb disable iff (!reset) (!$isunknown(out) && !$isunknown(dout)));

  // out always follows in (registered by 1 cycle) regardless of dir
  ap_out_follows_in: assert property (cb disable iff (!reset) 1'b1 |=> out == $past(in));

  // dout updates only when dir==1; otherwise holds its value
  ap_dout_holds_when_dir0: assert property (cb disable iff (!reset) (!dir) |=> $stable(dout));

  // When dir==1, dout is the bit-reversed version of in (registered by 1 cycle)
  ap_dout_rev_when_dir1: assert property (cb disable iff (!reset) dir |=> dout == rev4($past(in)));

  // Simple functional coverage
  cp_dir0:              cover property (cb disable iff (!reset) !dir);
  cp_dir1:              cover property (cb disable iff (!reset) dir);
  cp_dir_toggle:        cover property (cb disable iff (!reset) dir ##1 !dir ##1 dir);
  cp_dout_reversal:     cover property (cb disable iff (!reset) dir |=> dout == rev4($past(in)));
  cp_dout_hold_dir0:    cover property (cb disable iff (!reset) !dir |=> dout == $past(dout));

endmodule

// Bind into DUT
bind bidirectional_data_port bidirectional_data_port_sva sva_i (
  .clk(clk),
  .reset(reset),
  .in(in),
  .dir(dir),
  .out(out),
  .dout(dout)
);