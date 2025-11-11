// SVA for instruction_fetch
// Bind this file to the DUT: bind instruction_fetch instruction_fetch_sva sva();

module instruction_fetch_sva;

  default clocking cb @ (posedge clk); endclocking
  default disable iff (!nrst)

  // Local helpers
  let aligned   = (addr[1:0] == 2'b00);
  let active_s  = (rd_cmd && aligned && !i_IErr);

  // Combinational outputs equivalence
  a_align:    assert property (err_align == (rd_cmd && !aligned));
  a_errbus:   assert property (err_bus   == i_IErr);
  a_oirdc:    assert property (o_IRdC    == active_s);
  a_oaddr:    assert property (o_IAddr   == (active_s ? addr : 32'h0));
  a_busy:     assert property (busy      == ((active_s || state) && !i_IRdy));
  a_mux:      assert property (instr_dat == ((active_s || state) ? i_IData : lch_idata));

  // Reset values (async reset sampled at clk)
  a_reset_vals: assert property (!nrst |-> (state==1'b0 && lch_idata==32'h0 && o_IAddr==32'h0 && o_IRdC==1'b0));

  // FSM behavior
  a_to_wait:     assert property ( state && !$past(state) |-> $past(active_s && !i_IRdy) );
  a_wait_exit:   assert property ( state &&  i_IRdy |=> !state );
  a_wait_sticky: assert property ( state && !i_IRdy |=>  state );

  // Data capture
  a_latch: assert property ( i_IRdy && (state || (!state && active_s)) |=> lch_idata == $past(i_IData) );

  // Sanity (no X on key regs/outs)
  a_no_x: assert property ( !$isunknown({busy, err_align, err_bus, o_IAddr, o_IRdC, instr_dat, state, lch_idata}) );

  // Coverage
  c_align_err:    cover property (rd_cmd && !aligned);
  c_bus_err:      cover property (rd_cmd && i_IErr);
  c_single_cycle: cover property (!state && active_s && i_IRdy ##1 !state && !busy);
  c_wait_path:    cover property (!state && active_s && !i_IRdy ##1 state [*1:$] ##1 i_IRdy ##1 !state);
  c_busy_drop:    cover property (busy ##1 !busy);

endmodule