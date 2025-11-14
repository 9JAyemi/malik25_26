// SVA for audio_fifo: concise, high-quality checks and coverage.
module audio_fifo_sva (
  input  logic        clk, rst, en, we, re,
  input  logic [1:0]  mode,
  input  logic [31:0] din,
  input  logic [19:0] dout,
  input  logic [1:0]  status,
  input  logic        full, empty,
  // Internal DUT signals (bound by name)
  input  logic [2:0]  wp,
  input  logic [3:0]  rp,
  input  logic [1:0]  status_reg,
  input  logic [19:0] dout_reg,
  input  logic        empty_reg,
  input  logic [31:0] mem [0:7]
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity / connectivity
  a_no_x:        assert property (!$isunknown({dout,status,full,empty})); 
  a_out_assigns: assert property (dout==dout_reg && status==status_reg && empty==empty_reg);

  // Legal mode on any read
  a_mode_legal:  assert property ( (!en || !re) or (mode inside {2'b00,2'b01,2'b10}) );

  // When en==0, state holds
  a_hold_en0:    assert property (!en |=> $stable({wp,rp,status_reg,dout_reg,empty_reg}));

  // Full flag definition (combinational)
  a_full_def:    assert property ( full == (({1'b0,wp} == rp) & we) );

  // Next-state of empty and status (computed from previous cycle values when en)
  a_empty_nxt:   assert property ( en |=> empty == ( ($past(rp)=={1'b0,$past(wp)}) &
                                                    (($past(mode)==2'b00) ? 1'b1 : $past(we)) ) );
  a_status_nxt:  assert property ( en |=> status == ( ({1'b0,$past(wp)} - $past(rp) - 4'd1)[1:0] ) );

  // Write behavior
  a_wp_adv:      assert property ( en && we |=> wp == $past(wp) + 3'd1 );
  a_mem_write:   assert property ( en && we |=> mem[$past(wp)] == $past(din) );

  // Read behavior: data transform and rp advance (uses pre-state mem/rp/mode)
  a_dout_xform:  assert property (
                    en && re |=> 
                      ( ($past(mode)==2'b00 && dout == { $past(mem[$past(rp[2:0])])[15:0], 4'h0 }) ||
                        ($past(mode)==2'b01 && dout == { $past(mem[$past(rp[2:0])])[17:0], 2'h0 }) ||
                        ($past(mode)==2'b10 && dout ==   $past(mem[$past(rp[2:0])])[19:0]      ) )
                  );
  a_rp_adv:      assert property ( en && re |=> 
                                   rp[2:0] == ($past(rp[2:0]) + (($past(mode)==2'b00) ? 3'd1 : 3'd2)) );

  // rp MSB must not be used as part of memory address on read (catch out-of-range)
  a_rp_addr_ok:  assert property ( en && re |-> $past(rp[3])==1'b0 );

  // No unintended changes when enables are low
  a_wp_hold:     assert property ( en && !we |=> wp == $past(wp) );
  a_rp_hold:     assert property ( en && !re |=> rp == $past(rp) );
  a_dout_hold:   assert property ( en && !re |=> dout == $past(dout) );

  // Coverage
  c_mode0:       cover property ( en && re && mode==2'b00 );
  c_mode1:       cover property ( en && re && mode==2'b01 );
  c_mode2:       cover property ( en && re && mode==2'b10 );

  c_simul_wr_rd: cover property ( en && we && re );
  c_full:        cover property ( we && ({1'b0,wp}==rp) && full );
  c_empty:       cover property ( empty );

  c_wp_wrap:     cover property ( en && we && $past(wp)==3'd7 && wp==3'd0 );
  c_rp_wrap_m0:  cover property ( en && re && $past(mode)==2'b00 && $past(rp[2:0])==3'd7 &&
                                   rp[2:0]==3'd0 );
  c_rp_wrap_m12: cover property ( en && re && ($past(mode)!=2'b00) &&
                                   ($past(rp[2:0])>=3'd6) &&
                                   rp[2:0]==(($past(rp[2:0])+3'd2)&3'h7) );

  c_status0:     cover property ( status==2'd0 );
  c_status1:     cover property ( status==2'd1 );
  c_status2:     cover property ( status==2'd2 );
  c_status3:     cover property ( status==2'd3 );
endmodule

// Bind to DUT
bind audio_fifo audio_fifo_sva i_audio_fifo_sva (
  .clk(clk), .rst(rst), .en(en), .we(we), .re(re),
  .mode(mode), .din(din), .dout(dout), .status(status), .full(full), .empty(empty),
  .wp(wp), .rp(rp), .status_reg(status_reg), .dout_reg(dout_reg), .empty_reg(empty_reg), .mem(mem)
);