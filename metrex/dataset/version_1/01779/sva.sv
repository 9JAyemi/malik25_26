// Bind this SVA module to the DUT: bind control control_sva svac(.dut(dut));
module control_sva (control dut);

  default clocking cb @ (posedge dut.clk); endclocking
  default disable iff (!dut.rstn);

  // Constants
  localparam int CYC_MAX     = 6'd40;
  localparam int CYC_SET     = 6'd5;
  localparam int CYC_CLR     = 6'd1;
  localparam int FIN_CYC     = 6'd10;
  localparam int BLK_STOP    = 7'd64;
  localparam int BLK_MAX     = 7'd65;

  // Asynchronous reset sanity (hold low during reset)
  a_reset_clear: assert property (!dut.rstn |-> (dut.newblock==0 && dut.gxgyrun==0 &&
                                                 dut.counterrun1==0 && dut.counterrun2==0 &&
                                                 dut.finish==0 && dut.cyclecnt==0 && dut.blockcnt==0));

  // Ranges
  a_cyclecnt_range: assert property (dut.cyclecnt <= CYC_MAX);
  a_blockcnt_range: assert property (dut.blockcnt <= BLK_MAX);

  // newblock is exactly when cyclecnt==40 (1-cycle pulse)
  a_newblock_set:   assert property ($past(dut.cyclecnt)==CYC_MAX |-> dut.newblock);
  a_newblock_only:  assert property (dut.newblock |-> $past(dut.cyclecnt)==CYC_MAX);

  // cyclecnt behavior
  a_cyc_wrap_or_fin: assert property ( ($past(dut.cyclecnt)==CYC_MAX || $past(dut.finish)) |-> dut.cyclecnt==6'd0 );
  a_cyc_inc:         assert property ( $past(dut.enable) && $past(dut.cyclecnt)!=CYC_MAX && !$past(dut.finish)
                                       |-> dut.cyclecnt == $past(dut.cyclecnt)+1 );
  a_cyc_hold:        assert property ( !$past(dut.enable) && $past(dut.cyclecnt)!=CYC_MAX && !$past(dut.finish)
                                       |-> dut.cyclecnt == $past(dut.cyclecnt) );

  // blockcnt behavior
  a_blk_reset_on_fin: assert property ( $past(dut.finish) |-> dut.blockcnt==7'd0 );
  a_blk_inc_on_wrap:  assert property ( $past(dut.enable) && $past(dut.cyclecnt)==CYC_MAX
                                        |-> dut.blockcnt == $past(dut.blockcnt)+1 );
  a_blk_hold_other:   assert property ( !($past(dut.enable) && $past(dut.cyclecnt)==CYC_MAX) && !$past(dut.finish)
                                        |-> dut.blockcnt == $past(dut.blockcnt) );

  // gxgyrun behavior
  a_gx_set_at5:       assert property ( $past(dut.cyclecnt)==CYC_SET && $past(dut.blockcnt)!=BLK_STOP |-> dut.gxgyrun );
  a_gx_not_set_blk64: assert property ( $past(dut.cyclecnt)==CYC_SET && $past(dut.blockcnt)==BLK_STOP |-> !dut.gxgyrun );
  a_gx_clear_at1:     assert property ( $past(dut.cyclecnt)==CYC_CLR |-> !dut.gxgyrun );
  a_gx_holds_until1:  assert property ( $past(dut.gxgyrun) && $past(dut.cyclecnt)!=CYC_CLR |-> dut.gxgyrun );

  // counterrun pipelines
  a_cr1_delay: assert property ( dut.counterrun1 == $past(dut.gxgyrun) );
  a_cr2_delay: assert property ( dut.counterrun2 == $past(dut.counterrun1) );

  // finish behavior
  a_fin_set:        assert property ( $past(dut.blockcnt)==BLK_MAX && $past(dut.cyclecnt)==FIN_CYC |-> dut.finish );
  a_fin_clear_when_en_no_set: assert property ( $past(dut.enable) &&
                                               !($past(dut.blockcnt)==BLK_MAX && $past(dut.cyclecnt)==FIN_CYC)
                                               |-> !dut.finish );
  a_fin_rose_cause: assert property ( !$past(dut.finish) && dut.finish
                                      |-> $past(dut.blockcnt)==BLK_MAX && $past(dut.cyclecnt)==FIN_CYC );

  // Coverage
  c_newblock: cover property ( $past(dut.cyclecnt)==CYC_MAX && dut.newblock );
  c_finish:   cover property ( $past(dut.blockcnt)==BLK_MAX && $past(dut.cyclecnt)==FIN_CYC && dut.finish );
  c_gx_64_65: cover property ( (dut.cyclecnt==CYC_SET && dut.blockcnt==BLK_STOP && !dut.gxgyrun)
                               ##[1:$] (dut.cyclecnt==CYC_SET && dut.blockcnt==BLK_MAX && dut.gxgyrun) );

endmodule