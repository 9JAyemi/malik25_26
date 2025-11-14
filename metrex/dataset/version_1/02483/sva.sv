// SVA for crossbar36
// Bind into DUT to access internals (active0/1, cross_int, active*_next)
module crossbar36_sva;

  // Short-hands
  wire hand0 = src0_rdy_i & dst0_rdy_o;
  wire hand1 = src1_rdy_i & dst1_rdy_o;

  // Reset/clear behavior
  assert property (@(posedge clk) (reset || clear) |=> (active0==0 && active1==0 && cross_int==0));

  // active0 update semantics
  assert property (@(posedge clk) disable iff (reset || clear)
                   hand0 |=> active0 == ~$past(data0_i[33]));
  assert property (@(posedge clk) disable iff (reset || clear)
                   !hand0 |=> active0 == $past(active0));

  // active1 update semantics
  assert property (@(posedge clk) disable iff (reset || clear)
                   hand1 |=> active1 == ~$past(data1_i[33]));
  assert property (@(posedge clk) disable iff (reset || clear)
                   !hand1 |=> active1 == $past(active1));

  // cross_int update semantics: capture when both next-actives are 0, else hold
  assert property (@(posedge clk) disable iff (reset || clear)
                   (~active0_next & ~active1_next) |=> cross_int == $past(cross));
  assert property (@(posedge clk) disable iff (reset || clear)
                   (active0_next | active1_next) |=> cross_int == $past(cross_int));

  // Output mux correctness (same-cycle mapping)
  assert property (@(posedge clk)
                   (cross_int==1'b0) |-> (data0_o==data0_i && data1_o==data1_i &&
                                          src0_rdy_o==src0_rdy_i && src1_rdy_o==src1_rdy_i &&
                                          dst0_rdy_o==dst0_rdy_i && dst1_rdy_o==dst1_rdy_i));
  assert property (@(posedge clk)
                   (cross_int==1'b1) |-> (data0_o==data1_i && data1_o==data0_i &&
                                          src0_rdy_o==src1_rdy_i && src1_rdy_o==src0_rdy_i &&
                                          dst0_rdy_o==dst1_rdy_i && dst1_rdy_o==dst0_rdy_i));

  // No Xs on key state after reset/clear deasserted
  assert property (@(posedge clk) disable iff (reset || clear)
                   !$isunknown({cross_int,active0,active1}));

  // Coverage
  // Capture cross_int changes when allowed
  cover property (@(posedge clk) disable iff (reset || clear)
                  (~active0_next & ~active1_next) && (cross==1) ##1 (cross_int==1));
  cover property (@(posedge clk) disable iff (reset || clear)
                  (~active0_next & ~active1_next) && (cross==0) ##1 (cross_int==0));

  // Hold cross_int when update is disallowed
  cover property (@(posedge clk) disable iff (reset || clear)
                  (active0_next | active1_next) && (cross != cross_int) ##1 (cross_int==$past(cross_int)));

  // Exercise active0/1 set/clear via data[33]
  cover property (@(posedge clk) disable iff (reset || clear)
                  hand0 && (data0_i[33]==0) ##1 (active0==1));
  cover property (@(posedge clk) disable iff (reset || clear)
                  hand0 && (data0_i[33]==1) ##1 (active0==0));
  cover property (@(posedge clk) disable iff (reset || clear)
                  hand1 && (data1_i[33]==0) ##1 (active1==1));
  cover property (@(posedge clk) disable iff (reset || clear)
                  hand1 && (data1_i[33]==1) ##1 (active1==0));

endmodule

bind crossbar36 crossbar36_sva sv_inst();