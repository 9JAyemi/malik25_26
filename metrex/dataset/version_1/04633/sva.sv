// SVA for crossbar36
// Concise, high-quality checks + essential coverage

module crossbar36_sva
(
  input logic                  clk, reset, clear,
  input logic                  cross,
  input logic [35:0]           data0_i, input logic src0_rdy_i, input logic dst0_rdy_o,
  input logic [35:0]           data1_i, input logic src1_rdy_i, input logic dst1_rdy_o,
  input logic [35:0]           data0_o, input logic src0_rdy_o, input logic dst0_rdy_i,
  input logic [35:0]           data1_o, input logic src1_rdy_o, input logic dst1_rdy_i,
  // internal DUT state/nets
  input logic                  cross_int,
  input logic                  active0, active1,
  input logic                  active0_next, active1_next
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset || clear);

  // Combinational mapping checks
  assert property (cross_int==1'b0
                   |-> (data0_o==data0_i && data1_o==data1_i
                        && src0_rdy_o==src0_rdy_i && src1_rdy_o==src1_rdy_i
                        && dst0_rdy_o==dst0_rdy_i && dst1_rdy_o==dst1_rdy_i));

  assert property (cross_int==1'b1
                   |-> (data0_o==data1_i && data1_o==data0_i
                        && src0_rdy_o==src1_rdy_i && src1_rdy_o==src0_rdy_i
                        && dst0_rdy_o==dst1_rdy_i && dst1_rdy_o==dst0_rdy_i));

  // Active flag update rules (next-cycle semantics)
  // handshake0/1 occur when source ready and selected destination ready
  assert property ( (src0_rdy_i & (cross_int ? dst1_rdy_i : dst0_rdy_i))
                    |=> active0 == ~ $past(data0_i[33]) );
  assert property ( !(src0_rdy_i & (cross_int ? dst1_rdy_i : dst0_rdy_i))
                    |=> active0 == $past(active0) );

  assert property ( (src1_rdy_i & (cross_int ? dst0_rdy_i : dst1_rdy_i))
                    |=> active1 == ~ $past(data1_i[33]) );
  assert property ( !(src1_rdy_i & (cross_int ? dst0_rdy_i : dst1_rdy_i))
                    |=> active1 == $past(active1) );

  // cross_int update protocol: may change only when both next-actives are 0
  assert property ( $changed(cross_int) |-> $past(~active0_next & ~active1_next) );
  assert property ( (~active0_next & ~active1_next) |=> cross_int == $past(cross) );
  assert property ( (active0_next | active1_next)   |=> cross_int == $past(cross_int) );

  // Synchronous reset/clear effects (next cycle)
  assert property (@cb (reset || clear) |=> (active0==0 && active1==0 && cross_int==0));

  // Coverage: exercise straight and cross handshakes and cross_int flips
  cover property (@cb disable iff (reset || clear)
                  cross_int==1'b0 && (src0_rdy_i & dst0_rdy_i));
  cover property (@cb disable iff (reset || clear)
                  cross_int==1'b1 && (src0_rdy_i & dst1_rdy_i));
  cover property (@cb disable iff (reset || clear)
                  cross_int==1'b0 && (src1_rdy_i & dst1_rdy_i));
  cover property (@cb disable iff (reset || clear)
                  cross_int==1'b1 && (src1_rdy_i & dst0_rdy_i));

  cover property (@cb disable iff (reset || clear)
                  (~active0_next & ~active1_next) && (cross_int==0) && cross ##1 (cross_int==1));
  cover property (@cb disable iff (reset || clear)
                  (~active0_next & ~active1_next) && (cross_int==1) && !cross ##1 (cross_int==0));

  // Cover both values captured into active flags
  cover property (@cb disable iff (reset || clear)
                  (src0_rdy_i & (cross_int ? dst1_rdy_i : dst0_rdy_i) & ~data0_i[33]) ##1 (active0==1));
  cover property (@cb disable iff (reset || clear)
                  (src0_rdy_i & (cross_int ? dst1_rdy_i : dst0_rdy_i) &  data0_i[33]) ##1 (active0==0));

  cover property (@cb disable iff (reset || clear)
                  (src1_rdy_i & (cross_int ? dst0_rdy_i : dst1_rdy_i) & ~data1_i[33]) ##1 (active1==1));
  cover property (@cb disable iff (reset || clear)
                  (src1_rdy_i & (cross_int ? dst0_rdy_i : dst1_rdy_i) &  data1_i[33]) ##1 (active1==0));

endmodule

bind crossbar36 crossbar36_sva sva (.*);