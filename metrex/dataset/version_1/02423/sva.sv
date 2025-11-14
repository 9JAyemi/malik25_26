// SVA for top_module and its sub-blocks (concise, high-quality checks)
module top_module_sva
(
  input  logic        clk, reset,
  input  logic [7:0]  a,b,c,d,
  input  logic [7:0]  in_hi,in_lo, min_out,
  input  logic [15:0] comb_out, final_out,
  input  logic        select
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Helpers
  function automatic [7:0] f_min2(input [7:0] x,y); f_min2 = (x<=y)? x : y; endfunction
  function automatic [7:0] f_min4(input [7:0] ia,ib,ic,id);
    automatic [7:0] m1,m2;
    begin m1=f_min2(ia,ib); m2=f_min2(ic,id); f_min4=f_min2(m1,m2); end
  endfunction

  // minimum_circuit checks
  ap_min_value:    assert property (min_out == f_min4(a,b,c,d));
  ap_min_le_all:   assert property ((min_out<=a) && (min_out<=b) && (min_out<=c) && (min_out<=d));
  ap_min_known:    assert property (!($isunknown({a,b,c,d})) |-> !($isunknown(min_out)));

  // combinational_circuit checks
  ap_comb_pack:    assert property (comb_out == {in_hi,in_lo});
  ap_comb_known:   assert property (!($isunknown({in_hi,in_lo})) |-> !($isunknown(comb_out)));

  // additive_control_logic checks
  ap_add_mode:     assert property ((select==1'b0) |-> (final_out == ({8'h00,min_out} + comb_out)));
  ap_sub_mode:     assert property ((select==1'b1) |-> (final_out == ({8'h00,min_out} - comb_out)));
  ap_final_known:  assert property (!($isunknown({select,min_out,comb_out})) |-> !($isunknown(final_out)));
  ap_stability:    assert property ($stable({select,min_out,comb_out}) |-> $stable(final_out));

  // Functional coverage (concise)
  cv_sel0:         cover property (select==1'b0);
  cv_sel1:         cover property (select==1'b1);
  cv_sel_toggle:   cover property (select==1 ##1 select==0);

  cv_min_a_unique: cover property ((a<b && a<c && a<d) && (min_out==a));
  cv_min_b_unique: cover property ((b<a && b<c && b<d) && (min_out==b));
  cv_min_c_unique: cover property ((c<a && c<b && c<d) && (min_out==c));
  cv_min_d_unique: cover property ((d<a && d<b && d<c) && (min_out==d));
  cv_min_tie_ab:   cover property ((a==b) && (a<=c) && (a<=d) && (min_out==a));
  cv_min_tie_cd:   cover property ((c==d) && (c<=a) && (c<=b) && (min_out==c));

  cv_comb_zeros:   cover property (in_hi==8'h00 && in_lo==8'h00 && comb_out==16'h0000);
  cv_comb_ones:    cover property (in_hi==8'hFF && in_lo==8'hFF && comb_out==16'hFFFF);

  cv_add_overflow: cover property ((select==1'b0) && (({8'h00,min_out} + comb_out) < comb_out));
  cv_sub_underflow:cover property ((select==1'b1) && ({8'h00,min_out} < comb_out));

endmodule

bind top_module top_module_sva u_top_module_sva
(
  .clk(clk),
  .reset(reset),
  .a(a), .b(b), .c(c), .d(d),
  .in_hi(in_hi), .in_lo(in_lo),
  .min_out(min_out),
  .comb_out(comb_out),
  .final_out(final_out),
  .select(select)
);