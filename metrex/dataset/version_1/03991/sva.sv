// SystemVerilog Assertions for MODE0 and Online_test2

// --- MODE0 combinational checker (bound into every MODE0) ---
module MODE0_sva(
  input  logic [15:0]        a, b,
  input  logic signed [17:0] outR, outI
);
  logic signed [7:0]  aR = $signed(a[15:8]);
  logic signed [7:0]  aI = $signed(a[7:0]);
  logic signed [7:0]  bR = $signed(b[15:8]);
  logic signed [7:0]  bI = $signed(b[7:0]);
  logic signed [17:0] r1 = aR*bR, r2 = aI*bI, i1 = aR*bI, i2 = aI*bR;

  always @* begin
    assert (outR == r1 - r2) else $error("MODE0 outR mismatch");
    assert (outI == i1 + i2) else $error("MODE0 outI mismatch");
  end
endmodule

bind MODE0 MODE0_sva u_mode0_sva(.a(a), .b(b), .outR(outR), .outI(outI));


// --- Online_test2 protocol/timing checker ---
module Online_test2_sva(
  input  logic         clk,
  input  logic         rst_n,
  input  logic         in_valid,
  input  logic [15:0]  in,
  input  logic         in_mode,
  input  logic         out_valid,
  input  logic [35:0]  out,

  input  logic         inMod,
  input  logic         rstState,
  input  logic [5:0]   cnt1, cnt2,
  input  logic [15:0]  a0, a1, b0, b1,

  input  logic signed [17:0] m00R,m00I,m01R,m01I,m10R,m10I,m11R,m11I,
  input  logic signed [17:0] rea, img,

  input  logic [35:0]  o0,o2,o4,o6,o8,o10
);
  default clocking cb @(posedge clk); endclocking
  `define RST (rst_n || rstState)

  // Inputs well-defined and internal mirror
  ap_inmode_known:    assert property ( !$isunknown(in_mode) );
  ap_inMod_mirrors:   assert property ( !`RST |-> (inMod == in_mode) );

  // Reset behavior
  ap_reset_clears:    assert property ( (rst_n || rstState) |-> (out_valid==0 && out==0 && cnt1==0 && cnt2==0) );

  // cnt1 increments only with in_valid, otherwise holds (outside reset)
  ap_cnt1_inc:        assert property ( disable iff(`RST) in_valid |-> cnt1 == $past(cnt1)+1 );
  ap_cnt1_hold:       assert property ( disable iff(`RST) !in_valid |-> cnt1 == $past(cnt1) );

  // Input capture order while in_valid
  ap_cap_a0:          assert property ( disable iff(`RST) in_valid && $past(cnt1)==0 |-> a0 == in );
  ap_cap_a1:          assert property ( disable iff(`RST) in_valid && $past(cnt1)==1 |-> a1 == in );
  ap_cap_b0:          assert property ( disable iff(`RST) in_valid && $past(cnt1)==2 |-> b0 == in );
  ap_cap_b1:          assert property ( disable iff(`RST) in_valid && $past(cnt1)==3 |-> b1 == in );

  // cnt2 advances only when output phase condition is met
  ap_cnt2_inc:        assert property ( disable iff(`RST) (cnt1>0 && !in_valid) |-> cnt2 == $past(cnt2)+1 );
  ap_cnt2_hold:       assert property ( disable iff(`RST) !(cnt1>0 && !in_valid) |-> cnt2 == $past(cnt2) );

  // out_valid only during output phase
  ap_outv_phase:      assert property ( out_valid |-> (!in_valid && cnt1>0) );

  // Mode 0: three output beats then done
  ap_m0_1:            assert property ( disable iff(`RST) (inMod==0 && cnt2==1) |-> (out_valid && out[35:18]==m00R && out[17:0]==m00I) );
  ap_m0_2_vals:       assert property ( disable iff(`RST) (inMod==0 && cnt2==2) |-> (out_valid && out[35:18]==rea  && out[17:0]==img) );
  ap_m0_2_sumR:       assert property ( disable iff(`RST) (inMod==0 && cnt2==2) |-> (rea == $signed(m01R)+$signed(m10R)) );
  ap_m0_2_sumI:       assert property ( disable iff(`RST) (inMod==0 && cnt2==2) |-> (img == $signed(m01I)+$signed(m10I)) );
  ap_m0_3:            assert property ( disable iff(`RST) (inMod==0 && cnt2==3) |-> (out_valid && out[35:18]==m11R && out[17:0]==m11I) );
  ap_m0_done:         assert property ( disable iff(`RST) (inMod==0 && cnt2>=4) |-> (!out_valid && rstState) );

  // Mode 1: histogram outputs ordering and stability
  ap_m1_2:            assert property ( disable iff(`RST) (inMod==1 && cnt2==2) |-> (out_valid && out==o0) );
  ap_m1_3:            assert property ( disable iff(`RST) (inMod==1 && cnt2==3) |-> (out_valid && out==o2) );
  ap_m1_4:            assert property ( disable iff(`RST) (inMod==1 && cnt2==4) |-> (out_valid && out==o4) );
  ap_m1_5:            assert property ( disable iff(`RST) (inMod==1 && cnt2==5) |-> (out_valid && out==o6) );
  ap_m1_6:            assert property ( disable iff(`RST) (inMod==1 && cnt2==6) |-> (out_valid && out==o8) );
  ap_m1_7:            assert property ( disable iff(`RST) (inMod==1 && cnt2==7) |-> (out_valid && out==o10) );
  ap_m1_stable:       assert property ( disable iff(`RST) (inMod==1 && cnt2 inside {[2:7]}) |-> ($stable(o0) && $stable(o2) && $stable(o4) && $stable(o6) && $stable(o8) && $stable(o10)) );
  ap_m1_done:         assert property ( disable iff(`RST) (inMod==1 && cnt2>=8) |-> (!out_valid && rstState) );

  // Functional coverage
  cv_mode0:           cover  property ( disable iff(`RST)
                          (inMod==0, in_valid [*4]) ##1 !in_valid
                          ##1 (cnt2==1 && out_valid)
                          ##1 (cnt2==2 && out_valid)
                          ##1 (cnt2==3 && out_valid) );

  cv_mode1:           cover  property ( disable iff(`RST)
                          (inMod==1, in_valid [*1]) ##1 !in_valid
                          ##1 (cnt2==2 && out_valid)
                          ##[3:5] 1'b1
                          ##1 (cnt2==7 && out_valid) );

  cv_rstState_pulse:  cover  property ( rstState ##1 !rstState );
endmodule

bind Online_test2 Online_test2_sva u_online_test2_sva(
  .clk(clk), .rst_n(rst_n), .in_valid(in_valid), .in(in), .in_mode(in_mode),
  .out_valid(out_valid), .out(out),
  .inMod(inMod), .rstState(rstState), .cnt1(cnt1), .cnt2(cnt2),
  .a0(a0), .a1(a1), .b0(b0), .b1(b1),
  .m00R(m00R), .m00I(m00I), .m01R(m01R), .m01I(m01I), .m10R(m10R), .m10I(m10I), .m11R(m11R), .m11I(m11I),
  .rea(rea), .img(img),
  .o0(o0), .o2(o2), .o4(o4), .o6(o6), .o8(o8), .o10(o10)
);