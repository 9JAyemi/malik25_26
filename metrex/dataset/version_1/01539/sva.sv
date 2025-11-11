// SVA for jt10_adpcm_comb
// Bind into DUT scope to access internals
module jt10_adpcm_comb_sva;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // -------------------------
  // Reset value checks (async reset low)
  // -------------------------
  // Combinational path is forced to these values while rst_n=0
  assert property (@(posedge clk)
    !rst_n |-> ( x2==16'd0 && step2==15'd127 &&
                 x3==16'd0 && step3==17'd127 &&
                 x4==16'd0 && step4==17'd127 &&
                 x5==16'd0 && step5==17'd127 &&
                 x6==16'd0 && step6==15'd127 &&
                 d2==4'd0 && d3==16'd0 && d4==16'd0 &&
                 sign2==1'b0 && sign3==1'b0 && sign4==1'b0 && sign5==1'b0 &&
                 chon2==1'b0 && chon3==1'b0 && chon4==1'b0 && chon5==1'b0 &&
                 pcm==16'd0));

  // Sequential regs reset
  assert property (@(posedge clk)
    !rst_n |-> (x1==16'd0 && step1==15'd127 && d1==4'd0 && data1==4'd0));

  // -------------------------
  // Hold/update behavior on cen
  // -------------------------
  assert property (!cen |-> $stable({x1,step1,d1,data1}));

  assert property (cen |-> ( x1    == $past(x6)
                          && step1 == $past(step6)
                          && d1    == {$past(data[2:0]),1'b1}
                          && data1 == $past(data)));

  // -------------------------
  // PCM mirroring
  // -------------------------
  assert property (pcm == x2);
  assert property (x2 == x1);

  // -------------------------
  // Stage 1: immediate comb relationships
  // -------------------------
  assert property (d2==d1 && sign2==data1[3] && data2==data1
                   && step2==step1 && chon2==chon);

  // step_val decode
  assert property ( step_val ==
                    (d2[3]==1'b0 ? 8'd57 :
                     (d2[2:1]==2'b00 ? 8'd77 :
                      d2[2:1]==2'b01 ? 8'd102 :
                      d2[2:1]==2'b10 ? 8'd128 : 8'd153)));

  // Multiplies and shift
  assert property (d2l == d2 * step2);
  assert property (step2l == step_val * step2);
  assert property (d3 == d2l[18:3]);

  // -------------------------
  // Stage 2
  // -------------------------
  assert property (sign3==sign2 && x3==x2 && step3==step2l[22:6] && chon3==chon2);

  // -------------------------
  // Stage 3/4 propagation
  // -------------------------
  assert property (d4 == (sign3 ? (~d3 + 16'd1) : d3));
  assert property (sign4==sign3 && signEqu4==(sign3==x3[15]) && x4==x3 && step4==step3 && chon4==chon3);

  // -------------------------
  // Stage 5 pre-saturation
  // -------------------------
  assert property (x5 == $signed(x4) + $signed(d4));
  assert property (sign5==sign4 && signEqu5==signEqu4 && step5==step4 && chon5==chon4);

  // chon pipeline integrity
  assert property (chon5 == chon);

  // -------------------------
  // Saturation and step clamp
  // -------------------------
  // chon low forces zero/127
  assert property (!chon5 |-> (x6==16'd0 && step6==15'd127));

  // Saturate when required
  assert property ( chon5 && signEqu5 && (sign5 != x5[15])
                    |-> x6 == (sign5 ? 16'h8000 : 16'h7FFF));

  // No saturation otherwise
  assert property ( chon5 && !(signEqu5 && (sign5 != x5[15]))
                    |-> x6 == x5);

  // Step clamp range
  assert property ( chon5 && (step5 < 15'd127)   |-> step6 == 15'd127);
  assert property ( chon5 && (step5 > 15'd24576) |-> step6 == 15'd24576);
  assert property ( chon5 && (step5 >= 15'd127) && (step5 <= 15'd24576)
                    |-> step6 == step5[14:0]);

  // -------------------------
  // X/Z checks (active when out of reset)
  // -------------------------
  assert property (!$isunknown({x1,x2,x3,x4,x5,x6,
                                step1,step2,step3,step4,step5,step6,
                                d1,d2,d3,d4,sign2,sign3,sign4,sign5,
                                chon2,chon3,chon4,chon5,step_val,d2l,step2l,pcm})));

  // -------------------------
  // Coverage
  // -------------------------
  // First update after reset
  cover property ( $fell(rst_n) ##1 rst_n ##1 cen && (x1 == $past(x6)));

  // Saturation to +MAX and -MAX
  cover property ( chon5 && signEqu5 && (sign5==1'b0) && (sign5 != x5[15]) && x6==16'h7FFF);
  cover property ( chon5 && signEqu5 && (sign5==1'b1) && (sign5 != x5[15]) && x6==16'h8000);

  // Step clamp low and high
  cover property ( chon5 && (step5 < 15'd127)   && (step6==15'd127));
  cover property ( chon5 && (step5 > 15'd24576) && (step6==15'd24576));

  // No-saturation normal update
  cover property ( chon5 && !(signEqu5 && (sign5 != x5[15])) && (x6==x5));

  // chon low path
  cover property (!chon && (x6==16'd0) && (step6==15'd127));

  // step_val decode categories
  cover property (d2[3]==1'b0 && step_val==8'd57);
  cover property (d2[3:1]==3'b100 && step_val==8'd77);
  cover property (d2[3:1]==3'b101 && step_val==8'd102);
  cover property (d2[3:1]==3'b110 && step_val==8'd128);
  cover property (d2[3:1]==3'b111 && step_val==8'd153);

endmodule

bind jt10_adpcm_comb jt10_adpcm_comb_sva sva_inst();