// SVA for jt12_amp and jt12_amp_stereo
// Focused, concise, high-quality checks and coverage

// ------------------------- jt12_amp SVA -------------------------
module jt12_amp_sva (
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 sample,
  input  logic signed [13:0]   pre,
  input  logic        [2:0]    volume,
  input  logic signed [15:0]   post
);

  // Reference model (saturating) for all volume levels
  function automatic logic signed [15:0] amp_ref(input logic signed [13:0] pre_i,
                                                 input logic        [2:0]  vol_i);
    int factor;
    int prod;
    begin
      unique case (vol_i)
        3'd0: factor = 1;
        3'd1: factor = 2;
        3'd2: factor = 4;
        3'd3: factor = 4;
        3'd4: factor = 6;
        3'd5: factor = 8;
        3'd6: factor = 12;
        default: factor = 16; // 3'd7
      endcase
      prod = $signed(pre_i) * factor;
      if (prod >  32767)   amp_ref = 16'sh7FFF;
      else if (prod < -32768) amp_ref = 16'sh8000;
      else                 amp_ref = logic'(prod[15:0]);
    end
  endfunction

  // Basic protocol/functional checks
  // Reset drives post to 0 by next clock, and stays 0 while rst is held
  assert property (@(posedge clk) rst |=> post == 16'sd0);
  assert property (@(posedge clk) rst && $past(rst) |-> post == 16'sd0);

  // No update when sample==0
  assert property (@(posedge clk) disable iff (rst) !sample |-> $stable(post));

  // Inputs must be known when sampling
  assert property (@(posedge clk) disable iff (rst) sample |-> !$isunknown({pre,volume}));

  // Functional equivalence to golden model (post updates next cycle)
  assert property (@(posedge clk) disable iff (rst)
                   sample |=> post == amp_ref($past(pre), $past(volume)));

  // For volume 0..3 there is no saturation and sign must be preserved
  assert property (@(posedge clk) disable iff (rst)
                   sample && (volume<=3) |=> post[15] == $past(pre[13]));

  // Explicit check that vol 2 and vol 3 are equivalent to pre<<<2
  assert property (@(posedge clk) disable iff (rst)
                   sample && (volume==3'd2) |=> post == ($signed($past(pre)) <<< 2));
  assert property (@(posedge clk) disable iff (rst)
                   sample && (volume==3'd3) |=> post == ($signed($past(pre)) <<< 2));

  // Coverage: hit all volume settings
  genvar v;
  generate
    for (v=0; v<8; v++) begin : COV_VOL
      cover property (@(posedge clk) disable iff (rst) sample && (volume==v[2:0]));
    end
  endgenerate

  // Coverage: saturations on both sides for the saturating modes
  cover property (@(posedge clk) disable iff (rst)
                  sample && (volume>=3'd4) && (amp_ref(pre,volume)==16'sh7FFF));
  cover property (@(posedge clk) disable iff (rst)
                  sample && (volume>=3'd4) && (amp_ref(pre,volume)==16'sh8000));

endmodule

bind jt12_amp jt12_amp_sva amp_chk (
  .clk(clk), .rst(rst), .sample(sample), .pre(pre), .volume(volume), .post(post)
);

// ---------------------- jt12_amp_stereo SVA ----------------------
module jt12_amp_stereo_sva (
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  sample,
  input  logic          [5:0]   psg,
  input  logic                  enable_psg,
  input  logic signed  [11:0]   fmleft,
  input  logic signed  [11:0]   fmright,
  input  logic          [2:0]   volume,
  input  logic signed  [15:0]   postleft,
  input  logic signed  [15:0]   postright,
  // internal wires
  input  logic signed  [13:0]   preleft,
  input  logic signed  [13:0]   preright,
  input  logic signed   [8:0]   psg_dac,
  input  logic signed  [12:0]   psg_sum
);

  // Reuse golden amp
  function automatic logic signed [15:0] amp_ref(input logic signed [13:0] pre_i,
                                                 input logic        [2:0]  vol_i);
    int factor;
    int prod;
    begin
      unique case (vol_i)
        3'd0: factor = 1;
        3'd1: factor = 2;
        3'd2: factor = 4;
        3'd3: factor = 4;
        3'd4: factor = 6;
        3'd5: factor = 8;
        3'd6: factor = 12;
        default: factor = 16;
      endcase
      prod = $signed(pre_i) * factor;
      if (prod >  32767)   amp_ref = 16'sh7FFF;
      else if (prod < -32768) amp_ref = 16'sh8000;
      else                 amp_ref = logic'(prod[15:0]);
    end
  endfunction

  // Reference for PSG path
  function automatic logic signed [8:0]  psg_dac_ref(input logic [5:0] psg_i);
    psg_dac_ref = $signed({1'b0,psg_i}) <<< 3;
  endfunction

  function automatic logic signed [12:0] psg_sum_ref(input logic [5:0] psg_i,
                                                     input logic       en_i);
    logic signed [8:0] d = psg_dac_ref(psg_i);
    psg_sum_ref = en_i ? {2'b00, d, 1'b0} : 13'sd0;
  endfunction

  function automatic logic signed [12:0] fm_ext2(input logic signed [11:0] fm);
    fm_ext2 = { fm[11], fm, 1'b0 }; // sign-extend then *2
  endfunction

  // Structural checks for internal combinational paths
  assert property (@(posedge clk) psg_dac == psg_dac_ref(psg));
  assert property (@(posedge clk) psg_sum == psg_sum_ref(psg, enable_psg));
  assert property (@(posedge clk) preleft  == $signed(fm_ext2(fmleft))  + psg_sum);
  assert property (@(posedge clk) preright == $signed(fm_ext2(fmright)) + psg_sum);

  // Outputs update only on sample and match amp_ref(next cycle)
  assert property (@(posedge clk) disable iff (rst) !sample |-> $stable({postleft,postright}));
  assert property (@(posedge clk) disable iff (rst)
                   sample |=> postleft  == amp_ref($past(preleft),  $past(volume)));
  assert property (@(posedge clk) disable iff (rst)
                   sample |=> postright == amp_ref($past(preright), $past(volume)));

  // Inputs known when sampling
  assert property (@(posedge clk) disable iff (rst)
                   sample |-> !$isunknown({fmleft,fmright,psg,enable_psg,volume}));

  // Symmetry: equal FM produces equal outputs
  assert property (@(posedge clk) disable iff (rst)
                   sample && (fmleft==fmright) |=> postleft==postright);

  // Coverage
  cover property (@(posedge clk) disable iff (rst) sample && !enable_psg);
  cover property (@(posedge clk) disable iff (rst) sample &&  enable_psg);
  cover property (@(posedge clk) disable iff (rst)
                  sample && (fmleft==fmright) |=> postleft==postright);

  // Cover saturations on either channel
  cover property (@(posedge clk) disable iff (rst)
                  sample && (volume>=3'd4) &&
                  (amp_ref(preleft,volume)==16'sh7FFF || amp_ref(preleft,volume)==16'sh8000));
  cover property (@(posedge clk) disable iff (rst)
                  sample && (volume>=3'd4) &&
                  (amp_ref(preright,volume)==16'sh7FFF || amp_ref(preright,volume)==16'sh8000));

endmodule

bind jt12_amp_stereo jt12_amp_stereo_sva stereo_chk (
  .clk(clk), .rst(rst), .sample(sample),
  .psg(psg), .enable_psg(enable_psg),
  .fmleft(fmleft), .fmright(fmright), .volume(volume),
  .postleft(postleft), .postright(postright),
  .preleft(preleft), .preright(preright), .psg_dac(psg_dac), .psg_sum(psg_sum)
);