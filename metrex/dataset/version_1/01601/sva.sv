Below is a concise SVA bind file that targets the key behaviors of this design: reset values, MPU write protocol and field masking, register/output mappings, timing generator counter/MA behavior, HS/VS pulse control, display timing, and the video_offset_o composition. It uses bind modules for crtc6845, mpu_if, and crtc_gen. Focus is on high-signal-value checks with minimal redundancy.


// ==========================================================
// Bind: top (crtc6845) – video_offset_o composition
// ==========================================================
module crtc6845_sva
(
  input  logic        I_CLK,
  input  logic        I_RSTn,
  input  logic [15:0] video_offset_o,
  input  logic [13:0] W_Msa
);
  default clocking cb @(posedge I_CLK); endclocking

  // video_offset_o constant fields always match spec
  assert property (cb disable iff (!I_RSTn)
                   (video_offset_o[15:11] == 5'b11000) && (video_offset_o[0] == 1'b0));

  // video_offset_o middle field matches MSA[9:0]
  assert property (cb disable iff (!I_RSTn)
                   (video_offset_o[10:1] == W_Msa[9:0]));

  // Coverage: observe some non-zero MSA and corresponding offset mapping
  cover property (cb I_RSTn && (W_Msa[9:0] != 10'h000) && (video_offset_o[10:1] == W_Msa[9:0]));
endmodule

bind crtc6845 crtc6845_sva u_crtc6845_sva(.I_CLK(I_CLK), .I_RSTn(I_RSTn), .video_offset_o(video_offset_o), .W_Msa(W_Msa));


// ==========================================================
// Bind: mpu_if – reset defaults, write protocol, field masking
// ==========================================================
module mpu_if_sva
(
  input  logic        I_RSTn,
  input  logic        I_E,
  input  logic [7:0]  I_DI,
  input  logic        I_RS,
  input  logic        I_RWn,
  input  logic        I_CSn,

  input  logic [7:0]  O_Nht,
  input  logic [7:0]  O_Nhd,
  input  logic [7:0]  O_Nhsp,
  input  logic [3:0]  O_Nhsw,
  input  logic [6:0]  O_Nvt,
  input  logic [4:0]  O_Nadj,
  input  logic [6:0]  O_Nvd,
  input  logic [6:0]  O_Nvsp,
  input  logic [3:0]  O_Nvsw,
  input  logic [4:0]  O_Nr,
  input  logic [13:0] O_Msa,
  input  logic [1:0]  O_DScue,
  input  logic [1:0]  O_CScue,
  input  logic        O_VMode,
  input  logic        O_IntSync
);
  default clocking cb @(negedge I_E); endclocking

  // Track the latched address per MPU protocol (address on RS=0 write)
  logic [4:0] addr_sva;
  always @(negedge I_E or negedge I_RSTn) begin
    if (!I_RSTn) addr_sva <= 5'd0;
    else if (!I_CSn && !I_RWn && !I_RS) addr_sva <= I_DI[4:0];
  end

  // Reset defaults taken at negedge I_RSTn
  property p_reset_defaults;
    @(negedge I_RSTn)
      1 |-> ##0 (O_Nht  == 8'h3F  &&
                 O_Nhd  == 8'h28  &&
                 O_Nhsp == 8'h33  &&
                 {O_Nvsw,O_Nhsw} == 8'h24 &&
                 O_Nvt  == 7'h1E  &&
                 O_Nadj == 5'h02  &&
                 O_Nvd  == 7'h19  &&
                 O_Nvsp == 7'h1B  &&
                 {O_CScue,O_DScue,O_VMode,O_IntSync} == 8'h91 &&
                 O_Nr   == 5'h09  &&
                 O_Msa  == {6'h28,8'h00});
  endproperty
  assert property (p_reset_defaults);

  // Data write updates per current latched address, with proper masking
  property p_write_updates;
    cb disable iff (!I_RSTn)
    (!I_CSn && !I_RWn && I_RS)
      |-> ##0
      (case (addr_sva)
        5'h0: O_Nht   == I_DI;
        5'h1: O_Nhd   == I_DI;
        5'h2: O_Nhsp  == I_DI;
        5'h3: {O_Nvsw,O_Nhsw} == I_DI;
        5'h4: O_Nvt   == I_DI[6:0];
        5'h5: O_Nadj  == I_DI[4:0];
        5'h6: O_Nvd   == I_DI[6:0];
        5'h7: O_Nvsp  == I_DI[6:0];
        5'h8: {O_CScue,O_DScue,O_VMode,O_IntSync} == {I_DI[7:6],I_DI[5:4], I_DI[1], I_DI[0]};
        5'h9: O_Nr    == I_DI[4:0];
        5'hC: (O_Msa[13:8] == I_DI[5:0]) && (O_Msa[7:0] == $past(O_Msa[7:0]));
        5'hD: (O_Msa[7:0]  == I_DI)      && (O_Msa[13:8] == $past(O_Msa[13:8]));
        default: 1'b1;
      endcase);
  endproperty
  assert property (p_write_updates);

  // Coverage: exercise several key registers and fields
  cover property (cb !I_CSn && !I_RWn && !I_RS);                // address latch
  cover property (cb !I_CSn && !I_RWn && I_RS && addr_sva==5'h3); // Nhsw/Nvsw write
  cover property (cb !I_CSn && !I_RWn && I_RS && addr_sva==5'h8); // Intr write
  cover property (cb !I_CSn && !I_RWn && I_RS && addr_sva==5'hC); // Msah write
  cover property (cb !I_CSn && !I_RWn && I_RS && addr_sva==5'hD); // Msal write
endmodule

bind mpu_if mpu_if_sva u_mpu_if_sva(.*);


// ==========================================================
// Bind: crtc_gen – counters, MA behavior, H/V sync, display timing
// ==========================================================
module crtc_gen_sva
(
  input  logic        I_CLK,
  input  logic        I_RSTn,
  input  logic [7:0]  I_Nht,
  input  logic [7:0]  I_Nhd,
  input  logic [7:0]  I_Nhsp,
  input  logic [3:0]  I_Nhsw,
  input  logic [6:0]  I_Nvt,
  input  logic [4:0]  I_Nr,
  input  logic [4:0]  I_Nadj,
  input  logic [6:0]  I_Nvd,
  input  logic [6:0]  I_Nvsp,
  input  logic [3:0]  I_Nvsw,
  input  logic [13:0] I_Msa,

  // internal regs exposed for checking
  input  logic [7:0]  R_H_CNT,
  input  logic [6:0]  R_V_CNT,
  input  logic [4:0]  R_RA,
  input  logic [13:0] R_MA,
  input  logic        R_H_SYNC,
  input  logic        R_V_SYNC,
  input  logic        R_DISPTMG,
  input  logic        R_V_DISPTMG,
  input  logic [13:0] R_MA_C,
  input  logic        R_LAST_LINE,

  // outputs (should mirror regs)
  input  logic [4:0]  O_RA,
  input  logic [13:0] O_MA,
  input  logic        O_H_SYNC,
  input  logic        O_V_SYNC,
  input  logic        O_DISPTMG
);
  default clocking cb @(negedge I_CLK); endclocking

  // Local recomputations (match DUT)
  logic [7:0] next_h;  assign next_h  = R_H_CNT + 8'h01;
  logic [6:0] next_v;  assign next_v  = R_V_CNT + 7'h01;
  logic [4:0] next_ra; assign next_ra = R_RA + 1'b1;

  logic hd;      assign hd      = (R_H_CNT == I_Nht);
  logic vd;      assign vd      = (R_V_CNT == I_Nvt);
  logic adj_c;   assign adj_c   = R_LAST_LINE & (next_ra == I_Nadj);
  logic vcnt_ret;assign vcnt_ret= (((R_RA==I_Nr) & (I_Nadj==0) & vd) | adj_c);
  logic ra_c;    assign ra_c    = ((R_RA==I_Nr) | adj_c);

  logic hsync_p; assign hsync_p = (next_h == I_Nhsp);
  logic hsync_w; assign hsync_w = (next_h[3:0] == (I_Nhsp[3:0] + I_Nhsw));
  logic vsync_p; assign vsync_p = ((next_v == I_Nvsp) & ra_c);
  logic vsync_w; assign vsync_w = (next_ra[3:0] == I_Nvsw);

  logic hdisp_n; assign hdisp_n = (next_h == I_Nhd);
  logic vdisp_n; assign vdisp_n = ((next_v == I_Nvd) & ra_c);

  // Reset defaults at negedge reset
  property p_reset_defaults;
    @(negedge I_RSTn)
      1 |-> ##0 (R_MA==14'h0 && R_MA_C==14'h0 && R_H_CNT==8'h0 && !R_H_SYNC &&
                 R_RA==5'h0 && R_V_CNT==7'h0 && !R_LAST_LINE && !R_V_SYNC &&
                 !R_V_DISPTMG && !R_DISPTMG);
  endproperty
  assert property (p_reset_defaults);

  // Counter behavior
  assert property (cb disable iff (!I_RSTn) (!hd |-> ##1 (R_H_CNT == $past(R_H_CNT)+8'h1)));
  assert property (cb disable iff (!I_RSTn) ( hd |-> ##1 (R_H_CNT == 8'h00)));

  // RA behavior: only updates at end-of-line
  assert property (cb disable iff (!I_RSTn) (!hd |-> ##1 (R_RA == $past(R_RA))));
  assert property (cb disable iff (!I_RSTn) ( hd |-> ##1 (R_RA == ($past(ra_c) ? 5'h00 : ($past(R_RA)+1'b1)))));

  // V counter behavior: updates only when RA carries (ra_c) at end-of-line
  assert property (cb disable iff (!I_RSTn) (!(hd && ra_c) |-> ##1 (R_V_CNT == $past(R_V_CNT))));
  assert property (cb disable iff (!I_RSTn) ( (hd && ra_c) |-> ##1 (R_V_CNT == ($past(vcnt_ret) ? 7'h00 : ($past(R_V_CNT)+7'h01)))));

  // MA behavior (pixel increment and line base carry)
  assert property (cb disable iff (!I_RSTn) (!hd |-> ##1 (R_MA == $past(R_MA)+1'b1)));
  assert property (cb disable iff (!I_RSTn) ( hd |-> ##1 (R_MA == $past(R_MA_C))));
  // MA_C update point
  assert property (cb disable iff (!I_RSTn)
                   ((ra_c && (R_H_CNT==I_Nhd)) |-> ##1 (R_MA_C == ($past(vcnt_ret) ? I_Msa : $past(R_MA)))));

  // H-SYNC set/clear and exclusivity
  assert property (cb disable iff (!I_RSTn) (hsync_p |-> ##1 R_H_SYNC));
  assert property (cb disable iff (!I_RSTn) (hsync_w |-> ##1 !R_H_SYNC));
  assert property (cb disable iff (!I_RSTn) ((R_H_SYNC != $past(R_H_SYNC)) |-> $past(hsync_p || hsync_w)));

  // V-SYNC set/clear occur only at end-of-line
  assert property (cb disable iff (!I_RSTn) ($changed(R_V_SYNC) |-> $past(hd)));
  // Set/clear conditions (sampled on the HD boundary)
  assert property (cb disable iff (!I_RSTn) ($past(hd && vsync_p) |-> (R_V_SYNC)));
  assert property (cb disable iff (!I_RSTn) ($past(hd && vsync_w) |-> (!R_V_SYNC)));

  // Display timing: vertical enable and per-line transfer
  assert property (cb disable iff (!I_RSTn) (vcnt_ret |-> ##1 R_V_DISPTMG));
  assert property (cb disable iff (!I_RSTn) (vdisp_n |-> ##1 !R_V_DISPTMG));
  assert property (cb disable iff (!I_RSTn) ( hd |-> ##1 (R_DISPTMG == $past(R_V_DISPTMG))));
  assert property (cb disable iff (!I_RSTn) ( hdisp_n |-> ##1 !R_DISPTMG));
  // DISPTMG only changes at HD or hdisp_n
  assert property (cb disable iff (!I_RSTn) ($changed(R_DISPTMG) |-> ($past(hd) || hdisp_n)));

  // Output mappings always match regs
  assert property (cb disable iff (!I_RSTn) (O_RA == R_RA));
  assert property (cb disable iff (!I_RSTn) (O_MA == R_MA));
  assert property (cb disable iff (!I_RSTn) (O_H_SYNC == R_H_SYNC));
  assert property (cb disable iff (!I_RSTn) (O_V_SYNC == R_V_SYNC));
  assert property (cb disable iff (!I_RSTn) (O_DISPTMG == R_DISPTMG));

  // Coverage: line end, RA carry, frame return, HS/VS pulses, display active
  cover property (cb hd);
  cover property (cb hd && ra_c);
  cover property (cb hd && vcnt_ret);
  cover property (cb hsync_p ##1 hsync_w);
  cover property (cb $past(hd && vsync_p) ##1 $past(hd && vsync_w));
  cover property (cb R_DISPTMG);
endmodule

bind crtc_gen crtc_gen_sva u_crtc_gen_sva(
  .I_CLK(I_CLK), .I_RSTn(I_RSTn),
  .I_Nht(I_Nht), .I_Nhd(I_Nhd), .I_Nhsp(I_Nhsp), .I_Nhsw(I_Nhsw),
  .I_Nvt(I_Nvt), .I_Nr(I_Nr), .I_Nadj(I_Nadj), .I_Nvd(I_Nvd),
  .I_Nvsp(I_Nvsp), .I_Nvsw(I_Nvsw), .I_Msa(I_Msa),
  .R_H_CNT(R_H_CNT), .R_V_CNT(R_V_CNT), .R_RA(R_RA), .R_MA(R_MA),
  .R_H_SYNC(R_H_SYNC), .R_V_SYNC(R_V_SYNC), .R_DISPTMG(R_DISPTMG),
  .R_V_DISPTMG(R_V_DISPTMG), .R_MA_C(R_MA_C), .R_LAST_LINE(R_LAST_LINE),
  .O_RA(O_RA), .O_MA(O_MA), .O_H_SYNC(O_H_SYNC), .O_V_SYNC(O_V_SYNC), .O_DISPTMG(O_DISPTMG)
);