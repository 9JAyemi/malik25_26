module crtc6845( 
I_E, 
I_DI, 
I_RS, 
I_RWn, 
I_CSn, 
I_CLK, 
I_RSTn, 
 
O_RA, 
O_MA, 
O_H_SYNC, 
O_V_SYNC, 
O_DISPTMG,
video_offset_o 
 
); 
 
input  I_E; 
input  [7:0]I_DI; 
input  I_RS; 
input  I_RWn; 
input  I_CSn; 
 
input  I_CLK; 
input  I_RSTn; 
 
output [4:0]O_RA; 
output [13:0]O_MA; 
output O_H_SYNC; 
output O_V_SYNC; 
output O_DISPTMG; 

output [15:0] video_offset_o;
 
wire   [7:0]W_Nht; 
wire   [7:0]W_Nhd; 
wire   [7:0]W_Nhsp; 
wire   [3:0]W_Nhsw; 
wire   [6:0]W_Nvt; 
wire   [4:0]W_Nadj; 
wire   [6:0]W_Nvd; 
wire   [6:0]W_Nvsp; 
wire   [3:0]W_Nvsw; 
wire   [4:0]W_Nr; 
wire   [13:0]W_Msa; 
 
wire   W_Vmode; 
wire   W_IntSync; 
wire   [1:0] W_DScue; 
wire   [1:0] W_CScue; 

assign video_offset_o = {5'b11000,W_Msa[9:0],1'b0};
 
mpu_if mpu_if( 
 
.I_RSTn(I_RSTn), 
.I_E(I_E), 
.I_DI(I_DI), 
.I_RS(I_RS), 
.I_RWn(I_RWn), 
.I_CSn(I_CSn), 
 
.O_Nht(W_Nht), 
.O_Nhd(W_Nhd), 
.O_Nhsp(W_Nhsp), 
.O_Nhsw(W_Nhsw), 
.O_Nvt(W_Nvt), 
.O_Nadj(W_Nadj), 
.O_Nvd(W_Nvd), 
.O_Nvsp(W_Nvsp), 
.O_Nvsw(W_Nvsw), 
.O_Nr(W_Nr), 
.O_Msa(W_Msa), 
 
.O_VMode(W_Vmode), 
.O_IntSync(W_IntSync), 
.O_DScue(W_DScue), 
.O_CScue(W_CScue)
); 
 
crtc_gen crtc_gen( 
 
.I_CLK(I_CLK), 
.I_RSTn(I_RSTn), 
.I_Nht(W_Nht), 
.I_Nhd(W_Nhd), 
.I_Nhsp(W_Nhsp), 
.I_Nhsw(W_Nhsw), 
.I_Nvt(W_Nvt), 
.I_Nadj(W_Nadj), 
.I_Nvd(W_Nvd), 
.I_Nvsp(W_Nvsp), 
.I_Nvsw(W_Nvsw), 
.I_Nr(W_Nr), 
.I_Msa(W_Msa), 
 
.O_RA(O_RA), 
.O_MA(O_MA), 
.O_H_SYNC(O_H_SYNC), 
.O_V_SYNC(O_V_SYNC), 
.O_DISPTMG(O_DISPTMG) 
 
); 
 
 
endmodule 
 
 
module mpu_if( 
 
I_RSTn, 
I_E, 
I_DI, 
I_RS, 
I_RWn, 
I_CSn, 
 
O_Nht, 
O_Nhd, 
O_Nhsp, 
O_Nhsw, 
O_Nvt, 
O_Nadj, 
O_Nvd, 
O_Nvsp, 
O_Nvsw, 
O_Nr, 
O_Msa, 
 
O_DScue, 
O_CScue, 
O_VMode, 
O_IntSync
); 
 
input I_RSTn; 
input  I_E; 
input  [7:0]I_DI; 
input  I_RS; 
input  I_RWn; 
input  I_CSn; 
 
output [7:0]O_Nht; 
output [7:0]O_Nhd; 
output [7:0]O_Nhsp; 
output [3:0]O_Nhsw; 
output [6:0]O_Nvt; 
output [4:0]O_Nadj; 
output [6:0]O_Nvd; 
output [6:0]O_Nvsp; 
output [3:0]O_Nvsw; 
output [4:0]O_Nr; 
output [13:0]O_Msa; 
output [1:0] O_DScue; 
output [1:0] O_CScue; 
output O_VMode; 
output O_IntSync; 
 

reg    [4:0]R_ADR; 
reg    [7:0]R_Nht; 
reg    [7:0]R_Nhd; 
reg    [7:0]R_Nhsp; 
reg    [7:0]R_Nsw; 
reg    [6:0]R_Nvt; 
reg    [4:0]R_Nadj; 
reg    [6:0]R_Nvd; 
reg    [6:0]R_Nvsp; 
reg    [7:0]R_Intr; 
reg    [4:0]R_Nr; 
reg    [5:0]R_Msah; 
reg    [7:0]R_Msal; 

assign O_Nht  = R_Nht; 
assign O_Nhd  = R_Nhd; 
assign O_Nhsp = R_Nhsp; 
assign O_Nhsw = R_Nsw[3:0]; 
assign O_Nvt  = R_Nvt; 
assign O_Nadj = R_Nadj; 
assign O_Nvd  = R_Nvd; 
assign O_Nvsp = R_Nvsp; 
assign O_Nvsw = R_Nsw[7:4]; 
assign O_Nr   = R_Nr; 
assign O_Msa  = {R_Msah,R_Msal}; 
 
assign O_VMode   =  R_Intr[1]; 
assign O_IntSync =  R_Intr[0]; 
assign O_DScue   = R_Intr[5:4]; assign O_CScue   = R_Intr[7:6]; always@(negedge I_RSTn or negedge I_E) 
begin 
  if(~I_RSTn) begin 
   R_Nht  <= 8'h3F;     R_Nhd  <= 8'h28;     R_Nhsp <= 8'h33;     R_Nsw  <= 8'h24;     R_Nvt  <= 7'h1E;     R_Nadj <= 5'h02;     R_Nvd  <= 7'h19;     R_Nvsp <= 7'h1B; R_Intr <= 8'h91; R_Nr   <= 5'h09; R_Msah <= 6'h28;     R_Msal <= 8'h00;     end else 
  if(~I_CSn)begin 
    if(~I_RWn)begin 
      if(~I_RS)begin       
        R_ADR <= I_DI[4:0]; 
      end else begin 
        case(R_ADR) 
          5'h0 : R_Nht  <= I_DI ; 
          5'h1 : R_Nhd  <= I_DI ; 
          5'h2 : R_Nhsp <= I_DI ; 
          5'h3 : R_Nsw  <= I_DI ; 
          5'h4 : R_Nvt  <= I_DI[6:0] ; 
          4'h5 : R_Nadj <= I_DI[4:0] ; 
          5'h6 : R_Nvd  <= I_DI[6:0] ; 
          5'h7 : R_Nvsp <= I_DI[6:0] ; 
          5'h8 : R_Intr <= I_DI[7:0] ; 
          5'h9 : R_Nr   <= I_DI[4:0] ; 
          5'hC : R_Msah <= I_DI[5:0] ; 
          5'hD : R_Msal <= I_DI ; 
          default:; 
        endcase 
      end 
    end 
  end 
end 
 
endmodule 
 
module crtc_gen( 
 
I_CLK, 
I_RSTn, 
I_Nht, 
I_Nhd, 
I_Nhsp, 
I_Nhsw, 
I_Nvt, 
I_Nadj, 
I_Nvd, 
I_Nvsp, 
I_Nvsw, 
I_Nr, 
I_Msa, 
 
O_RA, 
O_MA, 
O_H_SYNC, 
O_V_SYNC, 
O_DISPTMG 
 
); 
 
input  I_CLK; 
input  I_RSTn; 
input  [7:0]I_Nht; 
input  [7:0]I_Nhd; 
input  [7:0]I_Nhsp; 
input  [3:0]I_Nhsw; 
input  [6:0]I_Nvt; 
input  [4:0]I_Nr; 
input  [4:0]I_Nadj;  input  [6:0]I_Nvd; 
input  [6:0]I_Nvsp; 
input  [3:0]I_Nvsw; 
input  [13:0]I_Msa; 
 
output [4:0]O_RA; 
output [13:0]O_MA; 
output O_H_SYNC; 
output O_V_SYNC; 
output O_DISPTMG; 
 
reg    [7:0]R_H_CNT; 
reg    [6:0]R_V_CNT; 
reg    [4:0]R_RA; 
reg    [13:0]R_MA; 
reg    R_H_SYNC,R_V_SYNC; 
reg    R_DISPTMG ,R_V_DISPTMG; 
reg    R_LAST_LINE; 
 
wire   [7:0] NEXT_R_H_CNT = (R_H_CNT+8'h01); 
wire   [6:0] NEXT_R_V_CNT = (R_V_CNT+7'h01); 
wire   [4:0] NEXT_R_RA    = R_RA + 1'b1; 
 
wire W_HD       = (R_H_CNT==I_Nht); 
 
wire W_VD       = (R_V_CNT==I_Nvt); 
wire W_ADJ_C    = R_LAST_LINE & (NEXT_R_RA==I_Nadj); 
wire W_VCNT_RET = ((R_RA==I_Nr) & (I_Nadj==0) & W_VD) | W_ADJ_C; 
 
wire W_RA_C     = (R_RA==I_Nr) | W_ADJ_C; 
 
wire   W_HSYNC_P = (NEXT_R_H_CNT == I_Nhsp); 
wire   W_HSYNC_W = (NEXT_R_H_CNT[3:0] == (I_Nhsp[3:0]+I_Nhsw) ); 
wire   W_VSYNC_P = (NEXT_R_V_CNT == I_Nvsp ) & W_RA_C; 
wire   W_VSYNC_W = (NEXT_R_RA[3:0]==I_Nvsw); 
 
wire W_HDISP_N   = (NEXT_R_H_CNT==I_Nhd); 
wire W_VDISP_N   = (NEXT_R_V_CNT==I_Nvd) & W_RA_C; 
 
assign O_H_SYNC = R_H_SYNC; 
assign O_V_SYNC = R_V_SYNC; 
assign O_RA     = R_RA; 
assign O_MA     = R_MA; 
assign O_DISPTMG = R_DISPTMG; 
 
reg    [13:0] R_MA_C; 
always@(negedge I_CLK or negedge I_RSTn) 
begin 
  if(! I_RSTn)begin 
    R_MA   <= 14'h0000; 
    R_MA_C <= 14'h0000; 
    R_H_CNT <= 8'h00;  
    R_H_SYNC <= 0;  
    R_RA <= 5'h00;  
 
    R_V_CNT <= 7'h00;  
    R_LAST_LINE <= 1'b0; 
    R_V_SYNC <= 0;  
 
    R_V_DISPTMG <= 1'b0; 
    R_DISPTMG   <= 1'b0; 
  end 
  else begin 
    R_H_CNT <= W_HD ? 8'h00 : NEXT_R_H_CNT; 
 
    R_MA <= W_HD ? R_MA_C : R_MA + 1'b1; 
 
    if(W_RA_C & (R_H_CNT==I_Nhd) ) 
      R_MA_C <= W_VCNT_RET ? I_Msa : R_MA; 
 
    if(W_HSYNC_P)      R_H_SYNC <= 1'b1; 
    else if(W_HSYNC_W) R_H_SYNC <= 1'b0; 
 
    if(W_HD) 
    begin 
      R_RA <= W_RA_C ? 5'h00 : NEXT_R_RA; 
 
      if(W_VSYNC_P) R_V_SYNC <= 1'b1; 
      else if(W_VSYNC_W) R_V_SYNC <= 1'b0; 
 
      if(W_RA_C) 
      begin 
        R_LAST_LINE <= W_VD; 
 
        R_V_CNT <= W_VCNT_RET ? 7'h00 : NEXT_R_V_CNT; 
      end 
    end 
 
    if(W_VCNT_RET)     R_V_DISPTMG <= 1'b1; 
    else if(W_VDISP_N) R_V_DISPTMG <= 1'b0; 
 
    if(W_HD)           R_DISPTMG <= R_V_DISPTMG; 
    else if(W_HDISP_N) R_DISPTMG <= 1'b0; 
  end 
end 
 
endmodule
