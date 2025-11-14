// SystemVerilog Assertions for bt656cap_decoder
module bt656cap_decoder_sva(
  input  logic        vid_clk,
  input  logic [7:0]  p,

  input  logic        stb,
  input  logic        field,
  input  logic [31:0] ycc422,

  input  logic [7:0]  ioreg,
  input  logic [1:0]  byten,
  input  logic [31:0] inreg,

  input  logic        in_field,
  input  logic        in_hblank,
  input  logic        in_vblank
);
  default clocking cb @(posedge vid_clk); endclocking
  default disable iff ($initstate);

  let code_detect = (byten==2'd0 && inreg[31:8]==24'hff0000);
  let data_ok    = (byten==2'd0 && inreg[31:8]!=24'hff0000 && !in_hblank && !in_vblank);

  // Input sampling
  assert property (ioreg == $past(p));

  // Byte counter sequencing and start detection
  assert property ((ioreg!=8'hff) |=> byten == $past(byten)+2'd1);
  assert property ((ioreg==8'hff) |=> (byten==2'd1 && inreg[31:24]==8'hff));
  assert property (($past(ioreg)!=8'hff && $past(byten)==2'd3) |=> byten==2'd0);

  // Byte placement into inreg
  assert property (($past(ioreg)!=8'hff && $past(byten)==2'd0) |=> inreg[31:24] == $past(ioreg));
  assert property (($past(ioreg)!=8'hff && $past(byten)==2'd1) |=> inreg[23:16] == $past(ioreg));
  assert property (($past(ioreg)!=8'hff && $past(byten)==2'd2) |=> inreg[15:8]  == $past(ioreg));
  assert property (($past(ioreg)!=8'hff && $past(byten)==2'd3) |=> inreg[7:0]   == $past(ioreg));

  // Flags update only on code; values taken from code XY bits
  assert property (!code_detect |=> $stable({in_field,in_hblank,in_vblank}));
  assert property (code_detect |=> {in_field,in_vblank,in_hblank} == {$past(inreg[6]),$past(inreg[5]),$past(inreg[4])});

  // Strobe generation/gating
  assert property (data_ok |-> ##0 stb);
  assert property (stb |-> (byten==2'd0 && inreg[31:8]!=24'hff0000 && !in_hblank && !in_vblank));
  assert property (stb |=> !stb);             // one-cycle pulse
  assert property (code_detect |-> ##0 !stb); // never strobe on codes
  assert property ((in_hblank || in_vblank) |-> !stb);

  // Output payload on strobe and stability otherwise
  assert property (stb |-> ##0 (field==in_field && ycc422==inreg));
  assert property (!stb |=> ($stable(field) && $stable(ycc422)));
  assert property (stb |-> !$isunknown({field,ycc422}));
  assert property (!$isunknown({in_field,in_hblank,in_vblank,stb}));

  // Coverage
  cover property (code_detect);
  cover property (code_detect && inreg[6]==1'b0);
  cover property (code_detect && inreg[6]==1'b1);
  cover property (code_detect && inreg[5]==1'b0);
  cover property (code_detect && inreg[5]==1'b1);
  cover property (code_detect && inreg[4]==1'b0);
  cover property (code_detect && inreg[4]==1'b1);
  cover property (stb);
  cover property (code_detect ##[1:20] stb);
  cover property (stb && field==1'b0);
  cover property (stb && field==1'b1);
  cover property (byten==2'd0 && $past(byten)==2'd3 && $past(ioreg)!=8'hff);
endmodule

bind bt656cap_decoder bt656cap_decoder_sva u_bt656cap_decoder_sva(
  .vid_clk(vid_clk),
  .p(p),
  .stb(stb),
  .field(field),
  .ycc422(ycc422),
  .ioreg(ioreg),
  .byten(byten),
  .inreg(inreg),
  .in_field(in_field),
  .in_hblank(in_hblank),
  .in_vblank(in_vblank)
);