// SVA for denise_sprites_shifter
// Bind into the DUT to check internal behavior concisely

module denise_sprites_shifter_sva
(
  input  logic         clk,
  input  logic         clk7_en,
  input  logic         reset,
  input  logic         aen,
  input  logic [1:0]   address,
  input  logic [8:0]   hpos,
  input  logic [15:0]  fmode,
  input  logic         shift,
  input  logic [47:0]  chip48,
  input  logic [15:0]  data_in,
  input  logic [1:0]   sprdata,
  input  logic         attach,

  input  logic [63:0]  datla,
  input  logic [63:0]  datlb,
  input  logic [63:0]  shifta,
  input  logic [63:0]  shiftb,
  input  logic [8:0]   hstart,
  input  logic         armed,
  input  logic         load,
  input  logic         load_del,
  input  logic [63:0]  spr_fmode_dat
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset/arm behavior (check reset explicitly)
  assert property (@(posedge clk) clk7_en && reset |=> !armed);
  assert property (clk7_en && aen && address==2'b01 |=> !armed); // CTL clears
  assert property (clk7_en && aen && address==2'b10 |=> armed);  // DATA arms
  assert property (clk7_en && !(aen && (address inside {2'b01,2'b10})) |=> $stable(armed));

  // load computation and its 1-cycle delay to load_del
  assert property (clk7_en |=> load == $past(armed && (hpos[7:0]==hstart[7:0]) && (fmode[15] || (hpos[8]==hstart[8]))));
  assert property (clk7_en |=> load_del == $past(load));

  // POS and CTL writes and stability of unrelated bits
  assert property (clk7_en && aen && address==2'b00 |=> hstart[8:1] == $past(data_in[7:0]));          // POS
  assert property (clk7_en && !(aen && address==2'b00) |=> $stable(hstart[8:1]));
  assert property (clk7_en && aen && address==2'b01 |=> hstart[0] == $past(data_in[0]) && attach == $past(data_in[7])); // CTL
  assert property (clk7_en && !(aen && address==2'b01) |=> $stable(hstart[0]) && $stable(attach));

  // DATA/DATB write semantics and stability otherwise
  assert property (clk7_en && aen && address==2'b10 |=> datla == $past(spr_fmode_dat));
  assert property (clk7_en && !(aen && address==2'b10) |=> $stable(datla));
  assert property (clk7_en && aen && address==2'b11 |=> datlb == $past(spr_fmode_dat));
  assert property (clk7_en && !(aen && address==2'b11) |=> $stable(datlb));

  // spr_fmode_dat formation
  assert property (spr_fmode_dat[63:48] == data_in);
  assert property ((fmode[3:2]==2'b00) |-> spr_fmode_dat[47:0]  == 48'h0);
  assert property ((fmode[3:2]==2'b11) |-> spr_fmode_dat[47:0]  == chip48);
  assert property ((fmode[3:2] inside {2'b01,2'b10}) |-> (spr_fmode_dat[47:32]==chip48[47:32] && spr_fmode_dat[31:0]==32'h0));

  // Shifter load vs shift vs hold
  assert property (clk7_en && load_del |=> shifta == $past(datla) && shiftb == $past(datlb)); // load has priority
  assert property (shift && !(clk7_en && load_del) |=> shifta == {$past(shifta)[62:0],1'b0} && shiftb == {$past(shiftb)[62:0],1'b0});
  assert property (!(shift) && !(clk7_en && load_del) |=> $stable(shifta) && $stable(shiftb));

  // Output mapping
  assert property (sprdata == {shiftb[63], shifta[63]});

  // After 64 shifts without a reload, MSBs must be 0 (zero-fill)
  assert property ( (shift && !(clk7_en && load_del)) [*64] |=> sprdata == 2'b00 );

  // Minimal functional coverage
  cover property (clk7_en && aen && address==2'b00); // POS write
  cover property (clk7_en && aen && address==2'b01); // CTL write
  cover property (clk7_en && aen && address==2'b10); // DATA write
  cover property (clk7_en && aen && address==2'b11); // DATB write
  cover property (fmode[15]==0 && (fmode[3:2] inside {2'b00,2'b01,2'b10,2'b11}));
  cover property (fmode[15]==1 && (fmode[3:2] inside {2'b00,2'b01,2'b10,2'b11}));
  cover property (clk7_en && load ##1 clk7_en && load_del); // load pipeline observed
  cover property ((clk7_en && load_del) ##1 (shift && !(clk7_en && load_del))); // load followed by shift
  cover property ($changed(sprdata));

endmodule

// Bind into every instance of denise_sprites_shifter
bind denise_sprites_shifter denise_sprites_shifter_sva sva_i
(
  .clk,
  .clk7_en,
  .reset,
  .aen,
  .address,
  .hpos,
  .fmode,
  .shift,
  .chip48,
  .data_in,
  .sprdata,
  .attach,
  .datla,
  .datlb,
  .shifta,
  .shiftb,
  .hstart,
  .armed,
  .load,
  .load_del,
  .spr_fmode_dat
);