// SVA bind module for sprites_shifter
module sprites_shifter_sva (
  input  logic         clk,
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

  // Mirror register addresses (keep in sync with DUT)
  localparam POS  = 2'b00;
  localparam CTL  = 2'b01;
  localparam DATA = 2'b10;
  localparam DATB = 2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // spr_fmode_dat mapping
  assert property ( (fmode[3:2]==2'b00) |-> spr_fmode_dat == {data_in, 48'h0} );
  assert property ( (fmode[3:2]==2'b11) |-> spr_fmode_dat == {data_in, chip48} );
  assert property ( (fmode[3:2] inside {2'b01,2'b10}) |-> spr_fmode_dat == {data_in, chip48[47:32], 32'h0} );

  // Writes to registers
  assert property ( aen && address==POS  |=> hstart == $past(data_in[8:0]) );
  assert property ( aen && address==CTL  |=> attach == $past(data_in[7]) );
  assert property ( aen && address==DATA |=> datla  == $past(spr_fmode_dat) );
  assert property ( aen && address==DATB |=> datlb  == $past(spr_fmode_dat) );

  // Armed control
  assert property ( aen && address==CTL  |=> armed==1'b0 );
  assert property ( aen && address==DATA |=> armed==1'b1 );
  assert property ( !(aen && (address==CTL || address==DATA)) |=> $stable(armed) );

  // Load generation equivalence
  assert property ( load == (armed && (hpos[7:0]==hstart[7:0]) && (fmode[15] || (hpos[8]==hstart[8]))) );

  // load_del is 1-cycle delayed load
  assert property ( load_del == $past(load) );

  // Shift/load behavior
  assert property ( load_del |=> (shifta==$past(datla) && shiftb==$past(datlb)) );
  assert property ( shift && !load_del |=> (shifta==={$past(shifta[62:0]),1'b0} && shiftb==={$past(shiftb[62:0]),1'b0}) );

  // Output mapping and stability when idle
  assert property ( sprdata == {shiftb[63], shifta[63]} );
  assert property ( !(load_del || shift) |=> $stable({shifta,shiftb,sprdata}) );

  // No-X on key control signals (out of reset)
  assert property ( !$isunknown({sprdata, armed, load, load_del}) );

  // Writes during reset do not change regs (allowing armed to be 0 by reset logic)
  assert property (@(posedge clk) reset && aen && address==POS  |=> $stable(hstart));
  assert property (@(posedge clk) reset && aen && address==CTL  |=> $stable(attach));
  assert property (@(posedge clk) reset && aen && address==DATA |=> $stable(datla));
  assert property (@(posedge clk) reset && aen && address==DATB |=> $stable(datlb));

  // Reset effects
  assert property (@(posedge clk) reset |-> (armed==0 && load==0 && load_del==0));

  // Coverage
  cover property ( aen && address==POS );
  cover property ( aen && address==CTL );
  cover property ( aen && address==DATA );
  cover property ( aen && address==DATB );
  cover property ( aen && address==DATA ##1 armed );
  cover property ( load && fmode[15] );
  cover property ( load && !fmode[15] && (hpos[8]==hstart[8]) );
  cover property ( load_del ##1 shift );
  cover property ( fmode[3:2]==2'b00 );
  cover property ( fmode[3:2]==2'b11 );
  cover property ( fmode[3:2] inside {2'b01,2'b10} );

endmodule

bind sprites_shifter sprites_shifter_sva sva_i (.*);