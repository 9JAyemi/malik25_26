
module sprites_shifter (
  input clk,          // 28MHz clock
  input reset,        // reset
  input aen,          // address enable
  input [1:0] address,// register address input
  input [8:0] hpos,   // horizontal beam counter
  input [15:0] fmode, // fmode input
  input shift,        // shift signal
  input [47:0] chip48,// chip48 input
  input [15:0] data_in,// bus data in
  output [1:0] sprdata,// serialized sprite data out
  output reg attach   // sprite is attached
);

// register names and addresses
parameter POS  = 2'b00;
parameter CTL  = 2'b01;
parameter DATA = 2'b10;
parameter DATB = 2'b11;

// local signals
reg [63:0] datla;    // data register A
reg [63:0] datlb;    // data register B
reg [63:0] shifta;   // shift register A
reg [63:0] shiftb;   // shift register B
reg [8:0] hstart;    // horizontal start value
reg armed;           // sprite "armed" signal
reg load;            // load shift register signal
reg load_del;

// switch data according to fmode
reg [64-1:0] spr_fmode_dat;

always @ (*) begin
  case(fmode[3:2])
    2'b00   : spr_fmode_dat = {data_in, 48'h000000000000};
    2'b11   : spr_fmode_dat = {data_in, chip48[47:0]};
    default : spr_fmode_dat = {data_in, chip48[47:32], 32'h00000000};
  endcase
end

// generate armed signal
always @(posedge clk)
  if (reset) // reset disables sprite
    armed <= 0;
  else if (aen && address == CTL && !reset) // writing CTL register disables sprite
    armed <= 0;
  else if (aen && address == DATA && !reset) // writing data register A arms sprite
    armed <= 1;

// generate load signal
always @(posedge clk)
  if (reset) // reset disables load
    load <= 0;
  else if (armed && hpos[7:0] == hstart[7:0] && (fmode[15] || hpos[8] == hstart[8])) // load when horizontal beam counter matches horizontal start value and sprite is armed
    load <= 1;
  else
    load <= 0;

always @(posedge clk)
  if (reset) // reset disables load
    load_del <= 0;
  else
    load_del <= load;

// POS register
always @(posedge clk)
  if (aen && address == POS && !reset)
    hstart[8:0] <= data_in[8:0];

// CTL register
always @(posedge clk)
  if (aen && address == CTL && !reset)
    attach <= data_in[7];

// data register A
always @(posedge clk)
  if (aen && address == DATA && !reset)
    datla[63:0] <= spr_fmode_dat;

// data register B
always @(posedge clk)
  if (aen && address == DATB && !reset)
    datlb[63:0] <= spr_fmode_dat;

// sprite shift register
always @(posedge clk)
  if (load_del) // load new data into shift register
  begin
    shifta[63:0] <= datla[63:0];
    shiftb[63:0] <= datlb[63:0];
  end
  else if (shift) // shift left by one bit
  begin
    shifta[63:0] <= {shifta[62:0], 1'b0};
    shiftb[63:0] <= {shiftb[62:0], 1'b0};
  end

// assign serialized output data
assign sprdata = {shiftb[63], shifta[63]};

endmodule