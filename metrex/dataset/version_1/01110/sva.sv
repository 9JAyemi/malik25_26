// SVA for pixel_reader. Bind this file to the DUT.
// Focused, high-signal-coverage checks + a small shadow counter to relate o_read_stb to i_read_size.

`ifndef PIXEL_READER_SVA
`define PIXEL_READER_SVA

module pixel_reader_sva (
  input                     clk,
  input                     rst,

  input                     i_read_rdy,
  input           [23:0]    i_read_size,
  input           [24:0]    i_read_data,
  input                     i_pixel_stb,

  input                     i_tp_red,
  input                     i_tp_blue,
  input                     i_tp_green,

  input                     o_read_act,
  input                     o_read_stb,

  input           [7:0]     o_red,
  input           [7:0]     o_green,
  input           [7:0]     o_blue,

  input                     o_pixel_rdy,
  input                     o_last
);

default clocking cb @(posedge clk); endclocking
default disable iff (rst);

// Shadow counter: expected remaining pixels this transaction
logic [23:0] pending;
always_ff @(posedge clk) begin
  if (rst) pending <= '0;
  else begin
    if ($rose(o_read_act)) pending <= i_read_size;
    else if (o_read_stb)   pending <= pending - 24'd1;
  end
end

// Reset values
assert property (@(posedge clk) rst |-> (!o_read_act && !o_read_stb && !o_pixel_rdy &&
                                         o_red==8'd0 && o_green==8'd0 && o_blue==8'd0 && o_last==1'b0));

// Start causality
assert property ($rose(o_read_act) |-> $past(i_read_rdy && !o_read_act));

// Zero-length transfer behavior
assert property ($rose(o_read_act) && (i_read_size==24'd0) |-> !o_read_stb ##1 $fell(o_read_act));

// Pixel-ready timing (1-cycle pipeline of o_read_act)
assert property (o_pixel_rdy == $past(o_read_act));

// Read strobe well-formed
assert property (o_read_stb |-> ($past(o_read_act) && i_pixel_stb));
assert property ((!o_read_act && !$past(o_read_act)) |-> !o_read_stb);

// No overshoot vs. requested size, and proper completion
assert property (o_read_stb |-> (pending > 24'd0));
assert property ($fell(o_read_act) |-> (pending == 24'd0));

// Data capture correctness (RGB + last) on handshake
assert property ($past(o_pixel_rdy && i_pixel_stb) |->
                 (o_red   == $past(i_read_data[23:16]) &&
                  o_green == $past(i_read_data[15:8])  &&
                  o_blue  == $past(i_read_data[7:0])   &&
                  o_last  == $past(i_read_data[24])));

// Outputs hold value when no capture
assert property (!$past(o_pixel_rdy && i_pixel_stb) |-> $stable({o_red,o_green,o_blue,o_last}));

// Optional environment assumption: size remains stable while active
assume  property (o_read_act |-> $stable(i_read_size));

// Compact, useful coverage
sequence three_strobes; o_read_stb ##[0:$] o_read_stb ##[0:$] o_read_stb; endsequence
cover property ($rose(o_read_act) ##[1:$] three_strobes ##[1:$] $fell(o_read_act));
cover property ($rose(o_read_act) ##[1:$] $fell(o_read_act));                 // any completed read
cover property ($rose(o_read_act) && (i_read_size==24'd0) ##1 $fell(o_read_act));
cover property ($past(o_pixel_rdy && i_pixel_stb && i_read_data[24]) |-> o_last);

endmodule

bind pixel_reader pixel_reader_sva sva_inst (
  .clk(clk), .rst(rst),
  .i_read_rdy(i_read_rdy),
  .i_read_size(i_read_size),
  .i_read_data(i_read_data),
  .i_pixel_stb(i_pixel_stb),
  .i_tp_red(i_tp_red), .i_tp_blue(i_tp_blue), .i_tp_green(i_tp_green),
  .o_read_act(o_read_act), .o_read_stb(o_read_stb),
  .o_red(o_red), .o_green(o_green), .o_blue(o_blue),
  .o_pixel_rdy(o_pixel_rdy),
  .o_last(o_last)
);

`endif