// SystemVerilog Assertions for the provided DUTs.
// Bind these checkers; no RTL changes required.

///////////////////////////////////////////////////////////////
// digitalfilter SVA
///////////////////////////////////////////////////////////////
module digitalfilter_sva(
  input clk, input ce, input in, input out,
  input [5:0] taps, input result
);
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;
  default clocking @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Combinational consistency
  assert property (out == result);
  assert property (!$isunknown({out,result,taps}));  

  // Shift behavior
  assert property ($past(ce) |-> (taps[5:1] == $past(taps[4:0]) && taps[0] == $past(in)));
  assert property (!$past(ce) |-> taps == $past(taps));

  // Consensus output rules
  assert property ($past(&taps[5:2]) |-> result == 1'b1);
  assert property ($past(~|taps[5:2]) |-> result == 1'b0);

  // Result changes only on consensus
  assert property (($past(result) != result) |-> ($past(&taps[5:2]) || $past(~|taps[5:2])));

  // Coverage
  cover property ($rose(result));
  cover property ($fell(result));
endmodule

bind digitalfilter digitalfilter_sva u_digitalfilter_sva(
  .clk(clk), .ce(ce), .in(in), .out(out), .taps(taps), .result(result)
);

///////////////////////////////////////////////////////////////
// graycode2 SVA
///////////////////////////////////////////////////////////////
module graycode2_sva(
  input clk, input freeze, input [1:0] tach,
  input up, input down, input [1:0] last, input [3:0] encodedstate
);
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;
  default clocking @(posedge clk); endclocking
  default disable iff (!past_valid);

  // No X, mutual exclusion
  assert property (!$isunknown({up,down,last})); 
  assert property (!(up && down));

  // Freeze holds state and no pulses
  assert property ($past(freeze) |-> (up==0 && down==0 && last==$past(last)));

  // Directional decoding (based on previous cycle's encoding)
  assert property ($past(!freeze && ($past(encodedstate) inside
                  {4'b0100,4'b1101,4'b1011,4'b0010})) |-> (up==1 && down==0 && last==$past(tach)));
  assert property ($past(!freeze && ($past(encodedstate) inside
                  {4'b0001,4'b0111,4'b1110,4'b1000})) |-> (up==0 && down==1 && last==$past(tach)));

  // Neutral transitions: no pulses, last holds
  assert property ($past(!freeze && ($past(encodedstate) inside
                  {4'b0000,4'b1111,4'b1010,4'b0101,4'b0011,4'b1100,4'b0110,4'b1001}))
                  |-> (up==0 && down==0 && last==$past(last)));

  // Coverage
  cover property (up && !down);
  cover property (down && !up);
  cover property ($rose(freeze));
endmodule

bind graycode2 graycode2_sva u_graycode2_sva(
  .clk(clk), .freeze(freeze), .tach(tach),
  .up(up), .down(down), .last(last), .encodedstate(encodedstate)
);

///////////////////////////////////////////////////////////////
// udcounter16 SVA
///////////////////////////////////////////////////////////////
module udcounter16_sva(
  input clk, input up, input down, input [15:0] counter, input [15:0] result
);
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;
  default clocking @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Port consistency and no X
  assert property (counter == result);
  assert property (!$isunknown(result));

  // Update rules (down wins if both asserted)
  assert property ($past( up && !down) |-> result == $past(result) + 16'd1);
  assert property ($past(!up &&  down) |-> result == $past(result) - 16'd1);
  assert property ($past( up &&  down) |-> result == $past(result) - 16'd1);
  assert property ($past(!up && !down) |-> result == $past(result));

  // Coverage: inc, dec, wrap/underflow
  cover property ($past(up && !down) ##1 result == $past(result)+16'd1);
  cover property ($past(down && !up) ##1 result == $past(result)-16'd1);
  cover property ($past(result)==16'hFFFF && $past(up && !down) ##1 result==16'h0000);
  cover property ($past(result)==16'h0000 && $past(down && !up) ##1 result==16'hFFFF);
endmodule

bind udcounter16 udcounter16_sva u_udcounter16_sva(
  .clk(clk), .up(up), .down(down), .counter(counter), .result(result)
);

///////////////////////////////////////////////////////////////
// qc16 SVA
///////////////////////////////////////////////////////////////
module qc16_sva(
  input clk, input [1:0] tach, input freeze, input invphase,
  input [7:0] counth, input [7:0] countl,
  input [15:0] counter, input up, input down, input [1:0] adjtach
);
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;
  default clocking @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Adjtach mux correctness
  assert property ( invphase -> (adjtach == {tach[0],tach[1]}));
  assert property (!invphase -> (adjtach == tach));

  // Byte-slice correctness
  assert property (counth == counter[15:8]);
  assert property (countl == counter[7:0]);

  // Freeze holds counter (no pulses under freeze)
  assert property ($past(freeze) |-> counter == $past(counter));

  // Up/Down exclusivity and counter reaction (integration check)
  assert property (!(up && down));
  assert property ($past(up && !down) |-> counter == $past(counter)+16'd1);
  assert property ($past(down && !up) |-> counter == $past(counter)-16'd1);

  // No X on key internal signals
  assert property (!$isunknown({up,down,counter,adjtach,counth,countl}));

  // Coverage: both invphase settings and pulses
  cover property ($rose(invphase));
  cover property ($fell(invphase));
  cover property (up || down);
endmodule

bind qc16 qc16_sva u_qc16_sva(
  .clk(clk), .tach(tach), .freeze(freeze), .invphase(invphase),
  .counth(counth), .countl(countl),
  .counter(counter), .up(up), .down(down), .adjtach(adjtach)
);

///////////////////////////////////////////////////////////////
// tachcounter SVA
///////////////////////////////////////////////////////////////
module tachcounter_sva(
  input clk, input freeze,
  input [7:0] counth, input [7:0] countl
);
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;
  default clocking @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Top-level: freeze holds outputs
  assert property ($past(freeze) |-> {counth,countl} == $past({counth,countl}));

  // No X on outputs
  assert property (!$isunknown({counth,countl}));

  // Coverage
  cover property ($rose(freeze));
endmodule

bind tachcounter tachcounter_sva u_tachcounter_sva(
  .clk(clk), .freeze(freeze), .counth(counth), .countl(countl)
);