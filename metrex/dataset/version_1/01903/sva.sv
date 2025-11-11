// SVA for flt_mult. Bind this module to the DUT.
// Example:
// bind flt_mult flt_mult_sva i_flt_mult_sva (.*);

module flt_mult_sva (
  input logic         clk,
  input logic         rstn,
  input logic [31:0]  afl,
  input logic [31:0]  bfl,
  input logic [31:0]  fl,

  // Internal DUT signals (connected via bind)
  input logic [47:0]  mfl_0,
  input logic         sfl_0,
  input logic [7:0]   efl_0,
  input logic         zero_out_0,
  input logic         sfl_1,
  input logic [7:0]   efl_1,
  input logic         zero_out_1,
  input logic         mfl47_1,
  input logic [24:0]  nmfl_1,
  input logic         not_mfl_47
);

default clocking cb @(posedge clk); endclocking
default disable iff (!rstn);

// Basic sanity
assert property (cb !rstn |-> (mfl_0==48'h0 && sfl_0==0 && efl_0==8'h0 && zero_out_0==0
                             && sfl_1==0 && efl_1==8'h0 && zero_out_1==0
                             && mfl47_1==0 && nmfl_1==25'h0 && fl==32'h0));
assert property (cb !$isunknown({afl,bfl,fl,sfl_0,efl_0,mfl_0,zero_out_0,sfl_1,efl_1,zero_out_1,mfl47_1,nmfl_1,not_mfl_47}));

// Pipe 0: combinational results registered
assert property (cb sfl_0 == (afl[31] ^ bfl[31]));
assert property (cb efl_0 == (afl[30:23] + bfl[30:23] - 8'h7E));
assert property (cb mfl_0 == ({1'b1,afl[22:0]} * {1'b1,bfl[22:0]}));
assert property (cb zero_out_0 == ((afl[30:0]==31'h0) || (bfl[30:0]==31'h0)));

// Pipe 1: register transfers and normalization
assert property (cb efl_1      == $past(efl_0));
assert property (cb sfl_1      == $past(sfl_0));
assert property (cb zero_out_1 == $past(zero_out_0));
assert property (cb mfl47_1    == $past(mfl_0[47]));
assert property (cb $past(mfl_0[47]) |-> (nmfl_1 == ($past(mfl_0[47:24]) + $past(mfl_0[23]))));
assert property (cb !$past(mfl_0[47]) |-> (nmfl_1 == ($past(mfl_0[47:23]) + $past(mfl_0[22]))));

// Combinational helper
assert property (cb not_mfl_47 == (~mfl47_1 & ~nmfl_1[24]));

// Pipe 2: final packing
assert property (cb zero_out_1 |-> (fl == 32'h0));
assert property (cb (!zero_out_1) |-> (fl == {sfl_1, (efl_1 - not_mfl_47), nmfl_1[22:0]}));

// End-to-end zero behavior from inputs (2-cycle latency)
assert property (cb (($past(afl[30:0],2)==0) || ($past(bfl[30:0],2)==0)) |-> (fl==32'h0));

// Output bitfield consistency when non-zero
assert property (cb (!zero_out_1) |-> (fl[31]==sfl_1));
assert property (cb (!zero_out_1) |-> (fl[22:0]==nmfl_1[22:0]));

// Coverage
cover property (cb ((afl[30:0]==0) || (bfl[30:0]==0)) ##2 (fl==32'h0));
cover property (cb $past(mfl_0[47]) && !zero_out_1);               // mfl_0[47] path
cover property (cb !$past(mfl_0[47]) &&  nmfl_1[24] && !zero_out_1); // rounding carry after left-normalize
cover property (cb !$past(mfl_0[47]) && !nmfl_1[24] && !zero_out_1); // no carry after left-normalize
cover property (cb !zero_out_1 && sfl_1);                          // negative result
cover property (cb !zero_out_1 && !sfl_1);                         // positive result
cover property (cb not_mfl_47);                                    // exponent adjust asserted
cover property (cb !not_mfl_47 && !zero_out_1);                    // no exponent adjust

endmodule