// SVA for decoder_2to4
module decoder_2to4_sva (
  input logic [1:0] in,
  input logic       out0,
  input logic       out1,
  input logic       out2,
  input logic       out3
);

  // Sample on any input edge; ignore checks when input has X/Z
  default clocking cb @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1]); endclocking
  default disable iff ($isunknown(in))

  // Outputs are known and exactly one-hot
  a_known:  assert property (!$isunknown({out3,out2,out1,out0})) else $error("decoder_2to4: X/Z on outputs");
  a_onehot: assert property ($onehot({out3,out2,out1,out0}))     else $error("decoder_2to4: outputs not one-hot");

  // Functional equivalence: {out3..out0} == (1 << in)
  a_decode: assert property ({out3,out2,out1,out0} == (4'b0001 << in))
            else $error("decoder_2to4: decode mismatch for in=%0b", in);

  // Functional coverage: hit all 4 input/output mappings
  c_00: cover property (in==2'b00 && {out3,out2,out1,out0}==4'b0001);
  c_01: cover property (in==2'b01 && {out3,out2,out1,out0}==4'b0010);
  c_10: cover property (in==2'b10 && {out3,out2,out1,out0}==4'b0100);
  c_11: cover property (in==2'b11 && {out3,out2,out1,out0}==4'b1000);

endmodule

// Bind into DUT
bind decoder_2to4 decoder_2to4_sva sva_inst (.*);