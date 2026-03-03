// SVA checker for Adder4Bit
module Adder4Bit_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic        Cin,
  input  logic [3:0]  S,
  input  logic        V
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional correctness: 5-bit sum must match {V,S}
  assert property ( {V,S} == ({1'b0,A} + {1'b0,B} + Cin) )
    else $error("Adder4Bit: {V,S} mismatch vs A+B+Cin");

  // Cleanliness: known inputs imply known outputs
  assert property ( !$isunknown({A,B,Cin}) |-> !$isunknown({S,V}) )
    else $error("Adder4Bit: X/Z on outputs with known inputs");

  // Combinational stability: if inputs stable, outputs stable
  assert property ( !$isunknown({A,B,Cin,S,V}) && $stable({A,B,Cin}) |-> $stable({S,V}) )
    else $error("Adder4Bit: outputs changed without input change");

  // Coverage
  cover property ( Cin==0 );
  cover property ( Cin==1 );
  cover property ( V==0 );
  cover property ( V==1 );
  cover property ( {A,B,Cin} == {4'h0,4'h0,1'b0} ); // min
  cover property ( {A,B,Cin} == {4'hF,4'hF,1'b1} ); // max/overflow
  // Hit every possible 4-bit sum value on S
  genvar i;
  generate
    for (i=0; i<16; i++) begin : gen_cov_S
      cover property ( S == i[3:0] );
    end
  endgenerate
endmodule

// Example bind (hook clk/rst_n from your TB)
// bind Adder4Bit Adder4Bit_sva u_adder4bit_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));