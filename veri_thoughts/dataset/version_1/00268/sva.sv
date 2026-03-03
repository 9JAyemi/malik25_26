// SVA for add_sub_4bit
// Bind these assertions to the DUT; provide clk/rst_n from TB.
// Example bind:
// bind add_sub_4bit add_sub_4bit_sva u_sva(.clk(tb_clk), .rst_n(tb_rst_n), .A(A), .B(B), .mode(mode), .O(O), .COUT(COUT));

module add_sub_4bit_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        mode,
  input logic [3:0]  O,
  input logic        COUT
);
  default clocking cb @ (posedge clk); endclocking
  default disable iff (!rst_n)

  // Helpers
  logic [4:0] sum5, diff5;
  assign sum5  = {1'b0, A} + {1'b0, B};
  assign diff5 = {1'b0, A} - {1'b0, B};

  // No X/Z on outputs when inputs are known
  assert property ( !$isunknown({A,B,mode}) |-> !$isunknown({O,COUT}) );

  // Functional correctness (5-bit accurate math)
  assert property ( (!$isunknown({A,B,mode})) && (mode==1'b0) |-> {COUT,O} == sum5  );
  assert property ( (!$isunknown({A,B,mode})) && (mode==1'b1) |-> {COUT,O} == diff5 );

  // Carry/borrow bit sanity
  assert property ( (!$isunknown({A,B,mode})) && (mode==1'b0) |-> COUT == sum5[4]  );
  assert property ( (!$isunknown({A,B,mode})) && (mode==1'b1) |-> COUT == diff5[4] );

  // Purely combinational: if inputs hold, outputs hold
  assert property ( $stable({A,B,mode}) |-> $stable({O,COUT}) );

  // Minimal functional coverage
  cover property ( (mode==1'b0) && (sum5[4]==1'b0) ); // add no carry
  cover property ( (mode==1'b0) && (sum5[4]==1'b1) ); // add with carry
  cover property ( (mode==1'b1) && (diff5[4]==1'b0) ); // sub no borrow
  cover property ( (mode==1'b1) && (diff5[4]==1'b1) ); // sub with borrow
  cover property ( (mode==1'b0) && (A==4'hF) && (B==4'h1) );
  cover property ( (mode==1'b1) && (A==4'h0) && (B==4'h1) );
  cover property ( (mode==1'b1) && (A==4'h8) && (B==4'h8) );
  cover property ( $changed(mode) );
endmodule