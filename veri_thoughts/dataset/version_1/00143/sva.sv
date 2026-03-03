// SVA for four_bit_adder
// Assumes a sampling clock 'clk' in the bind scope.
// Bind statement at bottom; change .clk(clk) as needed.

module four_bit_adder_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        Cin,
  input logic [3:0]  Sum,
  input logic        Cout
);
  default clocking cb @(posedge clk); endclocking

  // track availability of $past
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // No X/Z on outputs when inputs are known
  a_no_x: assert property ( !$isunknown({A,B,Cin}) |-> !$isunknown({Sum,Cout}) );

  // Functional correctness (5-bit result must equal A+B+Cin)
  a_add_ok: assert property ( disable iff ($isunknown({A,B,Cin,Sum,Cout}))
                              {Cout,Sum} == A + B + Cin );

  // Purely combinational: if inputs hold, outputs hold
  a_hold_ok: assert property ( disable iff (!past_valid || $isunknown({A,B,Cin,Sum,Cout}))
                               $stable({A,B,Cin}) |=> $stable({Sum,Cout}) );

  // Increment behavior: with A,B stable, Cin 0->1 increments 5-bit result by 1
  a_cin_inc: assert property ( disable iff (!past_valid || $isunknown({A,B,Cin,Sum,Cout}))
                               $stable({A,B}) && !$past(Cin) && Cin
                               |-> {Cout,Sum} == $past({Cout,Sum}) + 5'd1 );

  // Basic functional coverage
  c_cin0:        cover property (Cin==1'b0);
  c_cin1:        cover property (Cin==1'b1);
  c_carry0:      cover property (Cout==1'b0);
  c_carry1:      cover property (Cout==1'b1);

  // Corner cases
  c_zero:        cover property (A==4'h0 && B==4'h0 && Cin==1'b0 && Sum==4'h0 && Cout==1'b0);
  c_one:         cover property (A==4'h0 && B==4'h0 && Cin==1'b1 && Sum==4'h1 && Cout==1'b0);
  c_max_ovf:     cover property (A==4'hF && B==4'hF && Cin==1'b1 && Sum==4'hF && Cout==1'b1);

  // Commutativity across samples (swap A/B, keep Cin; result unchanged)
  c_commute:     cover property ( disable iff (!past_valid || $isunknown({A,B,Cin,Sum,Cout}))
                                  Cin==$past(Cin) && A==$past(B) && B==$past(A) &&
                                  {Cout,Sum}==$past({Cout,Sum}) );

endmodule

bind four_bit_adder four_bit_adder_sva sva_i (.clk(clk), .*);