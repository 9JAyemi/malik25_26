// SVA for sixteen_bit_adder and its internal 8-bit ripple chain.
// Binds into the DUT and checks functional correctness, wiring, X-prop, and key coverage.

module sixteen_bit_adder_sva (
  input clk,
  input reset,
  input [15:0] a,
  input [15:0] b,
  input carry_in,
  input [15:0] sum,
  input carry_out,
  input [7:0] adder1_sum,
  input adder1_carry_out,
  input [7:0] adder2_sum,
  input adder2_carry_out
);
  default clocking cb @(posedge clk); endclocking

  // Full 16-bit result must match 17-bit widened addition
  a_full: assert property ( !$isunknown({a,b,carry_in})
                            |-> {carry_out, sum} == ({1'b0,a} + {1'b0,b} + carry_in) );

  // Lower 8-bit adder result and carry
  a_lo:   assert property ( !$isunknown({a[7:0],b[7:0],carry_in})
                            |-> {adder1_carry_out, adder1_sum} == ({1'b0,a[7:0]} + {1'b0,b[7:0]} + carry_in) );

  // Upper 8-bit adder result and carry with ripple carry-in
  a_hi:   assert property ( !$isunknown({a[15:8],b[15:8],adder1_carry_out})
                            |-> {adder2_carry_out, adder2_sum} == ({1'b0,a[15:8]} + {1'b0,b[15:8]} + adder1_carry_out) );

  // Output wiring from internal adders
  a_map_sum:  assert property ( sum == {adder2_sum, adder1_sum} );
  a_map_cout: assert property ( carry_out == adder2_carry_out );

  // No X/Z on outputs when inputs known
  a_no_x_out: assert property ( !$isunknown({a,b,carry_in})
                                |-> !$isunknown({sum,carry_out,adder1_sum,adder2_sum,adder1_carry_out,adder2_carry_out}) );

  // Coverage: exercise carry_in, lower/upper carries, overall carry, and key corner cases
  c_ci0: cover property (!carry_in);
  c_ci1: cover property ( carry_in);
  c_c1_lo: cover property ( adder1_carry_out );
  c_c1_hi: cover property ( adder2_carry_out );
  c_co1:   cover property ( carry_out );

  c_zero_zero:    cover property ( !carry_in && a==16'h0000 && b==16'h0000 && sum==16'h0000 && !carry_out );
  c_lo_overflow:  cover property ( !carry_in && a[7:0]==8'hFF && b[7:0]==8'h01 && adder1_carry_out && sum[7:0]==8'h00 );
  c_cross_page:   cover property ( !carry_in && a==16'h00FF && b==16'h0001 && sum==16'h0100 );
  c_full_overflow:cover property ( !carry_in && a==16'hFFFF && b==16'h0001 && carry_out );

endmodule

bind sixteen_bit_adder sixteen_bit_adder_sva sva16 (.*);