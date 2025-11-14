// SVA checker for MC6502Accumulator
// Bind this module to the DUT and drive clk/rst_n from your environment.
module MC6502Accumulator_sva (
  input logic                 clk,
  input logic                 rst_n,
  input logic [7:0]           i_a,
  input logic [7:0]           i_m,
  input logic                 i_c,
  input logic                 i_d,
  input logic                 i_s,
  input logic [7:0]           o_a,
  input logic                 o_n,
  input logic                 o_z,
  input logic                 o_c,
  input logic                 o_v
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n || $isunknown({i_a,i_m,i_c,i_d,i_s}));

  // Pure combinational reference (mirrors DUT math exactly)
  let w_m8       = (i_s) ? ~i_m : i_m;
  let fix4       = (i_s) ? 4'ha : 4'h6;

  let ci5        = {4'b0, i_c};
  let bsum_lo5   = {1'b0,i_a[3:0]} + {1'b0,w_m8[3:0]} + ci5;
  let dover_lo   = (bsum_lo5 > 5'd9);
  let dsum_lo5   = dover_lo ? (bsum_lo5 + {1'b0,fix4}) : bsum_lo5;
  let sum_low5   = i_d ? dsum_lo5 : bsum_lo5;

  let carry1     = i_d ? (dover_lo ^ i_s) : sum_low5[4];

  let bsum_hi5   = {1'b0,i_a[7:4]} + {1'b0,w_m8[7:4]} + {4'b0,carry1};
  let hi_adj     = !(bsum_hi5[3:0] < 4'ha);
  let dsum_hi5   = hi_adj ? (bsum_hi5 + {1'b0,fix4}) : bsum_hi5;
  let sum_high5  = i_d ? dsum_hi5 : bsum_hi5;

  let exp_a8     = {sum_high5[3:0], sum_low5[3:0]};
  let exp_n1     = exp_a8[7];
  let exp_z1     = (exp_a8 == 8'h00);
  let exp_c1     = sum_high5[4];
  let exp_v1     = (!(i_a[7] ^ w_m8[7]) & (i_a[7] ^ exp_a8[7]));

  // Strong equivalence of all DUT outputs to reference
  property p_equivalence;
    1'b1 |-> (o_a==exp_a8 && o_n==exp_n1 && o_z==exp_z1 && o_c==exp_c1 && o_v==exp_v1);
  endproperty
  assert property (p_equivalence);

  // Sanity flag invariants (redundant with p_equivalence but explicit)
  assert property (o_n == o_a[7]);
  assert property (o_z == (o_a == 8'h00));

  // Binary mode shortcut cross-check (simple 9-bit add)
  let bin_sum9 = {1'b0,i_a} + {1'b0,w_m8} + {8'b0,i_c};
  assert property (!i_d |-> (o_a==bin_sum9[7:0] && o_c==bin_sum9[8]));

  // Low-nibble behavior in binary mode
  assert property (!i_d |-> (o_a[3:0] == (i_a[3:0] + w_m8[3:0] + i_c)[3:0]));

  // No X/Z on outputs when inputs are known
  assert property (!$isunknown({o_a,o_n,o_z,o_c,o_v}));

  // Functional coverage (concise but hits key scenarios)
  cover property (!i_d && !i_s);          // binary add
  cover property (!i_d &&  i_s);          // binary subtract
  cover property ( i_d && !i_s);          // decimal add
  cover property ( i_d &&  i_s);          // decimal subtract

  cover property ( i_d && dover_lo);      // decimal low nibble adjust
  cover property ( i_d && hi_adj);        // decimal high nibble adjust

  cover property ( o_c);                  // carry set
  cover property (!o_c);                  // carry clear
  cover property ( o_v);                  // overflow set
  cover property (!o_v);                  // overflow clear
  cover property ( o_z);                  // zero result
  cover property ( o_a[7]);               // negative result

endmodule

// Example bind (connect clk/rst_n from your environment):
// bind MC6502Accumulator MC6502Accumulator_sva u_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));