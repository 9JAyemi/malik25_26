// SVA bind module for binary_adder (combinational). Sample with any convenient clk.
module binary_adder_sva
(
  input  logic                         clk,
  input  logic signed [3:0]            a,
  input  logic signed [3:0]            b,
  input  logic signed                  cin,
  input  logic signed [3:0]            sum,
  input  logic signed                  cout
);

  default clocking cb @(posedge clk); endclocking

  // Functional consistency with RTL expression (connectivity/sanity)
  a_func_eq: assert property ( $signed({cout,sum}) == $signed(a + b + cin) );

  // Determinism: if inputs stable, outputs remain stable
  a_stable:   assert property ( $stable(a) && $stable(b) && $stable(cin) |-> $stable(sum) && $stable(cout) );

  // No X/Z on outputs when inputs are known
  a_no_x:     assert property ( !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout}) );

  // Given the signed widths used, cout equals sign bit of sum (observed structural behavior)
  a_cout_is_sign: assert property ( !$isunknown(sum) |-> (cout === sum[3]) );

  // Coverage: exercise cin, extremes, overflows, and observe cout polarity
  c_cin0:     cover property ( cin == 1'b0 );
  c_cin1:     cover property ( cin == 1'b1 );

  c_pos_overflow: cover property ( !$isunknown({a,b,cin,sum}) && (a[3]==1'b0) && (b[3]==1'b0) && (sum[3]==1'b1) );
  c_neg_overflow: cover property ( !$isunknown({a,b,cin,sum}) && (a[3]==1'b1) && (b[3]==1'b1) && (sum[3]==1'b0) );

  c_zero_sum: cover property ( !$isunknown({a,b,cin,sum}) && (sum == 4'sd0) );
  c_sum_max:  cover property ( !$isunknown({a,b,cin,sum}) && (sum == 4'sd7) );
  c_sum_min:  cover property ( !$isunknown({a,b,cin,sum}) && (sum == -4'sd8) );

  c_cout0:    cover property ( cout == 1'b0 );
  c_cout1:    cover property ( cout == 1'b1 );

  // Coverage: highlight cases where true 5-bit unsigned carry differs from reported cout
  c_carry_mismatch: cover property (
    !$isunknown({a,b,cin,sum,cout}) &&
    ( ($unsigned({1'b0,a}) + $unsigned({1'b0,b}) + $unsigned(cin))[4] != (cout) )
  );

endmodule

// Example bind (replace clk with your sampling clock):
// bind binary_adder binary_adder_sva u_binary_adder_sva (.* , .clk(tb_clk));