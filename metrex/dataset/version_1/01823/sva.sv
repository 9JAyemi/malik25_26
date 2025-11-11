// SVA binders for the given DUTs
// Focused, concise, strong end-to-end checks + essential internal invariants and coverage.

timeunit 1ns/1ps;

// Priority encoder assertions
module pe_sva;
  // Local sampling clock for purely combinational DUT
  bit clk; initial clk = 0; always #1 clk = ~clk;

  // Assert exact functional mapping and priority behavior
  // Disable on X/Z activity to avoid false failures
  property pe_func;
    !$isunknown({in, out}) |->
      out == (in[3] ? 2'b11 :
              in[2] ? 2'b10 :
              in[1] ? 2'b01 :
                      2'b00);
  endproperty

  // Priority cases (also serve as targeted coverage points)
  property pe_case3; !$isunknown({in,out}) |->
                     (in[3]) |-> (out == 2'b11); endproperty
  property pe_case2; !$isunknown({in,out}) |->
                     (!in[3] && in[2]) |-> (out == 2'b10); endproperty
  property pe_case1; !$isunknown({in,out}) |->
                     (!in[3] && !in[2] && in[1]) |-> (out == 2'b01); endproperty
  property pe_case0; !$isunknown({in,out}) |->
                     (!in[3] && !in[2] && !in[1]) |-> (out == 2'b00); endproperty

  // Assertions
  assert property (@(posedge clk) pe_func);
  assert property (@(posedge clk) pe_case3);
  assert property (@(posedge clk) pe_case2);
  assert property (@(posedge clk) pe_case1);
  assert property (@(posedge clk) pe_case0);

  // Coverage: hit each priority path, including multi-hot priorities
  cover property (@(posedge clk) in[3] && out==2'b11);
  cover property (@(posedge clk) !in[3] && in[2] && out==2'b10);
  cover property (@(posedge clk) !in[3] && !in[2] && in[1] && out==2'b01);
  cover property (@(posedge clk) !in[3] && !in[2] && !in[1] && out==2'b00);
  cover property (@(posedge clk) (in[3] && (|in[2:0])) && out==2'b11);
  cover property (@(posedge clk) (!in[3] && in[2] && (in[1]||in[0])) && out==2'b10);
endmodule
bind priority_encoder pe_sva pe_sva_i();


// Full adder assertions
module fa_sva;
  bit clk; initial clk = 0; always #1 clk = ~clk;

  // Strong arithmetic equivalence
  property fa_add;
    !$isunknown({a,b,cin,sum,cout}) |-> {cout, sum} == (a + b + cin);
  endproperty

  assert property (@(posedge clk) fa_add);

  // Coverage: all output combinations reachable
  cover property (@(posedge clk) !$isunknown({a,b,cin,sum,cout}) && {cout,sum}==2'b00);
  cover property (@(posedge clk) !$isunknown({a,b,cin,sum,cout}) && {cout,sum}==2'b01);
  cover property (@(posedge clk) !$isunknown({a,b,cin,sum,cout}) && {cout,sum}==2'b10);
  cover property (@(posedge clk) !$isunknown({a,b,cin,sum,cout}) && {cout,sum}==2'b11);
endmodule
bind full_adder fa_sva fa_sva_i();


// Binary multiplier assertions
module bm_sva;
  bit clk; initial clk = 0; always #1 clk = ~clk;

  // End-to-end correctness (unsigned)
  property bm_correct;
    !$isunknown({a,b,product}) |-> product == (a * b);
  endproperty
  assert property (@(posedge clk) bm_correct);

  // Zero-multiplicand property
  property bm_zero;
    !$isunknown({a,b,product}) |-> ((a==4'd0 || b==4'd0) |-> product==8'd0);
  endproperty
  assert property (@(posedge clk) bm_zero);

  // Internal invariants from DUT structure (sanity on internal transforms)
  property bm_internal_shift_zero_lsbs;
    !$isunknown({a_shifted,b_shifted}) |-> (a_shifted[1:0] == 2'b00 && b_shifted[1:0] == 2'b00);
  endproperty
  assert property (@(posedge clk) bm_internal_shift_zero_lsbs);

  // Coverage: key corners and a nontrivial valid case
  cover property (@(posedge clk) (a==4'd0) && (product==8'd0));
  cover property (@(posedge clk) (b==4'd0) && (product==8'd0));
  cover property (@(posedge clk) (a==4'd15 && b==4'd15));
  cover property (@(posedge clk) ($countones(a)==1 && b!=0));
  cover property (@(posedge clk) (a!=0 && b!=0 && product==(a*b)));
endmodule
bind binary_multiplier bm_sva bm_sva_i();