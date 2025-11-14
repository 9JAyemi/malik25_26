// SVA checker for twos_comp_addsub
module twos_comp_addsub_sva
  #(parameter int W = 16)
(
  input  logic                       clk,
  input  logic                       rst_n,
  input  logic signed [W-1:0]        a,
  input  logic signed [W-1:0]        b,
  input  logic                       sub,
  input  logic signed [W-1:0]        result,
  input  logic                       overflow
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Expected (mathematically correct, 2's comp wrapped) results and overflow
  logic signed [W-1:0] exp_add = $signed(a) + $signed(b);
  logic signed [W-1:0] exp_sub = $signed(a) - $signed(b);
  logic signed [W-1:0] exp_res = '0;

  logic add_ovf, sub_ovf, exp_ovf;
  always_comb begin
    exp_res = (sub ? exp_sub : exp_add);
    add_ovf = (a[W-1] == b[W-1]) && (exp_add[W-1] != a[W-1]);
    sub_ovf = (a[W-1] != b[W-1]) && (exp_sub[W-1] != a[W-1]);
    exp_ovf = sub ? sub_ovf : add_ovf;
  end

  // Inputs must be known; if they are, outputs must be known
  assert property ( !$isunknown({a,b,sub}) );
  assert property ( !$isunknown({a,b,sub}) |-> !$isunknown({result,overflow}) );

  // Functional correctness: result and overflow
  assert property ( !$isunknown({a,b,sub}) |-> result == exp_res );
  assert property ( !$isunknown({a,b,sub}) |-> overflow == exp_ovf );

  // Sanity: no overflow when impossible by sign pattern
  assert property ( sub==0 && (a[W-1] != b[W-1]) |-> overflow == 1'b0 );
  assert property ( sub==1 && (a[W-1] == b[W-1]) |-> overflow == 1'b0 );

  // Coverage: exercise both ops with/without overflow
  cover property ( sub==0 && !$isunknown({a,b}) && overflow );
  cover property ( sub==0 && !$isunknown({a,b}) && !overflow );
  cover property ( sub==1 && !$isunknown({a,b}) && overflow );
  cover property ( sub==1 && !$isunknown({a,b}) && !overflow );

  // Boundary/interesting cases
  cover property ( sub==0 && a==16'sh7FFF && b==16'sh0001 && overflow );
  cover property ( sub==0 && a==16'sh8000 && b==16'shFFFF && overflow );
  cover property ( sub==1 && a==16'sh8000 && b==16'sh7FFF && overflow );
  cover property ( sub==1 && a==16'sh7FFF && b==16'sh7FFF && result==0 && !overflow );
  cover property ( sub==0 && a==16'sd42   && b==-16'sd42   && result==0 && !overflow );

endmodule

// Example bind (provide clk/rst_n from TB)
// bind twos_comp_addsub twos_comp_addsub_sva #(.W(16)) u_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));