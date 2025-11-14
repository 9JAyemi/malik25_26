// SVA checker for binary_adder
module binary_adder_sva (
  input  logic [3:0] in1,
  input  logic [3:0] in2,
  input  logic       ctrl,
  input  logic [3:0] sum,
  input  logic       cout
);
  logic [4:0] exp_sum;
  always_comb exp_sum = {1'b0, in1} + {1'b0, in2};

  // No X on outputs when inputs known
  assert property (@(in1 or in2 or ctrl or sum or cout)
                   !$isunknown({in1,in2,ctrl}) |-> !$isunknown({sum,cout}))
    else $error("binary_adder: X/Z on outputs with known inputs");

  // ctrl == 0: sum is low nibble, cout is carry
  assert property (@(in1 or in2 or ctrl)
                   disable iff ($isunknown({in1,in2,ctrl}))
                   (ctrl==1'b0) |-> (sum==exp_sum[3:0] && cout==exp_sum[4]))
    else $error("binary_adder: ctrl=0 behavior mismatch");

  // ctrl == 1: sum is zero-extended carry, cout is carry
  assert property (@(in1 or in2 or ctrl)
                   disable iff ($isunknown({in1,in2,ctrl}))
                   (ctrl==1'b1) |-> (sum=={3'b000,exp_sum[4]} && cout==exp_sum[4]))
    else $error("binary_adder: ctrl=1 behavior mismatch");

  // cout always equals carry-out of addition (independent of ctrl)
  assert property (@(in1 or in2 or ctrl)
                   disable iff ($isunknown({in1,in2}))
                   cout == exp_sum[4])
    else $error("binary_adder: cout != carry-out");

  // Basic functional coverage
  cover property (@(in1 or in2 or ctrl) (ctrl==0 && exp_sum[4]==0));
  cover property (@(in1 or in2 or ctrl) (ctrl==0 && exp_sum[4]==1));
  cover property (@(in1 or in2 or ctrl) (ctrl==1 && exp_sum[4]==0));
  cover property (@(in1 or in2 or ctrl) (ctrl==1 && exp_sum[4]==1));
  cover property (@(in1 or in2 or ctrl) (in1==4'h0 && in2==4'h0));
  cover property (@(in1 or in2 or ctrl) (in1==4'hF && in2==4'hF));
endmodule

// Bind into DUT
bind binary_adder binary_adder_sva u_binary_adder_sva(.*);