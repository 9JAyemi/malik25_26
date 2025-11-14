// SVA for top_module and full_adder
// Bind these in your testbench or compile alongside the DUT

// Top-level SVA bound into top_module
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [15:0] sum,
  input logic [7:0]  fa_out1,
  input logic [7:0]  carry
);

  // Combinational ripple adder correctness (internal chain equals a+b)
  property p_comb_chain_correct;
    @(posedge clk)
      {carry[7], fa_out1} == ({1'b0, a} + {1'b0, b});
  endproperty
  assert property (p_comb_chain_correct);

  // Registered output equals previous cycle a+b (zero-extended to 16)
  property p_sum_reg_model;
    @(posedge clk) disable iff (reset)
      (!$past(reset)) |-> (sum == {7'b0, ({1'b0,$past(a)} + {1'b0,$past(b)})});
  endproperty
  assert property (p_sum_reg_model);

  // Registered output captures the internal chain (structure check)
  property p_sum_captures_chain;
    @(posedge clk) disable iff (reset)
      (!$past(reset)) |-> (sum == {7'b0, $past(carry[7]), $past(fa_out1)});
  endproperty
  assert property (p_sum_captures_chain);

  // Upper bits of sum are always zero (width consistency)
  property p_sum_upper_zero;
    @(posedge clk) disable iff (reset)
      sum[15:9] == '0;
  endproperty
  assert property (p_sum_upper_zero);

  // Synchronous reset drives sum to 0 on the next cycle
  property p_sync_reset_zero;
    @(posedge clk) reset |=> (sum == '0);
  endproperty
  assert property (p_sync_reset_zero);

  // X-checks (after reset deasserted)
  property p_known_outputs;
    @(posedge clk) disable iff (reset)
      !$isunknown(sum) && !$isunknown({fa_out1,carry});
  endproperty
  assert property (p_known_outputs);

  property p_known_inputs;
    @(posedge clk)
      !$isunknown({a,b});
  endproperty
  assert property (p_known_inputs);

  // Minimal but meaningful coverage
  // Zero result
  cover property (@(posedge clk) !reset && ({1'b0,a}+{1'b0,b}) == 9'd0);
  // Carry-out occurs
  cover property (@(posedge clk) !reset && ({1'b0,a}+{1'b0,b}) >= 9'd256);
  // Max result (510)
  cover property (@(posedge clk) !reset && ({1'b0,a}+{1'b0,b}) == 9'd510);
  // Long carry-propagation scenario (classic)
  cover property (@(posedge clk) !reset && (a==8'hFF) && (b==8'h01));

endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .a(a),
  .b(b),
  .sum(sum),
  .fa_out1(fa_out1),
  .carry(carry)
);


// SVA for full_adder primitive
module full_adder_sva (
  input logic clk,      // any clock; only used to sample
  input logic a, b, cin,
  input logic sum, cout
);
  // Functional truth check
  property p_fa_truth;
    @(posedge clk)
      (sum == (a ^ b ^ cin)) && (cout == ((a & b) | (a & cin) | (b & cin)));
  endproperty
  assert property (p_fa_truth);

  // X-check
  property p_fa_known;
    @(posedge clk)
      !$isunknown({a,b,cin,sum,cout});
  endproperty
  assert property (p_fa_known);

  // Cover all 8 input combinations
  cover property (@(posedge clk) 1'b1); // simple hit counter
  // Optional: specific corner covers
  cover property (@(posedge clk) (a==0 && b==0 && cin==0));
  cover property (@(posedge clk) (a==1 && b==1 && cin==1));
endmodule

// Bind full_adder SVA into each instance (uses DUT clock for sampling)
bind full_adder full_adder_sva u_full_adder_sva (
  .clk(top_module.clk), // reference top clock for sampling
  .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout)
);