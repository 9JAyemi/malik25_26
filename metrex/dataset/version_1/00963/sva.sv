// SVA for adder_4bit
// Bind into DUT
bind adder_4bit adder_4bit_sva sva(.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));

module adder_4bit_sva(
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       cin,
  input  logic [3:0] sum,
  input  logic       cout
);

  // Drive a sampling event on any input change
  event comb_ev;
  always @(a or b or cin) -> comb_ev;

  // Golden 5-bit expected result (avoid width truncation)
  function automatic logic [4:0] exp_sum(input logic [3:0] ax, bx, input logic cinx);
    exp_sum = {1'b0, ax} + {1'b0, bx} + cinx;
  endfunction

  // Outputs must be known whenever inputs are known
  property p_known_outputs;
    @(comb_ev) !$isunknown({a,b,cin}) |-> !$isunknown({cout,sum});
  endproperty
  assert property(p_known_outputs);

  // Functional correctness: {cout,sum} equals 5-bit addition of a, b, cin
  property p_add_correct;
    @(comb_ev) !$isunknown({a,b,cin}) |-> {cout,sum} == exp_sum(a,b,cin);
  endproperty
  assert property(p_add_correct);

  // Optional finer checks (redundant but clearer intent)
  property p_cout_bit;
    @(comb_ev) !$isunknown({a,b,cin}) |-> cout == exp_sum(a,b,cin)[4];
  endproperty
  assert property(p_cout_bit);

  property p_sum_bits;
    @(comb_ev) !$isunknown({a,b,cin}) |-> sum == exp_sum(a,b,cin)[3:0];
  endproperty
  assert property(p_sum_bits);

  // Concise functional coverage of key scenarios and boundaries
  cover property (@(comb_ev) !$isunknown({a,b,cin}) && a==4'd0 && b==4'd0 && cin==1'b0 && {cout,sum}==5'd0);     // zero + zero
  cover property (@(comb_ev) !$isunknown({a,b,cin}) && a==4'd0 && b==4'd0 && cin==1'b1 && {cout,sum}==5'd1);     // carry-in only
  cover property (@(comb_ev) !$isunknown({a,b,cin}) && b==4'd0 && cin==1'b0 && sum==a && cout==1'b0);            // identity: +0
  cover property (@(comb_ev) !$isunknown({a,b,cin}) && a==4'd0 && cin==1'b0 && sum==b && cout==1'b0);            // identity: +0
  cover property (@(comb_ev) !$isunknown({a,b,cin}) && a==4'hF && b==4'h1 && cin==1'b0 && cout==1'b1 && sum==4'd0); // exact 16 boundary
  cover property (@(comb_ev) !$isunknown({a,b,cin}) && a==4'hF && b==4'hF && cin==1'b1 && cout==1'b1 && sum==4'hF); // max 31
  cover property (@(comb_ev) !$isunknown({a,b,cin}) && cout==1'b0);                                               // any no-carry case
  cover property (@(comb_ev) !$isunknown({a,b,cin}) && cout==1'b1);                                               // any carry case

endmodule