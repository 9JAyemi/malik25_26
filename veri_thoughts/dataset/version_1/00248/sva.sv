// SVA checker for four_bit_adder
module four_bit_adder_sva #(parameter int WIDTH = 4)
(
  input  logic                  clk,
  input  logic [WIDTH-1:0]      a,
  input  logic [WIDTH-1:0]      b,
  input  logic                  cin,
  input  logic [WIDTH-1:0]      sum,
  input  logic                  cout
);

  default clocking cb @(posedge clk); endclocking

  // Core functional correctness
  assert property ( {cout, sum} == ({1'b0, a} + {1'b0, b} + cin) );

  // No X on outputs when inputs are known
  assert property ( !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout}) );

  // Purely combinational/stateness check
  assert property ( $stable({a,b,cin}) |-> $stable({sum,cout}) );

  // Optional commutativity check across adjacent cycles when exercised by stimulus
  assert property ( (a==$past(b) && b==$past(a) && cin==$past(cin))
                    |-> ({cout,sum}==$past({cout,sum})) );

  // Coverage: carry 0/1 and cin 0/1
  cover property (cout == 0);
  cover property (cout == 1);
  cover property (cin  == 0);
  cover property (cin  == 1);
  cover property (cin==0 && cout==1); // carry without carry-in
  cover property (cin==1 && cout==1); // carry with carry-in

  // Extremes and exact wraparound to 2^WIDTH
  cover property (a=={WIDTH{1'b0}} && b=={WIDTH{1'b0}} && cin==0 && sum=={WIDTH{1'b0}} && cout==0);
  cover property (a=={WIDTH{1'b1}} && b=={WIDTH{1'b1}} && cin==1 && sum=={WIDTH{1'b1}} && cout==1);
  cover property ( ({1'b0,a}+{1'b0,b}+cin) == {1'b1,{WIDTH{1'b0}}} && sum=={WIDTH{1'b0}} && cout==1 );

  // Hit every sum value 0 .. 2^WIDTH-1
  genvar i;
  generate
    for (i = 0; i < (1<<WIDTH); i++) begin : g_sum_cov
      cover property ( sum == i[WIDTH-1:0] );
    end
  endgenerate

endmodule

// Bind template (connect clk from your environment):
// bind four_bit_adder four_bit_adder_sva #(.WIDTH(4))
//   u_four_bit_adder_sva ( .clk(<your_clk>), .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout) );