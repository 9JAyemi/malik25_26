// SVA for four_bit_adder
module four_bit_adder_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  a, b,
  input logic        cin,
  input logic [3:0]  sum,
  input logic        cout
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  property p_reset_zero;
    rst |=> (sum == 4'b0 && cout == 1'b0);
  endproperty
  assert property (p_reset_zero);

  property p_reset_hold;
    rst && $past(rst,1,1'b1) |-> (sum == 4'b0 && cout == 1'b0);
  endproperty
  assert property (p_reset_hold);

  // Core functionality: registered 5-bit addition
  property p_add_correct;
    (!rst && !$past(rst,1,1'b1))
      |-> {cout, sum} == ($past({1'b0,a}) + $past({1'b0,b}) + $past(cin));
  endproperty
  assert property (p_add_correct);

  // X-propagation: no X on outputs when inputs known and not in reset
  property p_no_x_out;
    (!rst && !$past(rst,1,1'b1) && !$isunknown($past({a,b,cin})))
      |-> !$isunknown({sum,cout});
  endproperty
  assert property (p_no_x_out);

  // Coverage
  cover property (rst ##1 !rst); // reset then deassert
  cover property ((!rst && !$past(rst,1,1'b1))
                  && (($past({1'b0,a}) + $past({1'b0,b}) + $past(cin))[4] == 1'b0));
  cover property ((!rst && !$past(rst,1,1'b1))
                  && (($past({1'b0,a}) + $past({1'b0,b}) + $past(cin))[4] == 1'b1));

endmodule

// Bind into DUT
bind four_bit_adder four_bit_adder_sva sva_i (
  .clk(clk), .rst(rst),
  .a(a), .b(b), .cin(cin),
  .sum(sum), .cout(cout)
);