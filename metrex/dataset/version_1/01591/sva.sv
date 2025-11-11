// SVA for calculator_top
package calc_sva_pkg;
  function automatic logic [8:0] exp_sum9(logic [1:0] op, logic [7:0] a, b);
    case (op)
      2'b00: exp_sum9 = {1'b0,a} + {1'b0,b};
      2'b01: exp_sum9 = {1'b0,a} - {1'b0,b};
      default: exp_sum9 = 9'b0;
    endcase
  endfunction
endpackage

module calculator_top_sva;
  import calc_sva_pkg::*;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Async reset clears state/outputs (checked at clock edge)
  assert property (disable iff (1'b0) @(posedge clk)
                   !rst_n |-> (sum==9'b0 && result==8'b0 && valid==1'b1));

  // Sum update matches 9-bit arithmetic of previous-cycle inputs
  assert property ($past(rst_n) |-> sum == exp_sum9($past(op), $past(a), $past(b)));

  // Outputs are consistent with sum
  assert property (result == sum[7:0]);
  assert property (valid  == (sum[8]==1'b0));

  // Valid reflects true overflow/borrow of operation
  assert property ($past(rst_n) |-> valid == ~exp_sum9($past(op),$past(a),$past(b))[8]);

  // Basic safety: no X/Z on outputs
  assert property (!$isunknown({result,valid}));

  // Coverage
  cover property ($past(rst_n) && ($past(op)==2'b00));                  // add exercised
  cover property ($past(rst_n) && ($past(op)==2'b01));                  // sub exercised
  cover property ($past(rst_n) && !($past(op) inside {2'b00,2'b01}));   // default path
  cover property ($past(rst_n) && exp_sum9($past(op),$past(a),$past(b))[8]); // overflow/borrow scenario
  cover property (valid==1'b0);                                         // valid deasserts (should on overflow/borrow)
endmodule

bind calculator_top calculator_top_sva calc_sva_i();