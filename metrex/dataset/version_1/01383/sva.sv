// SVA for calculator
// Bind these assertions to the DUT for concise, high-quality checking and coverage.

module calculator_sva(input clk, input [7:0] a, input [7:0] b, input [1:0] op, input [7:0] result);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity on control
  ap_no_x_on_op:        assert property (!$isunknown(op));
  ap_no_div0:           assert property (!(op==2'b11 && b==8'd0)); // flag illegal divide-by-zero attempts

  // 1-cycle functional correctness (results reflect previous-cycle inputs)
  ap_add:               assert property ( $past(op)==2'b00 |-> result == (($past(a)+$past(b)) & 8'hFF) );
  ap_sub:               assert property ( $past(op)==2'b01 |-> result == (($past(a)-$past(b)) & 8'hFF) );
  ap_mul:               assert property ( $past(op)==2'b10 |-> result == (($past(a)*$past(b)) & 8'hFF) );
  ap_div:               assert property ( $past(op)==2'b11 && ($past(b)!=8'd0) |-> result == ($past(a)/$past(b)) );

  // Default case behavior when op is X/Z last cycle
  ap_default_on_xop:    assert property ( $isunknown($past(op)) |-> result == 8'h00 );

  // No X/Z on result when prior inputs are known and division is legal
  ap_no_x_result:       assert property (
                           !$isunknown({$past(a),$past(b),$past(op)}) &&
                           !($past(op)==2'b11 && $past(b)==8'd0)
                         |-> !$isunknown(result)
                         );

  // Functional coverage
  cover_add:            cover property (op==2'b00);
  cover_sub:            cover property (op==2'b01);
  cover_mul:            cover property (op==2'b10);
  cover_div:            cover property (op==2'b11);

  cover_add_overflow:   cover property ( $past(op)==2'b00 && ({1'b0,$past(a)}+{1'b0,$past(b)} > 9'h0FF) );
  cover_sub_underflow:  cover property ( $past(op)==2'b01 && ($past(a) < $past(b)) );
  cover_mul_overflow:   cover property ( $past(op)==2'b10 && (($past(a)*$past(b)) > 16'h00FF) );
  cover_div0_attempt:   cover property ( op==2'b11 && b==8'd0 );

endmodule

bind calculator calculator_sva u_calculator_sva(.clk(clk), .a(a), .b(b), .op(op), .result(result));