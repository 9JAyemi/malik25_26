// SVA for calculator_fixed
// Bind this file to the DUT:  bind calculator_fixed calculator_fixed_sva sva();

module calculator_fixed_sva;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helpers
  let ext1 = {4'b0, num1};
  let ext2 = {4'b0, num2};

  function automatic [7:0] exp_tr (input [3:0] a, b, input [1:0] o);
    case (o)
      2'b00: exp_tr = {4'b0,a} + {4'b0,b};
      2'b01: exp_tr = {4'b0,a} - {4'b0,b};
      2'b10: exp_tr = {4'b0,a} * {4'b0,b};
      2'b11: exp_tr = (b != 0) ? ({4'b0,a} / {4'b0,b}) : 8'hxx;
      default: exp_tr = 8'hxx;
    endcase
  endfunction

  // Reset behavior
  assert property (@cb rst |=> (temp_result==8'h00 && temp_display==4'h0 && result==4'h0 && display==4'h0));

  // Illegal operation
  assert property (@cb !(op==2'b11 && num2==4'h0)) else $error("Divide-by-zero detected");

  // Arithmetic correctness (sampled 1 cycle later)
  assert property (@cb (op==2'b00) |=> (temp_result == (ext1 + ext2)) && (result == (ext1 + ext2)[3:0]));
  assert property (@cb (op==2'b01) |=> (temp_result == (ext1 - ext2)) && (result == (ext1 - ext2)[3:0]));
  assert property (@cb (op==2'b10) |=> (temp_result == (ext1 * ext2)) && (result == (ext1 * ext2)[3:0]));
  assert property (@cb (op==2'b11 && num2!=0) |=> (temp_result == (ext1 / ext2)) && (result == (ext1 / ext2)[3:0]));

  // Display pipeline: display shows previous result nibble
  assert property (@cb $past(!rst) |-> (display == $past(result)));

  // Display formatting intent (flags truncation/intent mismatches)
  assert property (@cb $past(!rst) && (op==2'b10)
                   |-> (display == exp_tr($past(num1),$past(num2),$past(op))[3:0]));
  assert property (@cb $past(!rst) && (op==2'b00)
                   |-> ({1'b0,display} == {1'b0, exp_tr($past(num1),$past(num2),$past(op))[3:0]}));
  assert property (@cb $past(!rst) && (op==2'b11) && ($past(num2)!=0)
                   |-> ({1'b0,display} == {1'b0, exp_tr($past(num1),$past(num2),$past(op))[3:0]}));
  assert property (@cb $past(!rst) && (op==2'b01)
                   |-> ({1'b0,display} == {exp_tr($past(num1),$past(num2),$past(op))[7],
                                            exp_tr($past(num1),$past(num2),$past(op))[3:0]}));

  // Knownness on outputs
  assert property (@cb !$isunknown({result, display}));

  // Coverage
  cover property (@cb !rst ##1 op==2'b00);
  cover property (@cb !rst ##1 op==2'b01);
  cover property (@cb !rst ##1 op==2'b10);
  cover property (@cb !rst ##1 op==2'b11 && num2!=0);
  cover property (@cb (op==2'b01) ##1 exp_tr($past(num1),$past(num2),$past(op))[7]==1'b1); // sub negative
  cover property (@cb (op==2'b10) ##1 (exp_tr($past(num1),$past(num2),$past(op))[7:4] != 4'h0)); // mul overflow high nibble
  cover property (@cb (op==2'b11) && (num2==0)); // div-by-zero stimulus observed

endmodule

bind calculator_fixed calculator_fixed_sva sva();