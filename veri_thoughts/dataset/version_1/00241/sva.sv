// SVA for adder_4bit_carry
module adder_4bit_carry_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic       cin,
  input logic [3:0] sum,
  input logic       cout
);

  function automatic logic [4:0] ref_sum (input logic [3:0] fa,
                                          input logic [3:0] fb,
                                          input logic       fcin);
    ref_sum = {1'b0,fa} + {1'b0,fb} + fcin;
  endfunction

  // Functional equivalence (checked after delta to avoid preponed sampling races)
  property p_functional_correct;
    @(a or b or cin)
      !($isunknown({a,b,cin})) |-> ##0 ({cout,sum} == ref_sum(a,b,cin));
  endproperty
  assert property (p_functional_correct)
    else $error("Adder mismatch: a=%0h b=%0h cin=%0b -> sum=%0h cout=%0b (ref=%0h)",
                a,b,cin,sum,cout,ref_sum(a,b,cin));

  // Known outputs when inputs are known
  property p_known_out_when_known_in;
    @(a or b or cin)
      !($isunknown({a,b,cin})) |-> ##0 !($isunknown({sum,cout}));
  endproperty
  assert property (p_known_out_when_known_in)
    else $error("Unknown/Z outputs with known inputs: a=%0h b=%0h cin=%0b sum=%0h cout=%0b",
                a,b,cin,sum,cout);

  // Optional: explicit carry correctness (redundant but isolates cout)
  property p_carry_bit_correct;
    @(a or b or cin)
      !($isunknown({a,b,cin})) |-> ##0 (cout == ref_sum(a,b,cin)[4]);
  endproperty
  assert property (p_carry_bit_correct)
    else $error("Carry bit incorrect: a=%0h b=%0h cin=%0b cout=%0b (ref_cout=%0b)",
                a,b,cin,cout,ref_sum(a,b,cin)[4]);

  // Coverage: key scenarios and extremes
  cover property (@(a or b or cin) (cin==1'b0));
  cover property (@(a or b or cin) (cin==1'b1));

  cover property (@(a or b or cin) ##0 (!cout));          // no carry
  cover property (@(a or b or cin) ##0 (cout));           // carry out

  cover property (@(a or b or cin) (a==4'h0 && b==4'h0 && cin==1'b0)); // 0+0+0
  cover property (@(a or b or cin) (a==4'hF && b==4'hF && cin==1'b1)); // 15+15+1

  cover property (@(a or b or cin) ##0 ({cout,sum} == 5'd0));  // result 0
  cover property (@(a or b or cin) ##0 ({cout,sum} == 5'd16)); // result 16 (sum=0, cout=1)
  cover property (@(a or b or cin) ##0 (cout && (sum!=4'h0))); // carry with nonzero sum
  cover property (@(a or b or cin) ##0 (!cout && (sum==4'hF))); // max sum without carry

endmodule

// Bind into DUT
bind adder_4bit_carry adder_4bit_carry_sva adder_4bit_carry_sva_i (.*);