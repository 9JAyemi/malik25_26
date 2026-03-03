// SVA checker for adder_4bit_carry
module adder_4bit_carry_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       cin,
  input  logic [3:0] sum,
  input  logic       cout
);

  // Helpers
  let in_known = !$isunknown({a,b,cin});
  let exp5     = ({1'b0,a} + {1'b0,b} + cin);

  // Functional correctness (single concise check of full 5-bit result)
  assert property (@(*) in_known |-> {cout,sum} == exp5)
    else $error("Adder mismatch: a=%0h b=%0h cin=%0b -> sum=%0h cout=%0b (exp=%0h)",
                a, b, cin, sum, cout, exp5);

  // Outputs must be known when inputs are known
  assert property (@(*) in_known |-> !$isunknown({sum,cout}))
    else $error("Adder outputs X/Z with known inputs");

  // Basic scenario coverage
  cover property (@(*) in_known && cin==0 && cout==0);
  cover property (@(*) in_known && cin==0 && cout==1);
  cover property (@(*) in_known && cin==1 && cout==0);
  cover property (@(*) in_known && cin==1 && cout==1);

  // Corner cases
  cover property (@(*) in_known && a==4'h0 && b==4'h0 && cin==0 && sum==4'h0 && cout==0); // 0+0+0
  cover property (@(*) in_known && a==4'hF && b==4'h0 && cin==1 && sum==4'h0 && cout==1); // full propagate
  cover property (@(*) in_known && a==4'hF && b==4'hF && cin==0 && cout==1);              // overflow w/ cin=0
  cover property (@(*) in_known && {cout,sum} == 5'd31);                                   // max result (15+15+1)
  cover property (@(*) in_known && {cout,sum} == 5'd0);                                    // min result

  // Hit input extremes
  cover property (@(*) in_known && a==4'h0);
  cover property (@(*) in_known && a==4'hF);
  cover property (@(*) in_known && b==4'h0);
  cover property (@(*) in_known && b==4'hF);

endmodule

// Bind into DUT
bind adder_4bit_carry adder_4bit_carry_sva i_adder_4bit_carry_sva (.*);