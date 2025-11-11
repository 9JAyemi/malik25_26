// SVA checker for adder_4bit
// Bind this module to the DUT. No clock required; properties trigger on input changes.
module adder_4bit_sva
(
  input logic        cin,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic        cout,
  input logic [3:0]  sum
);

  // 5-bit expected result
  function automatic logic [4:0] exp_sum(input logic [3:0] a, b, input logic cin);
    return ({1'b0,a} + {1'b0,b} + cin);
  endfunction

  // Knownness: if inputs are known, outputs must be known
  assert property (@(a or b or cin)
                   !$isunknown({cin,a,b}) |-> !$isunknown({cout,sum}))
    else $error("adder_4bit: X/Z on outputs with known inputs");

  // Functional correctness: outputs equal expected 5-bit sum (only when all signals are known)
  assert property (@(a or b or cin)
                   !$isunknown({cin,a,b,cout,sum}) |-> {cout,sum} == exp_sum(a,b,cin))
    else $error("adder_4bit: {cout,sum} != a+b+cin");

  // Optional sanity: carry matches overflow of 4-bit addition
  assert property (@(a or b or cin)
                   !$isunknown({cin,a,b,cout}) |-> cout == (exp_sum(a,b,cin) >= 5'd16))
    else $error("adder_4bit: cout mismatch");

  // Coverage: key corner cases and carry/no-carry scenarios
  cover property (@(a or b or cin) (a==4'd0 && b==4'd0 && cin==1'b0) && {cout,sum}==5'd0);       // zero + zero
  cover property (@(a or b or cin) (a==4'hF && b==4'hF && cin==1'b1) && cout==1'b1 && sum==4'hF); // max + max + cin
  cover property (@(a or b or cin) exp_sum(a,b,cin) <  5'd16 && cout==1'b0);                      // no carry
  cover property (@(a or b or cin) exp_sum(a,b,cin) >= 5'd16 && cout==1'b1);                      // carry
  cover property (@(a or b or cin) cin==1'b1);                                                    // cin usage

endmodule

// Bind into the DUT (connect by name)
bind adder_4bit adder_4bit_sva u_adder_4bit_sva (.cin(cin), .a(a), .b(b), .cout(cout), .sum(sum));