// SVA for module four_to_one
module four_to_one_sva (
  input logic input1,
  input logic input2,
  input logic input3,
  input logic input4,
  input logic output1
);

  // Functional equivalence (4-state)
  always_comb begin
    assert #0 ( output1 === ( (input1 | input2 | input3 | input4) ? 1'b1 : 1'b0 ) )
      else $error("four_to_one: output1 mismatch: in=%b%b%b%b out=%b",
                   input1,input2,input3,input4,output1);
  end

  // Stronger implications and X-propagation sanity
  always_comb begin
    if (input1 || input2 || input3 || input4)
      assert #0 (output1 === 1'b1)
        else $error("four_to_one: some input=1 but output1!=1");
    if (!(input1 || input2 || input3 || input4) && !$isunknown({input1,input2,input3,input4}))
      assert #0 (output1 === 1'b0)
        else $error("four_to_one: all inputs=0 but output1!=0");
    if (!(input1 || input2 || input3 || input4) && $isunknown({input1,input2,input3,input4}))
      assert #0 ($isunknown(output1))
        else $error("four_to_one: X/Z inputs with no 1s should yield X on output1");
  end

  // Coverage: output toggles
  cover property (@(posedge output1) 1'b1);
  cover property (@(negedge output1) 1'b1);

  // Coverage: exactly one input high at output1 rise
  cover property (@(posedge output1)
                  (!$isunknown({input1,input2,input3,input4}) &&
                   $onehot({input1,input2,input3,input4})));

  // Coverage: multiple inputs high at output1 rise
  cover property (@(posedge output1)
                  (!$isunknown({input1,input2,input3,input4}) &&
                   ($countones({input1,input2,input3,input4}) >= 2)));

  // Coverage: all-zero case observed with output low
  cover property (@(input1 or input2 or input3 or input4 or output1)
                  (!$isunknown({input1,input2,input3,input4,output1}) &&
                   !input1 && !input2 && !input3 && !input4 && !output1));

endmodule

bind four_to_one four_to_one_sva u_four_to_one_sva (.*);