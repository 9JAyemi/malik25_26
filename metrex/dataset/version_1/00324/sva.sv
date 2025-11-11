// SVA for four_to_one. Bind this to the DUT.

module four_to_one_sva (
  input logic in1,
  input logic in2,
  input logic in3,
  input logic in4,
  input logic out
);

  default clocking cb @(*); endclocking

  // Functional equivalence (including X propagation semantics)
  assert property (out === (in1 || in2 || in3));

  // Output never depends on in4 alone
  assert property ( ($changed(in4) && $stable({in1,in2,in3})) |-> $stable(out) );

  // Output changes only if in1..in3 change
  assert property ( $changed(out) |-> $changed({in1,in2,in3}) );

  // No 'Z' on output
  assert property (!(out === 1'bz));

  // X-propagation: if no definite '1' on in1..in3 and some X/Z present, out must be X
  assert property ( !((in1===1'b1)||(in2===1'b1)||(in3===1'b1)) && $isunknown({in1,in2,in3}) |-> $isunknown(out) );

  // Coverage
  cover property (out===1'b0);
  cover property (out===1'b1);
  cover property ( (in1===1'b1)&&(in2!==1'b1)&&(in3!==1'b1) && out===1'b1 );
  cover property ( (in2===1'b1)&&(in1!==1'b1)&&(in3!==1'b1) && out===1'b1 );
  cover property ( (in3===1'b1)&&(in1!==1'b1)&&(in2!==1'b1) && out===1'b1 );
  cover property ( (((in1===1'b1)&&(in2===1'b1)) || ((in1===1'b1)&&(in3===1'b1)) || ((in2===1'b1)&&(in3===1'b1))) && out===1'b1 );
  cover property ( !((in1===1'b1)||(in2===1'b1)||(in3===1'b1)) && $isunknown({in1,in2,in3}) && $isunknown(out) );
  cover property ( $changed(out) );
  cover property ( $changed(in4) && $stable({in1,in2,in3}) && $stable(out) );

endmodule

bind four_to_one four_to_one_sva sva_i(.in1(in1),.in2(in2),.in3(in3),.in4(in4),.out(out));