// SVA for ripple_adder_mux (binds into the DUT scope to see internals)
module ripple_adder_mux_sva;
  // Sample on any combinational change
  default clocking cb @(*); endclocking

  // Known input guard
  property p_known_inputs; !$isunknown({A,B,cin,select}); endproperty

  // Adder correctness (full 5-bit result)
  assert property (p_known_inputs |-> {cout,sum} == A + B + cin)
    else $error("Adder mismatch: {cout,sum} != A+B+cin");

  // Mux correctness vs internal sum/constant
  assert property (p_known_inputs &&  select |-> out == sum)
    else $error("Mux sel=1: out != sum");
  assert property (p_known_inputs && !select |-> out == constant_value)
    else $error("Mux sel=0: out != constant_value");

  // Functional spec check vs recomputed adder (black-box check)
  assert property (p_known_inputs |-> out == (select ? (A+B+cin)[3:0] : 4'hF))
    else $error("Spec mismatch: out != mux(select, 4'hF, (A+B+cin)[3:0])");

  // No X/Z on outputs when inputs are known
  assert property (p_known_inputs |-> !$isunknown({sum,cout,out}))
    else $error("X/Z on outputs with known inputs");

  // Sanity: constant is as intended
  assert property (constant_value == 4'hF)
    else $error("constant_value != 4'hF");

  // Coverage (key scenarios)
  cover property (select==0 && out==4'hF);                // mux to constant
  cover property (select==1 && (A+B+cin)==5'd0);          // zero sum
  cover property (select==1 && (A+B+cin)[4]==1'b1);       // carry out
  cover property (select==1 && (A+B+cin)[3:0]==4'hF &&
                                  (A+B+cin)[4]==1'b0);    // sum=0xF, no carry
  cover property (select==1 && A==4'hF && B==4'hF && cin);// worst-case add
endmodule

bind ripple_adder_mux ripple_adder_mux_sva sva_ripple_adder_mux();