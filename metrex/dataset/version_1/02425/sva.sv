// SVA for rca_top: concise, full functional checks + key coverage
module rca_top_sva(
  input logic [15:0] input1,
  input logic [15:0] input2,
  input logic [15:0] final_output,
  input logic        carry_output
);
  default clocking cb @(*); endclocking

  // Expected 17-bit result
  let exp_sum17 = {1'b0, input1} + {1'b0, input2};

  // Core functional correctness
  assert property ( {carry_output, final_output} == exp_sum17 )
    else $error("rca_top: sum mismatch: %0h + %0h => got {%0b,%0h} exp {%0b,%0h}",
                input1, input2, carry_output, final_output, exp_sum17[16], exp_sum17[15:0]);

  // No X/Z on outputs when inputs are known
  assert property ( (!$isunknown({input1,input2})) |-> (!$isunknown({carry_output,final_output})) )
    else $error("rca_top: X/Z on outputs with known inputs");

  // Identity (add zero)
  assert property ( (input1==16'h0000) |-> ({carry_output,final_output} == {1'b0,input2}) )
    else $error("rca_top: 0 + B != B");
  assert property ( (input2==16'h0000) |-> ({carry_output,final_output} == {1'b0,input1}) )
    else $error("rca_top: A + 0 != A");

  // Corner: max + max
  assert property ( (input1==16'hFFFF && input2==16'hFFFF)
                    |-> ({carry_output,final_output} == 17'h1_FFFE) )
    else $error("rca_top: FFFF + FFFF corner failed");

  // -----------------------------------
  // Coverage (key scenarios and carries)
  // -----------------------------------
  // Carry-out seen / not seen
  cover property ( carry_output );
  cover property ( !carry_output );

  // Zero + Zero
  cover property ( input1==16'h0000 && input2==16'h0000 &&
                   final_output==16'h0000 && carry_output==1'b0 );

  // A + ~A => 0xFFFF, no carry
  cover property ( (input1 == ~input2) && final_output==16'hFFFF && carry_output==1'b0 );

  // Max + Max => carry and 0xFFFE
  cover property ( input1==16'hFFFF && input2==16'hFFFF &&
                   carry_output==1'b1 && final_output==16'hFFFE );

  // Propagation across 4-bit block boundaries
  cover property ( input1==16'h000F && input2==16'h0001 &&
                   final_output==16'h0010 && carry_output==1'b0 );
  cover property ( input1==16'h00FF && input2==16'h0001 &&
                   final_output==16'h0100 && carry_output==1'b0 );
  cover property ( input1==16'h0FFF && input2==16'h0001 &&
                   final_output==16'h1000 && carry_output==1'b0 );
endmodule

// Bind into DUT
bind rca_top rca_top_sva rca_top_sva_i(.*);