// SVA checkers and binds for the provided DUT

// Priority Encoder checker
module pe_sva (input [3:0] in, input [1:0] out);
  function automatic [1:0] pe_ref(input [3:0] i);
    pe_ref = (i==4'b0001) ? 2'b00 :
             (i==4'b0010) ? 2'b01 :
             (i==4'b0100) ? 2'b10 :
             (i==4'b1000) ? 2'b11 : 2'b11;
  endfunction

  // Functional correctness and no-X when input known
  assert property (@(*) !$isunknown(in) |-> out == pe_ref(in))
    else $error("PE mismatch: in=%b out=%b exp=%b", in, out, pe_ref(in));
  assert property (@(*) !$isunknown(in) |-> !$isunknown(out))
    else $error("PE X/Z out with known input");

  // Useful coverage
  cover property (@(*) in==4'b0001 && out==2'b00);
  cover property (@(*) in==4'b0010 && out==2'b01);
  cover property (@(*) in==4'b0100 && out==2'b10);
  cover property (@(*) in==4'b1000 && out==2'b11);
  cover property (@(*) in==4'b0000 && out==2'b11);
  cover property (@(*) $countones(in)>=2 && out==2'b11);
endmodule

// Ripple-Carry Adder checker
module rca_sva (input [3:0] A, B, input [3:0] SUM, input CARRY);
  assert property (@(*) !$isunknown({A,B}) |-> {CARRY,SUM} == A + B)
    else $error("RCA mismatch: A=%h B=%h SUM=%h CARRY=%b exp={%b,%h}",
                A, B, SUM, CARRY, (A+B)[4], (A+B)[3:0]);
  assert property (@(*) !$isunknown({A,B}) |-> !$isunknown({CARRY,SUM}))
    else $error("RCA X/Z outputs with known inputs");

  // Coverage (no/with carry, typical sums)
  cover property (@(*) A==4'h0 && B==4'h0 && SUM==4'h0 && !CARRY);
  cover property (@(*) A==4'hF && B==4'h1 && SUM==4'h0 && CARRY);
  cover property (@(*) A==4'hA && B==4'h5 && SUM==4'hF);
endmodule

// Functional combiner checker
module fm_sva (input [1:0] priority_output, input [3:0] ripple_sum, input [5:0] final_output);
  assert property (@(*) !$isunknown({priority_output,ripple_sum}) |-> final_output == {priority_output, ripple_sum})
    else $error("FM mismatch: prio=%b sum=%h final=%b", priority_output, ripple_sum, final_output);
  assert property (@(*) !$isunknown({priority_output,ripple_sum}) |-> !$isunknown(final_output))
    else $error("FM X/Z final_output with known inputs");

  // Coverage of MSBs and LSB extremes
  cover property (@(*) final_output[5:4]==2'b00);
  cover property (@(*) final_output[5:4]==2'b01);
  cover property (@(*) final_output[5:4]==2'b10);
  cover property (@(*) final_output[5:4]==2'b11);
  cover property (@(*) final_output[3:0]==4'h0);
  cover property (@(*) final_output[3:0]==4'hF);
endmodule

// Top-level end-to-end checker
module top_sva (
  input [3:0] in, input [3:0] A, B,
  input [5:0] final_output,
  input [1:0] priority_output,
  input [3:0] ripple_sum,
  input        carry
);
  function automatic [1:0] pe_ref(input [3:0] i);
    pe_ref = (i==4'b0001) ? 2'b00 :
             (i==4'b0010) ? 2'b01 :
             (i==4'b0100) ? 2'b10 :
             (i==4'b1000) ? 2'b11 : 2'b11;
  endfunction

  // End-to-end correctness when inputs known
  assert property (@(*) !$isunknown({in,A,B}) |-> final_output == {pe_ref(in), (A+B)[3:0]})
    else $error("TOP E2E mismatch: in=%b A=%h B=%h final=%b exp=%b", in, A, B, final_output, {pe_ref(in),(A+B)[3:0]});

  // Internal consistency
  assert property (@(*) final_output[5:4] == priority_output)
    else $error("TOP: MSBs mismatch with priority_output");
  assert property (@(*) final_output[3:0] == ripple_sum)
    else $error("TOP: LSBs mismatch with ripple_sum");
  assert property (@(*) !$isunknown({A,B}) |-> ripple_sum == (A+B)[3:0])
    else $error("TOP: ripple_sum mismatch vs A+B");
  assert property (@(*) !$isunknown({A,B}) |-> carry == (A+B)[4])
    else $error("TOP: carry mismatch vs A+B[4]");
  assert property (@(*) !$isunknown(in) |-> priority_output == pe_ref(in))
    else $error("TOP: priority_output mismatch vs pe_ref(in)");

  // Outputs known when inputs known
  assert property (@(*) !$isunknown({in,A,B}) |-> !$isunknown(final_output))
    else $error("TOP: final_output X/Z with known inputs");

  // Useful cross-coverage
  cover property (@(*) in==4'b0001 && A==4'hF && B==4'h1 &&
                          final_output[5:4]==2'b00 && final_output[3:0]==4'h0);
  cover property (@(*) $countones(in)>=2 && final_output[5:4]==2'b11);
endmodule

// Bind checkers to DUT modules
bind priority_encoder   pe_sva pe_sva_i ( .in(in), .out(out) );
bind ripple_carry_adder rca_sva rca_sva_i( .A(A), .B(B), .SUM(SUM), .CARRY(CARRY) );
bind functional_module  fm_sva  fm_sva_i( .priority_output(priority_output), .ripple_sum(ripple_sum), .final_output(final_output) );
bind top_module         top_sva top_sva_i(
  .in(in), .A(A), .B(B), .final_output(final_output),
  .priority_output(priority_output), .ripple_sum(ripple_sum), .carry(carry)
);