// SVA binders for top_module
// Concise end-to-end checks and coverage of all important behaviors.

bind top_module top_module_sva i_top_module_sva(
  .A(A),
  .B(B),
  .C(C),
  .multiplier_output(multiplier_output),
  .comparator_output(comparator_output),
  .final_output(final_output)
);

module top_module_sva(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [7:0] C,
  input  logic [7:0] multiplier_output,
  input  logic [1:0] comparator_output,
  input  logic [7:0] final_output
);
  // Use global clock for concurrent SVA; ##0 defers to end of delta for stable combinational checks
  default clocking cb @(posedge $global_clock); endclocking

  // Known-ness guards
  wire inputs_known = !$isunknown({A,B,C});
  wire mul_known    = !$isunknown({A,B});
  wire comp_known   = !$isunknown({multiplier_output,C});
  wire func_known   = !$isunknown({multiplier_output,comparator_output});

  // Multiplier correctness
  assert property (mul_known |-> ##0 (multiplier_output == (A * B)))
    else $error("Multiplier mismatch: A=%0d B=%0d got=%0d exp=%0d", A, B, multiplier_output, A*B);

  // Comparator legality and exact encoding
  assert property (comp_known |-> ##0 (comparator_output inside {2'b00,2'b01,2'b10}))
    else $error("Comparator illegal code: %b", comparator_output);

  assert property (comp_known |-> ##0 ((multiplier_output == C) == (comparator_output == 2'b00)))
    else $error("Comparator EQ encoding wrong: prod=%0d C=%0d code=%b", multiplier_output, C, comparator_output);

  assert property (comp_known |-> ##0 ((multiplier_output >  C) == (comparator_output == 2'b01)))
    else $error("Comparator GT encoding wrong: prod=%0d C=%0d code=%b", multiplier_output, C, comparator_output);

  assert property (comp_known |-> ##0 ((multiplier_output <  C) == (comparator_output == 2'b10)))
    else $error("Comparator LT encoding wrong: prod=%0d C=%0d code=%b", multiplier_output, C, comparator_output);

  // Functional module correctness (final output add with zero-extended comparator)
  assert property (func_known |-> ##0 (final_output == (multiplier_output + {2'b00, comparator_output})))
    else $error("Final output mismatch: mult=%0d comp=%b got=%0d exp=%0d",
                multiplier_output, comparator_output, final_output,
                multiplier_output + {2'b00, comparator_output});

  // Cross-check equivalence path (optional redundancy but strengthens end-to-end)
  assert property (inputs_known |-> ##0 (final_output ==
                    (A*B + {2'b00, comparator_output})))
    else $error("End-to-end mismatch via A*B path");

  // Functional coverage
  cover property (mul_known    && (multiplier_output == 8'd0));     // 0*X or X*0
  cover property (mul_known    && (multiplier_output == 8'd225));   // 15*15 max
  cover property (comp_known   && (comparator_output == 2'b00) && (multiplier_output == C));       // EQ
  cover property (comp_known   && (comparator_output == 2'b01) && (multiplier_output == C + 8'd1)); // GT boundary
  cover property (comp_known   && (comparator_output == 2'b10) && (multiplier_output + 8'd1 == C)); // LT boundary
  cover property (func_known   && (comparator_output == 2'b00) && (final_output == multiplier_output));
  cover property (func_known   && (comparator_output == 2'b01) && (final_output == multiplier_output + 8'd1));
  cover property (func_known   && (comparator_output == 2'b10) && (final_output == multiplier_output + 8'd2));
endmodule