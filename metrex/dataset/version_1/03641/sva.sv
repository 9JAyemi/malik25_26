// bitwise_operations_sva.sv
// Bind-only, concise, high-quality SVA for full functional checking and basic coverage

// synthesis translate_off
bind bitwise_operations bitwise_operations_sva sva_inst();
// synthesis translate_on

module bitwise_operations_sva;

  // Helper: inputs known
  function automatic bit inputs_known();
    return !$isunknown({a,b,operation_select,shift_amount});
  endfunction

  // Disallow X/Z on select (avoids latch/incomplete case behavior)
  assert property (@(operation_select) !$isunknown(operation_select))
    else $error("operation_select contains X/Z");

  // Result must be known if inputs are known
  assert property (@(a or b or operation_select or shift_amount or result)
                   inputs_known() |-> ##0 !$isunknown(result))
    else $error("result has X/Z when inputs are known");

  // Internal wire correctness
  assert property (@(a or b) ##0 and_result  == (a &  b))
    else $error("and_result mismatch");
  assert property (@(a or b) ##0 or_result   == (a |  b))
    else $error("or_result mismatch");
  assert property (@(a or b) ##0 xor_result  == (a ^  b))
    else $error("xor_result mismatch");
  assert property (@(a or shift_amount) ##0 shift_result == (a << shift_amount))
    else $error("shift_result mismatch");

  // Output functional correctness (evaluate after delta to avoid race/glitch)
  assert property (@(a or b or operation_select or shift_amount or result)
                   inputs_known() && operation_select==2'b00 |-> ##0 result == (a & b))
    else $error("AND operation mismatch");
  assert property (@(a or b or operation_select or shift_amount or result)
                   inputs_known() && operation_select==2'b01 |-> ##0 result == (a | b))
    else $error("OR operation mismatch");
  assert property (@(a or b or operation_select or shift_amount or result)
                   inputs_known() && operation_select==2'b10 |-> ##0 result == (a ^ b))
    else $error("XOR operation mismatch");
  assert property (@(a or b or operation_select or shift_amount or result)
                   inputs_known() && operation_select==2'b11 |-> ##0 result == (a << shift_amount))
    else $error("SHIFT operation mismatch");

  // Stability: with all inputs stable, result must be stable
  assert property (@(a or b or operation_select or shift_amount or result)
                   inputs_known() && $stable({a,b,operation_select,shift_amount}) |-> ##0 $stable(result))
    else $error("result glitches while inputs stable");

  // Basic functional coverage
  cover property (@(operation_select) operation_select==2'b00);
  cover property (@(operation_select) operation_select==2'b01);
  cover property (@(operation_select) operation_select==2'b10);
  cover property (@(operation_select) operation_select==2'b11);

  // Shift edge cases
  cover property (@(shift_amount or operation_select)
                  operation_select==2'b11 && shift_amount==5'd0);
  cover property (@(shift_amount or operation_select)
                  operation_select==2'b11 && shift_amount==5'd31);

  // Interesting data patterns per op
  cover property (@(a or b or operation_select)
                  operation_select==2'b10 && a==b ##0 result==32'h0);           // XOR cancel
  cover property (@(a or b or operation_select)
                  operation_select==2'b00 && &a && &b ##0 result==32'hFFFF_FFFF); // AND all-ones
  cover property (@(a or b or operation_select)
                  operation_select==2'b01 && (a==32'h0 && b==32'h0) ##0 result==32'h0); // OR zeros

endmodule