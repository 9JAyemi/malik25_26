// SVA for bitwise_and
module bitwise_and_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [3:0] and_result
);

  // Functional correctness (avoid preponed sampling with ##0)
  property p_and_correct;
    @(a or b or and_result) 1'b1 |-> ##0 (and_result === (a & b));
  endproperty
  assert property (p_and_correct)
    else $error("bitwise_and: and_result != (a & b)");

  // No X/Z on output when inputs are known 0/1
  property p_no_x_when_inputs_known;
    @(a or b or and_result) (!$isunknown(a) && !$isunknown(b)) |-> ##0 !$isunknown(and_result);
  endproperty
  assert property (p_no_x_when_inputs_known)
    else $error("bitwise_and: X/Z on output while inputs are known");

  // Per-bit truth-table coverage (all four input combos)
  genvar i;
  for (i = 0; i < 4; i++) begin : g_cov
    cover property (@(a[i] or b[i]) ##0 (a[i]===1'b0 && b[i]===1'b0 && and_result[i]===1'b0));
    cover property (@(a[i] or b[i]) ##0 (a[i]===1'b0 && b[i]===1'b1 && and_result[i]===1'b0));
    cover property (@(a[i] or b[i]) ##0 (a[i]===1'b1 && b[i]===1'b0 && and_result[i]===1'b0));
    cover property (@(a[i] or b[i]) ##0 (a[i]===1'b1 && b[i]===1'b1 && and_result[i]===1'b1));
  end

  // Aggregate edge-case coverage
  cover property (@(a or b) ##0 (a===4'h0 && b===4'h0 && and_result===4'h0));
  cover property (@(a or b) ##0 (a===4'hF && b===4'hF && and_result===4'hF));
  cover property (@(a or b) ##0 (a===4'hF && b===4'h0 && and_result===4'h0));
  cover property (@(a or b) ##0 (a===4'h0 && b===4'hF && and_result===4'h0));

endmodule

bind bitwise_and bitwise_and_sva sva_inst (.a(a), .b(b), .and_result(and_result));