// SVA for and_gate: concise, high-quality checks and coverage

module and_gate_sva (input logic [3:0] a, b, input logic [3:0] c);

  // Functional correctness (race-free with ##0)
  property p_func;
    @(a or b or c) 1'b1 |-> ##0 (c === (a & b));
  endproperty
  assert property (p_func);

  // No X on c when inputs are known
  property p_known;
    @(a or b or c) !$isunknown({a,b}) |-> ##0 (!$isunknown(c) && (c == (a & b)));
  endproperty
  assert property (p_known);

  // Output changes only when inputs change
  property p_no_spurious_c;
    @(c) 1'b1 |-> ##0 ($changed(a) || $changed(b));
  endproperty
  assert property (p_no_spurious_c);

  // Per-bit functional coverage for all input combinations + edge coverage
  genvar i;
  for (i = 0; i < 4; i++) begin : GEN_COV
    cover property (@(a[i] or b[i] or c[i]) 1'b1 |-> ##0 (a[i]==0 && b[i]==0 && c[i]==0));
    cover property (@(a[i] or b[i] or c[i]) 1'b1 |-> ##0 (a[i]==0 && b[i]==1 && c[i]==0));
    cover property (@(a[i] or b[i] or c[i]) 1'b1 |-> ##0 (a[i]==1 && b[i]==0 && c[i]==0));
    cover property (@(a[i] or b[i] or c[i]) 1'b1 |-> ##0 (a[i]==1 && b[i]==1 && c[i]==1));
    cover property (@(a[i] or b[i] or c[i]) 1'b1 |-> ##0 $rose(c[i]));
    cover property (@(a[i] or b[i] or c[i]) 1'b1 |-> ##0 $fell(c[i]));
  end

  // Corner vector coverage
  cover property (@(a or b or c) 1'b1 |-> ##0 (a==4'h0 && b==4'h0 && c==4'h0));
  cover property (@(a or b or c) 1'b1 |-> ##0 (a==4'hF && b==4'hF && c==4'hF));
  cover property (@(a or b or c) 1'b1 |-> ##0 (a==4'hA && b==4'h5 && c==4'h0));
  cover property (@(a or b or c) 1'b1 |-> ##0 (a==4'hF && b==4'h0 && c==4'h0));

endmodule

bind and_gate and_gate_sva i_and_gate_sva(.a(a), .b(b), .c(c));