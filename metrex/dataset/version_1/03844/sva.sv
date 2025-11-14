// SVA for count_ones: concise, combinational, full functional check and coverage
module count_ones_sva (
  input logic a,
  input logic b,
  input logic c,
  input logic [1:0] count
);

  // Functional correctness: when inputs are known, count equals number of 1s
  property p_correct_count;
    @(a or b or c)
      !$isunknown({a,b,c}) |-> ##0 (count == (a + b + c));
  endproperty
  assert property (p_correct_count);

  // No-glitch output: with stable, known inputs, output must stay stable
  property p_glitch_free;
    @(a or b or c or count)
      (!$isunknown({a,b,c}) && $stable({a,b,c})) |-> ##0 $stable(count);
  endproperty
  assert property (p_glitch_free);

  // Functional coverage: each input combination produces its expected count
  cover property (@(a or b or c) ({a,b,c}==3'b000) ##0 (count==2'b00));
  cover property (@(a or b or c) ({a,b,c}==3'b001) ##0 (count==2'b01));
  cover property (@(a or b or c) ({a,b,c}==3'b010) ##0 (count==2'b01));
  cover property (@(a or b or c) ({a,b,c}==3'b011) ##0 (count==2'b10));
  cover property (@(a or b or c) ({a,b,c}==3'b100) ##0 (count==2'b01));
  cover property (@(a or b or c) ({a,b,c}==3'b101) ##0 (count==2'b10));
  cover property (@(a or b or c) ({a,b,c}==3'b110) ##0 (count==2'b10));
  cover property (@(a or b or c) ({a,b,c}==3'b111) ##0 (count==2'b11));

endmodule

// Bind into DUT
bind count_ones count_ones_sva sva_i (.*);