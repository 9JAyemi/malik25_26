// SVA for LLbit_reg: concise, full next-state check, change qualification, and coverage.
module LLbit_reg_sva (
  input logic clk,
  input logic rst,
  input logic flush,
  input logic LLbit_i,
  input logic we,
  input logic LLbit_o
);
  default clocking cb @(posedge clk); endclocking

  // Golden next-state function (priority: rst > flush > we > hold)
  property p_next_state;
    1'b1 |=> LLbit_o ==
      ( $past(rst)   ? 1'b0 :
        $past(flush) ? 1'b0 :
        $past(we)    ? $past(LLbit_i) :
                       $past(LLbit_o) );
  endproperty
  assert property (p_next_state);

  // Output changes only when driven by rst/flush/we in prior cycle
  property p_only_changes_on_event;
    $changed(LLbit_o) |-> ($past(rst) || $past(flush) || ($past(we) && !$past(rst) && !$past(flush)));
  endproperty
  assert property (p_only_changes_on_event);

  // Output is known when not in reset
  assert property (!rst |-> !$isunknown(LLbit_o));

  // Coverage
  cover property (rst ##1 (LLbit_o == 1'b0));                             // reset clears
  cover property (!rst && flush ##1 (LLbit_o == 1'b0));                   // flush clears
  cover property (!rst && flush && we ##1 (LLbit_o == 1'b0));             // flush priority over we
  cover property (!rst && !flush && we && (LLbit_i == 1'b1) ##1 (LLbit_o == 1'b1)); // write 1
  cover property (!rst && !flush && we && (LLbit_i == 1'b0) ##1 (LLbit_o == 1'b0)); // write 0
  cover property (!rst && !flush && !we ##1 (LLbit_o == $past(LLbit_o))); // hold

endmodule

// Bind into DUT
bind LLbit_reg LLbit_reg_sva sva (
  .clk(clk),
  .rst(rst),
  .flush(flush),
  .LLbit_i(LLbit_i),
  .we(we),
  .LLbit_o(LLbit_o)
);