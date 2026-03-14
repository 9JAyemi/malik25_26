module multifunction_module_sva (
  input  logic clk,
  input  logic input_signal_1,
  input  logic input_signal_2,
  input  logic input_signal_3,
  input  logic input_signal_4,
  input  logic input_signal_5,
  input  logic output_signal
);
  // Local aliases for readability
  logic t_abcd;
  logic t1, t2, t3;

  assign t_abcd = input_signal_1 & input_signal_2 & input_signal_3 & input_signal_4;
  assign t1     = input_signal_1 & ~input_signal_2;
  assign t2     = ~input_signal_3 & input_signal_4;
  assign t3     = input_signal_5 ^ t_abcd;

  // Output equals the defined Boolean function.
  check_output_function: assert property (
    @(posedge clk) output_signal == (t1 | t2 | t3)
  );

  // If (input_signal_1 & ~input_signal_2) is true, output must be HIGH.
  check_term1_implies_output_high: assert property (
    @(posedge clk) t1 |-> output_signal
  );

  // If (~input_signal_3 & input_signal_4) is true, output must be HIGH.
  check_term2_implies_output_high: assert property (
    @(posedge clk) t2 |-> output_signal
  );

  // If (input_signal_5 ^ (input_signal_1&2&3&4)) is true, output must be HIGH.
  check_xor_term_implies_output_high: assert property (
    @(posedge clk) t3 |-> output_signal
  );

  // If all three terms are LOW, output must be LOW.
  check_all_terms_low_implies_output_low: assert property (
    @(posedge clk) (!t1 && !t2 && !t3) |-> (output_signal == 1'b0)
  );

  // Output HIGH implies at least one term is HIGH.
  check_output_high_implies_some_term_high: assert property (
    @(posedge clk) output_signal |-> (t1 || t2 || t3)
  );

  // Output LOW implies all terms are LOW.
  check_output_low_implies_no_term_high: assert property (
    @(posedge clk) !output_signal |-> (!t1 && !t2 && !t3)
  );

  // When input_signal_1&2&3&4 is HIGH, output equals ~input_signal_5.
  check_abcd_high_implies_output_not_e: assert property (
    @(posedge clk) t_abcd |-> (output_signal == ~input_signal_5)
  );

  // When input_signal_1&2&3&4 is LOW and other terms are LOW, output equals input_signal_5.
  check_abcd_low_and_no_other_terms_implies_output_e: assert property (
    @(posedge clk) (!t_abcd && !t1 && !t2) |-> (output_signal == input_signal_5)
  );

  // When the first two terms are LOW, output equals (input_signal_5 ^ (input_signal_1&2&3&4)).
  check_only_xor_drives_when_other_terms_low: assert property (
    @(posedge clk) (!t1 && !t2) |-> (output_signal == (input_signal_5 ^ t_abcd))
  );

endmodule