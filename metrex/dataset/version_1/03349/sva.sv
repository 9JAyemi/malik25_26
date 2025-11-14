// SVA for rem_charmatch
// Bind this module to the DUT to check internals.
module rem_charmatch_assertions
(
  input  logic        clk,
  input  logic        rst,
  input  logic        config_valid,
  input  logic [7:0]  config_char,
  input  logic        config_chained,
  input  logic        input_valid,
  input  logic [7:0]  input_char,
  input  logic        prev_matched,
  input  logic        this_matched,
  input  logic        char_match,    // internal
  input  logic [7:0]  char_data,     // internal
  input  logic        is_chained     // internal
);

  default clocking cb @(posedge clk); endclocking

  // Reset values
  assert property (rst |-> (char_data==8'h00 && char_match==1'b0 && this_matched==1'b0));

  // Output wiring
  assert property (disable iff (rst) (this_matched == char_match));

  // Config side-effects (priority over input)
  assert property (disable iff (rst)
                   config_valid |-> ##1 (char_data==$past(config_char) &&
                                          is_chained==$past(config_chained) &&
                                          char_match==1'b0));

  // Config has priority when both input_valid & config_valid
  assert property (disable iff (rst)
                   (input_valid && config_valid) |-> ##1 (char_match==1'b0));

  // State only updates when driven
  assert property (disable iff (rst) (!config_valid) |-> ##1 $stable(char_data));
  assert property (disable iff (rst) (!config_valid) |-> ##1 $stable(is_chained));
  assert property (disable iff (rst) (!input_valid && !config_valid) |-> ##1 $stable(char_match));

  // Match behavior: on input_valid without config
  // Mismatch -> 0
  assert property (disable iff (rst)
                   (input_valid && !config_valid && (char_data != input_char)) |-> ##1 (char_match==1'b0));
  // Equal and unchained -> 1
  assert property (disable iff (rst)
                   (input_valid && !config_valid && (char_data == input_char) && !is_chained) |-> ##1 (char_match==1'b1));
  // Equal and chained -> prev_matched
  assert property (disable iff (rst)
                   (input_valid && !config_valid && (char_data == input_char) &&  is_chained) |-> ##1 (char_match==prev_matched));

  // this_matched can only go 1 for legal reasons (previous cycle conditions)
  assert property (disable iff (rst)
                   this_matched |-> ($past(input_valid && !config_valid) &&
                                     ($past(char_data)==$past(input_char)) &&
                                     (!$past(is_chained) ||  $past(prev_matched))));

  // Knownness: output never X/Z; is_chained must be known when used
  assert property (disable iff (rst) !$isunknown(this_matched));
  assert property (disable iff (rst)
                   (input_valid && !config_valid && (char_data==input_char)) |-> !$isunknown(is_chained));

  // Key coverage
  // 1) Unchained config then matching input -> match=1
  cover property (disable iff (rst)
                  config_valid && !config_chained ##1
                  input_valid && (input_char==char_data) && !config_valid ##1
                  this_matched);

  // 2) Chained config, then two inputs: first prev_matched=0 (no match), then prev_matched=1 (match)
  cover property (disable iff (rst)
                  config_valid && config_chained ##1
                  input_valid && (input_char==char_data) && !config_valid && (prev_matched==1'b0) ##1
                  (this_matched==1'b0) ##1
                  input_valid && (input_char==char_data) && !config_valid && (prev_matched==1'b1) ##1
                  (this_matched==1'b1));

  // 3) Simultaneous config and matching input -> cleared by config
  cover property (disable iff (rst)
                  (input_valid && config_valid && (char_data==input_char)) ##1 (char_match==1'b0));

endmodule

// Example bind (place in a package or a separate file compiled after DUT)
// bind rem_charmatch rem_charmatch_assertions rcm_sva (.*);