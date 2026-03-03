// SVA for threshold_module
module threshold_module_sva #(parameter int THRESHOLD = 10)
(
  input  logic [3:0] input_value,
  input  logic [1:0] output_value
);

  // sampling event for combinational changes
  event comb_ev; always @* -> comb_ev;

  // predicates
  let le5 = (input_value <= 4'd5);
  let geT = (input_value >= THRESHOLD);
  let mid = (!le5 && !geT);

  // legality
  assert property (@(comb_ev) !$isunknown(output_value));
  assert property (@(comb_ev) output_value inside {2'b00,2'b01,2'b10});

  // forward mapping (input -> output), only when input known
  assert property (@(comb_ev) !$isunknown(input_value) && le5 |-> output_value == 2'b00);
  assert property (@(comb_ev) !$isunknown(input_value) && geT |-> output_value == 2'b10);
  assert property (@(comb_ev) !$isunknown(input_value) && mid |-> output_value == 2'b01);

  // reverse mapping (output -> input), only when input/output known
  assert property (@(comb_ev) !$isunknown({input_value,output_value}) && output_value == 2'b00 |-> le5);
  assert property (@(comb_ev) !$isunknown({input_value,output_value}) && output_value == 2'b10 |-> geT);
  assert property (@(comb_ev) !$isunknown({input_value,output_value}) && output_value == 2'b01 |-> mid);

  // functional determinism: same input => same output
  assert property (@(comb_ev)
                   !$isunknown(input_value) && !$isunknown($past(input_value)) &&
                   input_value == $past(input_value)
                   |-> output_value == $past(output_value));

  // coverage: regions hit
  cover property (@(comb_ev) !$isunknown({input_value,output_value}) && le5 && output_value == 2'b00);
  cover property (@(comb_ev) !$isunknown({input_value,output_value}) && mid && output_value == 2'b01);
  cover property (@(comb_ev) !$isunknown({input_value,output_value}) && geT && output_value == 2'b10);

  // coverage: boundaries
  cover property (@(comb_ev) !$isunknown({input_value,output_value}) && input_value == 4'd5 && output_value == 2'b00);
  cover property (@(comb_ev) (THRESHOLD > 6) && !$isunknown({input_value,output_value}) &&
                              input_value == 4'd6 && output_value == 2'b01);
  cover property (@(comb_ev) (THRESHOLD >= 0 && THRESHOLD <= 15) && !$isunknown({input_value,output_value}) &&
                              input_value == THRESHOLD[3:0] && output_value == 2'b10);
  cover property (@(comb_ev) (THRESHOLD > 0 && THRESHOLD <= 16) && !$isunknown({input_value,output_value}) &&
                              input_value == (THRESHOLD-1)[3:0] && output_value == 2'b01);

  // coverage: transition across both thresholds
  cover property (@(comb_ev)
                  (THRESHOLD > 6) && !$isunknown({input_value,output_value}) && !$isunknown($past({input_value,output_value})) &&
                  $past(input_value) == 4'd5 && input_value == 4'd6 &&
                  $past(output_value) == 2'b00 && output_value == 2'b01);

  cover property (@(comb_ev)
                  (THRESHOLD > 0 && THRESHOLD <= 16) &&
                  !$isunknown({input_value,output_value}) && !$isunknown($past({input_value,output_value})) &&
                  $past(input_value) == (THRESHOLD-1)[3:0] && input_value == THRESHOLD[3:0] &&
                  $past(output_value) == 2'b01 && output_value == 2'b10);

endmodule

// Bind into DUT
bind threshold_module threshold_module_sva #(.THRESHOLD(THRESHOLD))
  threshold_module_sva_i (.input_value(input_value), .output_value(output_value));