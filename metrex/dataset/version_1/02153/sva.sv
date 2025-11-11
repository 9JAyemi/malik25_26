// SVA for compute_tm_count
module compute_tm_count_sva (
  input  logic       clk,
  input  logic       atm_valid,
  input  logic       dtm_valid,
  input  logic       itm_valid,
  input  logic [1:0] compute_tm_count
);

  default clocking @(posedge clk); endclocking

  function automatic bit inputs_known();
    return !$isunknown({itm_valid, atm_valid, dtm_valid});
  endfunction

  // Output known when inputs known
  assert property (inputs_known() |-> !$isunknown(compute_tm_count))
    else $error("compute_tm_count X/Z with known inputs");

  // Functional correctness = population count of valids
  assert property (inputs_known() |-> compute_tm_count == $countones({itm_valid,atm_valid,dtm_valid})[1:0])
    else $error("compute_tm_count mismatch");

  // No unintended state: if inputs stable across a cycle, output stable
  assert property ($stable({itm_valid,atm_valid,dtm_valid}) |=> $stable(compute_tm_count))
    else $error("compute_tm_count changed without input change");

  // Range (explicit)
  assert property (!$isunknown(compute_tm_count) |-> (compute_tm_count inside {2'd0,2'd1,2'd2,2'd3}));

  // Functional coverage: all input combinations with matching output
  cover property (inputs_known() && {itm_valid,atm_valid,dtm_valid}==3'b000 && compute_tm_count==2'd0);
  cover property (inputs_known() && {itm_valid,atm_valid,dtm_valid}==3'b001 && compute_tm_count==2'd1);
  cover property (inputs_known() && {itm_valid,atm_valid,dtm_valid}==3'b010 && compute_tm_count==2'd1);
  cover property (inputs_known() && {itm_valid,atm_valid,dtm_valid}==3'b011 && compute_tm_count==2'd2);
  cover property (inputs_known() && {itm_valid,atm_valid,dtm_valid}==3'b100 && compute_tm_count==2'd1);
  cover property (inputs_known() && {itm_valid,atm_valid,dtm_valid}==3'b101 && compute_tm_count==2'd2);
  cover property (inputs_known() && {itm_valid,atm_valid,dtm_valid}==3'b110 && compute_tm_count==2'd2);
  cover property (inputs_known() && {itm_valid,atm_valid,dtm_valid}==3'b111 && compute_tm_count==2'd3);

endmodule

// Example bind (clk must be available in the instance scope)
bind compute_tm_count compute_tm_count_sva u_compute_tm_count_sva (
  .clk(clk),
  .atm_valid(atm_valid),
  .dtm_valid(dtm_valid),
  .itm_valid(itm_valid),
  .compute_tm_count(compute_tm_count)
);