// SVA for parity_check
// Bind inside the DUT to see internals without modifying RTL
bind parity_check parity_check_sva();

module parity_check_sva;
  default clocking cb @(posedge clk); endclocking

  // avoid first-cycle $past hazards and X-gating
  bit past_v; always @(cb) past_v <= 1'b1;

  // Implementation-semantic checks (given nonblocking semantics and widths)
  // shift_reg gets truncated concatenation -> equals data_in
  assert property (past_v && !$isunknown($past(data_in)))
    shift_reg == $past(data_in);

  // shifted_data uses previous shift_reg
  assert property (past_v && !$isunknown($past(shift_reg)))
    shifted_data == { $past(shift_reg[5:0]), 2'b00 };

  // sum uses previous shifted_data and previous shift_reg
  assert property (past_v && !$isunknown($past({shifted_data,shift_reg})))
    sum == $past(shifted_data) + $past(shift_reg);

  // Parity behavior as coded:
  // - If sum was zero, parity is forced to 1
  assert property (past_v && !$isunknown($past(sum)) && ($past(sum)==8'h00))
    parity == 1'b1;

  // - If any sum bit was 1, parity toggles from previous parity
  assert property (past_v && !$isunknown($past({sum,parity})) && ($past(sum)!=8'h00))
    parity == ~$past(parity);

  // Sanity: no X on architectural state after first valid cycle of its driver
  assert property (past_v) !$isunknown({parity, sum, shift_reg, shifted_data});

  // Lightweight coverage
  cover property (past_v && ($past(sum)==8'h00) && (parity==1'b1));          // zero case
  cover property (past_v && ($past(sum)!=8'h00) && (parity==~$past(parity))); // toggle case
  cover property (past_v && $countones($past(sum))==1);                       // single 1
  cover property (past_v && $countones($past(sum))>=2);                       // multiple 1s
  cover property (past_v && $changed(shift_reg));                             // data capture activity
endmodule