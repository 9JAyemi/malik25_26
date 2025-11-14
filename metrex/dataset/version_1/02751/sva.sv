// SVA for data_deal
bind data_deal data_deal_sva();

module data_deal_sva;

  // Access DUT scope directly (bind-local names)
  // clk, rst_n, data_in[6:0], data_in_sign, data_valid,
  // data_out[6:0], data_out_sign, data_ok,
  // data_reg[6:0], data_in_sign_reg

  default clocking cb @(posedge clk); endclocking

  // Track when $past() is valid
  bit past_v;
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) past_v <= 1'b0;
    else        past_v <= 1'b1;
  end

  // Reset value checks (async reset held low)
  assert property (@(posedge clk) !rst_n |-> (data_reg==7'h0 && data_ok==1'b0 &&
                                              data_in_sign_reg==1'b0 && data_out==7'h0 &&
                                              data_out_sign==1'b0));

  // No X on key regs/outs when out of reset
  assert property (past_v |-> !$isunknown({data_out, data_out_sign, data_ok,
                                           data_reg, data_in_sign_reg}));

  // Exact next-state functional equivalence (single-cycle)
  assert property (past_v |-> data_in_sign_reg == $past(data_in_sign));

  assert property (past_v |-> data_reg ==
                   ($past(data_in_sign) ? $past(data_reg)+7'd1 : $past(data_reg)));

  assert property (past_v |-> data_ok ==
                   ($past(data_in_sign_reg) ? &($past(data_reg) ~^ $past(data_in))
                                            : $past(data_ok)));

  assert property (past_v |-> data_out_sign ==
                   (~$past(data_out_sign) & $past(data_valid)));

  assert property (past_v |-> data_out ==
                   ($past(~data_out_sign & data_valid) ? $past(data_out)+7'd1
                                                        : $past(data_out)));

  // Change-implies-enable (no unintended updates)
  assert property (past_v && (data_reg != $past(data_reg)) |-> $past(data_in_sign));
  assert property (past_v && (data_ok  != $past(data_ok))  |-> $past(data_in_sign_reg));
  assert property (past_v && (data_out != $past(data_out)) |-> $past(~data_out_sign & data_valid));
  assert property (past_v && data_out_sign                |-> $past(~data_out_sign & data_valid));
  assert property (past_v && data_out_sign |=> !data_out_sign); // one-cycle pulse

  // Concise coverage
  cover property (past_v && data_in_sign ##1 (data_reg == $past(data_reg)+7'd1)); // data_reg increments
  cover property (past_v && $past(data_in_sign_reg) &&
                  (&($past(data_reg) ~^ $past(data_in))) && data_ok);              // data_ok==1 event
  cover property (past_v && $past(~data_out_sign & data_valid) &&
                  (data_out == $past(data_out)+7'd1));                            // data_out increments
  cover property (past_v && data_valid[*3]);                                      // exercise pulse train

endmodule