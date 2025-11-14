// SVA for register_addition
module register_addition_sva;
  // Bound into DUT scope; can directly see reg_bank, CLK, AR, Q_reg_0, Q_reg_30, Q
  default clocking cb @(posedge CLK); endclocking
  default disable iff (AR);

  // Basic sanity: no X on key controls during operation
  assert property (!$isunknown(Q_reg_0));
  assert property (!$isunknown(Q_reg_30));

  // Read-before-write behavior on Q (Q shows prior value of selected bank)
  assert property (1 |=> Q == $past(reg_bank[$past(Q_reg_0)]));

  // Selected bank updates = old + Q_reg_30 (mod 256); non-selected banks hold
  generate
    genvar k;
    for (k=0; k<4; k++) begin : G_BANK_0_3
      assert property ((Q_reg_0==k) |=> reg_bank[k] == ($past(reg_bank[k]) + $past(Q_reg_30))[7:0]);
      assert property ((Q_reg_0!=k) |=> reg_bank[k] == $past(reg_bank[k]));
      // Coverage: each select hit
      cover property (Q_reg_0==k);
      // Coverage: wrap-around on update
      cover property ((Q_reg_0==k) |=> reg_bank[k] < $past(reg_bank[k]));
    end
    for (k=4; k<8; k++) begin : G_BANK_4_7
      // Banks 4..7 are never written when not in reset
      assert property (1 |=> reg_bank[k] == $past(reg_bank[k]));
    end
  endgenerate

  // Reset effects (checked on clock, not disabled)
  assert property (@(posedge CLK) AR |-> (reg_bank[0]==0 && reg_bank[1]==0 && reg_bank[2]==0 && reg_bank[3]==0 &&
                                          reg_bank[4]==0 && reg_bank[5]==0 && reg_bank[6]==0 && reg_bank[7]==0 &&
                                          $stable(Q)));
  assert property (@(posedge CLK) $rose(AR) |=> (reg_bank[0]==0 && reg_bank[1]==0 && reg_bank[2]==0 && reg_bank[3]==0 &&
                                                 reg_bank[4]==0 && reg_bank[5]==0 && reg_bank[6]==0 && reg_bank[7]==0));
  // Reset coverage
  cover property (@(posedge CLK) $rose(AR));
  cover property (@(posedge CLK) AR [*1:$] ##1 !AR);
endmodule

bind register_addition register_addition_sva sva_i();