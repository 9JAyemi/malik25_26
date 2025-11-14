// Drop this SVA block inside vending_machine_controller (or bind it) – concise, high-signal-coverage

// ---------- SVA: vending_machine_controller ----------
generate
  if (1) begin : sva

    default clocking @(posedge clk); endclocking

    // Reset behavior (sync reset sets known values same cycle)
    assert property (rst |-> state==IDLE
                              && total_money==0
                              && !dispense_X && !dispense_Y && !dispense_Z
                              && button_A_enable && button_B_enable && button_C_enable);

    // State encoding is always valid
    assert property (disable iff (rst) (state==IDLE || state==DISPENSING || state==COIN_INSERTED));

    // Only zero or one dispense output may be asserted
    assert property (disable iff (rst) $onehot0({dispense_X,dispense_Y,dispense_Z}));

    // Dispense may be 1 only while in DISPENSING
    assert property (disable iff (rst) (dispense_X || dispense_Y || dispense_Z) |-> state==DISPENSING);

    // Enables reflect inventory availability
    assert property (disable iff (rst) button_A_enable == (inventory[0]>0));
    assert property (disable iff (rst) button_B_enable == (inventory[1]>0));
    assert property (disable iff (rst) button_C_enable == (inventory[2]>0));

    // Helper: no purchase condition true (priority-aware for IDLE path)
    sequence no_buy_idle;
      !(button_A && (inventory[0]>0)) &&
      !((!button_A || !(inventory[0]>0)) && button_B && (inventory[1]>0)) &&
      !((!button_A || !(inventory[0]>0)) && (!button_B || !(inventory[1]>0)) && button_C && (inventory[2]>0));
    endsequence

    // IDLE purchases (priority A>B>C), with money/inventory updates
    assert property (disable iff (rst)
      (state==IDLE && button_A && (inventory[0]>0)) |=> state==DISPENSING && dispense_X && !dispense_Y && !dispense_Z
                                                  && total_money==$past(total_money)+PRICE
                                                  && inventory[0]==$past(inventory[0])-1);

    assert property (disable iff (rst)
      (state==IDLE && !(button_A && (inventory[0]>0)) && button_B && (inventory[1]>0)) |=> state==DISPENSING && dispense_Y && !dispense_X && !dispense_Z
                                                                                      && total_money==$past(total_money)+PRICE
                                                                                      && inventory[1]==$past(inventory[1])-1);

    assert property (disable iff (rst)
      (state==IDLE && !(button_A && (inventory[0]>0)) && !(button_B && (inventory[1]>0)) && button_C && (inventory[2]>0)) |=> state==DISPENSING && dispense_Z && !dispense_X && !dispense_Y
                                                                                                                          && total_money==$past(total_money)+PRICE
                                                                                                                          && inventory[2]==$past(inventory[2])-1);

    // IDLE coin insertion (only when no buy chosen)
    assert property (disable iff (rst)
      (state==IDLE && coin && no_buy_idle) |=> state==COIN_INSERTED
                                          && !dispense_X && !dispense_Y && !dispense_Z
                                          && total_money==$past(total_money)+100);

    // DISPENSING exit only when all buttons released; clear dispense on exit
    assert property (disable iff (rst)
      (state==DISPENSING && !button_A && !button_B && !button_C) |=> state==IDLE && !dispense_X && !dispense_Y && !dispense_Z);

    // DISPENSING hold: keep outputs/money/inventory stable while any button is pressed
    assert property (disable iff (rst)
      (state==DISPENSING && (button_A || button_B || button_C)) |=> state==DISPENSING
                                                               && $stable({dispense_X,dispense_Y,dispense_Z,inventory,total_money}));

    // COIN_INSERTED purchases (same priority A>B>C), with money/inventory updates
    assert property (disable iff (rst)
      (state==COIN_INSERTED && button_A && (inventory[0]>0)) |=> state==DISPENSING && dispense_X && !dispense_Y && !dispense_Z
                                                          && total_money==$past(total_money)+PRICE
                                                          && inventory[0]==$past(inventory[0])-1);

    assert property (disable iff (rst)
      (state==COIN_INSERTED && !(button_A && (inventory[0]>0)) && button_B && (inventory[1]>0)) |=> state==DISPENSING && dispense_Y && !dispense_X && !dispense_Z
                                                                                              && total_money==$past(total_money)+PRICE
                                                                                              && inventory[1]==$past(inventory[1])-1);

    assert property (disable iff (rst)
      (state==COIN_INSERTED && !(button_A && (inventory[0]>0)) && !(button_B && (inventory[1]>0)) && button_C && (inventory[2]>0)) |=> state==DISPENSING && dispense_Z && !dispense_X && !dispense_Y
                                                                                                                              && total_money==$past(total_money)+PRICE
                                                                                                                              && inventory[2]==$past(inventory[2])-1);

    // COIN_INSERTED -> IDLE only when coin removed and no purchase condition taken
    assert property (disable iff (rst)
      (state==COIN_INSERTED && !coin
         && !(button_A && (inventory[0]>0))
         && !( !(button_A && (inventory[0]>0)) && button_B && (inventory[1]>0))
         && !( !(button_A && (inventory[0]>0)) && !(button_B && (inventory[1]>0)) && button_C && (inventory[2]>0))
      ) |=> state==IDLE && $stable({inventory,total_money,dispense_X,dispense_Y,dispense_Z}));

    // Safety: cannot enter DISPENSING unless a valid purchase was requested
    assert property (disable iff (rst)
      $rose(state==DISPENSING) |-> (
          ( $past(state)==IDLE || $past(state)==COIN_INSERTED )
          &&
          (
            ($past(button_A) && $past(inventory[0]>0) && dispense_X && !dispense_Y && !dispense_Z)
         || (!($past(button_A) && $past(inventory[0]>0)) && $past(button_B) && $past(inventory[1]>0) && dispense_Y && !dispense_X && !dispense_Z)
         || (!($past(button_A) && $past(inventory[0]>0)) && !($past(button_B) && $past(inventory[1]>0)) && $past(button_C) && $past(inventory[2]>0) && dispense_Z && !dispense_X && !dispense_Y)
          )
      )
    );

    // --------- Coverage (concise, high-value) ---------
    cover property (disable iff (rst) (state==IDLE && coin && no_buy_idle) ##1 (state==COIN_INSERTED));
    cover property (disable iff (rst) (state==IDLE && button_A && (inventory[0]>0)) ##1 (state==DISPENSING && dispense_X));
    cover property (disable iff (rst) (state==IDLE && !(button_A && (inventory[0]>0)) && button_B && (inventory[1]>0)) ##1 (state==DISPENSING && dispense_Y));
    cover property (disable iff (rst) (state==IDLE && !(button_A && (inventory[0]>0)) && !(button_B && (inventory[1]>0)) && button_C && (inventory[2]>0)) ##1 (state==DISPENSING && dispense_Z));
    cover property (disable iff (rst) (state==IDLE && button_A && button_B && button_C && (inventory[0]>0)) ##1 dispense_X); // priority A over B/C
    cover property (disable iff (rst) (state==IDLE && !(inventory[0]>0) && button_B && (inventory[1]>0)) ##1 dispense_Y);     // fallback to B if A out
    cover property (disable iff (rst) (state==IDLE && coin && no_buy_idle) ##1 (state==COIN_INSERTED && !coin) ##1 (state==IDLE)); // coin insert then remove no buy

  end
endgenerate
// ---------- end SVA ----------