// SVA checker for vending_machine
module vm_sva (
  input logic        clk,
  input logic        reset,
  input logic [2:0]  coin,
  input logic [1:0]  product,
  input logic        dispense,
  input logic [2:0]  change,
  input logic [3:0]  display,
  // bind to DUT internals
  input logic [2:0]  amount_inserted,
  input logic [2:0]  product_cost,
  input logic [2:0]  excess_change
);

  default clocking cb @(posedge clk); endclocking

  // Map coin to 3-bit increment actually implemented by this RTL (mod 3 bits)
  function automatic logic [2:0] inc3 (input logic [2:0] c);
    case (c)
      3'd1: inc3 = 3'd5; // +5
      3'd2: inc3 = 3'd2; // +10 -> 2 mod 8
      3'd3: inc3 = 3'd1; // +25 -> 1 mod 8
      3'd4: inc3 = 3'd2; // +50 -> 2 mod 8
      3'd5: inc3 = 3'd4; // +100 -> 4 mod 8
      default: inc3 = 3'd0;
    endcase
  endfunction

  // Reset clears all state/outputs at the following cycle
  assert property (@(posedge clk)
    reset |=> amount_inserted==3'd0 && product_cost==3'd0 &&
             excess_change==3'd0 && dispense==1'b0 &&
             change==3'd0 && display==4'd0
  );

  // No X/Z on primary outputs after reset deasserted
  assert property (@(posedge clk) disable iff (reset)
    !$isunknown({dispense, change, display})
  );

  // Product cost decode (uses prior-cycle product due to nonblocking semantics)
  assert property (@(posedge clk) disable iff (reset)
    product_cost == ( $past(product)==2'd1 ? 3'd2 :
                      $past(product)==2'd2 ? 3'd3 :
                      $past(product)==2'd3 ? 3'd4 :
                                              $past(product_cost) )
  );

  // Dispense decision is based on prior-cycle amount and cost
  assert property (@(posedge clk) disable iff (reset)
    dispense == ($past(amount_inserted) >= $past(product_cost))
  );

  // Amount update: either subtract cost on dispense, else add coin increment (mod 3 bits)
  assert property (@(posedge clk) disable iff (reset)
    amount_inserted ==
      ( ($past(amount_inserted) >= $past(product_cost)) ?
          ($past(amount_inserted) - $past(product_cost)) :
          ($past(amount_inserted) + inc3($past(coin))) )
  );

  // Excess change computes prior-cycle amount - cost (mod 3 bits)
  assert property (@(posedge clk) disable iff (reset)
    excess_change == ($past(amount_inserted) - $past(product_cost))
  );

  // change is a 1-cycle pipeline of excess_change
  assert property (@(posedge clk) disable iff (reset)
    change == $past(excess_change)
  );

  // Display is the truncated concat of prior-cycle {amount_inserted, product_cost}
  // 4 LSBs: {amount_inserted[0], product_cost[2:0]}
  assert property (@(posedge clk) disable iff (reset)
    display == { $past(amount_inserted[0]), $past(product_cost) }
  );

  // -------------------
  // Functional coverage
  // -------------------

  // Cover each coin code observed
  cover property (@(posedge clk) disable iff (reset) coin==3'd1);
  cover property (@(posedge clk) disable iff (reset) coin==3'd2);
  cover property (@(posedge clk) disable iff (reset) coin==3'd3);
  cover property (@(posedge clk) disable iff (reset) coin==3'd4);
  cover property (@(posedge clk) disable iff (reset) coin==3'd5);

  // Cover each product selection observed
  cover property (@(posedge clk) disable iff (reset) product==2'd1);
  cover property (@(posedge clk) disable iff (reset) product==2'd2);
  cover property (@(posedge clk) disable iff (reset) product==2'd3);

  // Cover a dispense event
  cover property (@(posedge clk) disable iff (reset) $past(amount_inserted) >= $past(product_cost) ##1 dispense);

  // Cover an addition wrap-around (no dispense, addition causes modulo-8 wrap)
  cover property (@(posedge clk) disable iff (reset)
    ($past(amount_inserted) < $past(product_cost)) == 1'b0 && // no dispense next
    (amount_inserted < $past(amount_inserted))
  );

  // Cover underpay (no dispense) with nonzero "negative" change modulo 3 bits
  cover property (@(posedge clk) disable iff (reset)
    $past(amount_inserted) < $past(product_cost) ##1 change != 3'd0
  );

endmodule

// Bind into the DUT (connects to internals by name)
bind vending_machine vm_sva vm_sva_i (.*);