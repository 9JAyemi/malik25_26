// SVA checker for vending_machine
module vm_sva #(parameter logic [1:0] PRICE = 2'b10,
                parameter logic [7:0] COIN_TABLE = 8'b0001_1011)
(
  input logic        clk,
  input logic        reset,
  input logic [1:0]  coin,
  input logic [1:0]  dispense,
  input logic        dispenser1,
  input logic        dispenser2,
  input logic        dispenser3,
  input logic        dispenser4,
  input logic [1:0]  change,
  input logic [1:0]  amount_inserted
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  function automatic logic inc_bit(input logic [1:0] c);
    inc_bit = COIN_TABLE[c]; // 1-bit, as coded in DUT
  endfunction

  let vend_can   = $past(!reset) && ($past(amount_inserted) >= PRICE);
  let refund_can = $past(!reset) && ($past(amount_inserted) > 0) && ($past(amount_inserted) < PRICE);

  // Basic sanity
  assert property (!$isunknown({coin,dispense}));
  assert property ($onehot0({dispenser1,dispenser2,dispenser3,dispenser4}));

  // Reset clears all observable state
  assert property (@(posedge clk) reset |-> (amount_inserted==2'b0 && change==2'b0 &&
                                             {dispenser4,dispenser3,dispenser2,dispenser1}==4'b0));

  // Amount update semantics (matches DUT as written)
  assert property (vend_can   |-> amount_inserted==2'b0);
  assert property (refund_can |-> amount_inserted==2'b0);
  assert property ($past(!reset) && !vend_can && !refund_can |->
                   amount_inserted == ($past(amount_inserted) + inc_bit($past(coin))));

  // Change update semantics
  assert property (vend_can   |-> change == ($past(amount_inserted) - PRICE));
  assert property (refund_can |-> change == $past(amount_inserted));
  assert property ($past(!reset) && !vend_can && !refund_can |-> change == $past(change));

  // Dispense behavior mapping (selected dispenser goes high on vend)
  assert property (vend_can && $past(dispense)==2'b00 |-> dispenser1);
  assert property (vend_can && $past(dispense)==2'b01 |-> dispenser2);
  assert property (vend_can && $past(dispense)==2'b10 |-> dispenser3);
  assert property (vend_can && $past(dispense)==2'b11 |-> dispenser4);

  // No new dispenser assertion without a vend decision
  assert property ($past(!reset) && !vend_can |->
                   !($rose(dispenser1) || $rose(dispenser2) || $rose(dispenser3) || $rose(dispenser4)));

  // Any dispenser rise must be due to vend and correct selector
  assert property ($rose(dispenser1) |-> vend_can && $past(dispense)==2'b00);
  assert property ($rose(dispenser2) |-> vend_can && $past(dispense)==2'b01);
  assert property ($rose(dispenser3) |-> vend_can && $past(dispense)==2'b10);
  assert property ($rose(dispenser4) |-> vend_can && $past(dispense)==2'b11);

  // change only updates on reset/refund/vend
  assert property ($changed(change) |-> reset || vend_can || refund_can);

  // Coverage
  cover property (vend_can && $past(dispense)==2'b00);
  cover property (vend_can && $past(dispense)==2'b01);
  cover property (vend_can && $past(dispense)==2'b10);
  cover property (vend_can && $past(dispense)==2'b11);
  cover property (refund_can);
  cover property ($past(!reset) && !vend_can && !refund_can && inc_bit($past(coin)));

  cover property (@(posedge clk) reset); // reset seen

endmodule

// Bind into DUT
bind vending_machine vm_sva #(.PRICE(product_price), .COIN_TABLE(coin_value))
  u_vm_sva (.*,.amount_inserted(amount_inserted));