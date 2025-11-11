// SVA for vending_machine
// Bind once to your DUT instance/type.
bind vending_machine vending_machine_sva i_vending_machine_sva(
  .clk(clk),
  .reset(reset),
  .coin(coin),
  .product(product),
  .dispense(dispense),
  .change(change),
  .ready(ready),
  .product_price(product_price),
  .coins_inserted(coins_inserted),
  .coins_returned(coins_returned),
  .dispense_product(dispense_product),
  .return_coins(return_coins),
  .ready_state(ready_state)
);

module vending_machine_sva(
  input  logic        clk,
  input  logic        reset,
  input  logic [1:0]  coin,
  input  logic [3:0]  product,
  input  logic        dispense,
  input  logic [1:0]  change,
  input  logic        ready,
  input  logic [3:0]  product_price,
  input  logic [7:0]  coins_inserted,
  input  logic [1:0]  coins_returned,
  input  logic        dispense_product,
  input  logic [1:0]  return_coins,
  input  logic        ready_state
);

  // Helpers
  function automatic int unsigned coin_val(logic [1:0] c);
    case (c)
      2'b00: coin_val = 1;
      2'b01: coin_val = 5;
      2'b10: coin_val = 10;
      default: coin_val = 25; // 2'b11
    endcase
  endfunction

  function automatic int unsigned price_val(logic [3:0] p);
    case (p)
      4'd5:  price_val = 5;
      4'd6:  price_val = 10;
      4'd7:  price_val = 15;
      4'd8:  price_val = 20;
      4'd9:  price_val = 25;
      4'd10: price_val = 30;
      4'd11: price_val = 35;
      4'd12: price_val = 40;
      4'd13: price_val = 45;
      4'd14: price_val = 50;
      4'd15: price_val = 55;
      default: price_val = 0;
    endcase
  endfunction

  // Shorthand for old-state vend decision (matches RTL semantics)
  let vend_cond = ($past(coins_inserted) >= $past(product_price)) && ($past(ready_state) == 1);
  let need_more = ($past(product_price) > $past(coins_inserted));

  // Reset behavior (asynchronous reset observed by next clk)
  property p_reset_vals;
    @(posedge clk) $rose(reset) |-> (coins_inserted==0 && coins_returned==0 && dispense_product==0 && return_coins==0 && ready_state==1);
  endproperty
  assert property(p_reset_vals);

  // Outputs mirror internal regs (combinational glue)
  assert property (@(posedge clk) (dispense==dispense_product) && (change==coins_returned) && (ready==ready_state));

  // Product-price decode: check intended mapping (this will flag width/coverage issues)
  assert property (@(posedge clk) product_price == price_val(product));

  // Coin accumulation vs vend reset
  // If not vending, next coins_inserted equals prior plus current coin value
  assert property (@(posedge clk) disable iff (reset)
                   !vend_cond |-> coins_inserted == $past(coins_inserted) + coin_val(coin));

  // If vending, coins_inserted is cleared
  assert property (@(posedge clk) disable iff (reset)
                   vend_cond |-> coins_inserted == 0);

  // Dispense/ready/change updates on vend
  assert property (@(posedge clk) disable iff (reset)
                   vend_cond |-> (dispense_product==1 && ready_state==0 &&
                                  coins_returned == ($past(coins_inserted) - $past(product_price))[1:0]));

  // Do not assert dispense without vend
  assert property (@(posedge clk) disable iff (reset)
                   $rose(dispense_product) |-> vend_cond);

  // Dispense sticks high until reset; ready stays low once cleared (per RTL)
  assert property (@(posedge clk) disable iff (reset) $past(dispense_product) |-> dispense_product);
  assert property (@(posedge clk) disable iff (reset) ($past(ready_state)==0) |-> (ready_state==0));

  // Return-coins path when not enough credit (internal side-effect)
  assert property (@(posedge clk) disable iff (reset) need_more |-> (return_coins == coin));

  // Sanity: no X on primary outputs
  assert property (@(posedge clk) !($isunknown({dispense,change,ready})) );

  // Change width safety (flags real design issue if overflow)
  assert property (@(posedge clk) disable iff (reset)
                   vend_cond |-> ($past(coins_inserted) - $past(product_price)) < 4)
    else $error("change width (2b) cannot represent due amount");

  // Coverage
  cover property (@(posedge clk) $rose(reset));
  cover property (@(posedge clk) coin==2'b00);
  cover property (@(posedge clk) coin==2'b01);
  cover property (@(posedge clk) coin==2'b10);
  cover property (@(posedge clk) coin==2'b11);
  cover property (@(posedge clk) product inside {[4'd5:4'd15]});
  cover property (@(posedge clk) vend_cond); // a vend occurs
  cover property (@(posedge clk) disable iff (reset)
                  vend_cond ##1 (dispense_product && !ready_state)); // vend effect seen
  cover property (@(posedge clk) need_more); // not enough credit path taken
  cover property (@(posedge clk) disable iff (reset)
                  vend_cond && (($past(coins_inserted)-$past(product_price))>=4)); // provoke change overflow

endmodule