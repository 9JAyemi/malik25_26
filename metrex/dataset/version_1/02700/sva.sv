// SVA checker for vending_machine
module vending_machine_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        nickel,
  input  logic        dime,
  input  logic        quarter,
  input  logic        select_A,
  input  logic        select_B,
  input  logic        select_C,
  input  logic        dispense,
  input  logic        change_10,
  input  logic        change_25,
  input  logic        product_A,
  input  logic        product_B,
  input  logic        product_C,
  input  logic [7:0]  total_amount,
  input  logic [1:0]  product_selected,
  input  logic [1:0]  change_returned,
  input  logic [7:0]  cost
);

  // Constant check
  assert property (@(posedge clk) cost == 8'd50);

  // Reset effects (next-cycle to avoid sampling order issues)
  assert property (@(posedge clk) rst |=> (total_amount==0 && product_selected==0 && change_returned==0));
  assert property (@(posedge clk) rst |-> (!dispense && !product_A && !product_B && !product_C && !change_10 && !change_25));

  // No X after reset deasserted
  assert property (@(posedge clk) disable iff (rst)
                   !$isunknown({total_amount,product_selected,change_returned,
                                dispense,product_A,product_B,product_C,change_10,change_25}));

  // Output mappings
  assert property (@(posedge clk) dispense == ((total_amount >= cost) && (select_A || select_B || select_C)));
  assert property (@(posedge clk) product_A == (product_selected == 2'b01));
  assert property (@(posedge clk) product_B == (product_selected == 2'b10));
  assert property (@(posedge clk) product_C == (product_selected == 2'b11));
  assert property (@(posedge clk) change_10  == (change_returned == 2'b10));
  assert property (@(posedge clk) change_25  == (change_returned == 2'b01));
  assert property (@(posedge clk) $onehot0({product_C,product_B,product_A}));
  assert property (@(posedge clk) !(change_10 && change_25));

  // Coin accumulation when no select
  property p_coin_accum_no_select;
    @(posedge clk) disable iff (rst)
      !($past(select_A)||$past(select_B)||$past(select_C)) &&
      ($past(nickel)||$past(dime)||$past(quarter))
      |-> total_amount == $past(total_amount)
                         + ($past(nickel)  ? 8'd5  : 8'd0)
                         + ($past(dime)    ? 8'd10 : 8'd0)
                         + ($past(quarter) ? 8'd25 : 8'd0);
  endproperty
  assert property (p_coin_accum_no_select);

  // change_returned behavior on coins (no select)
  assert property (@(posedge clk) disable iff (rst)
                   !($past(select_A)||$past(select_B)||$past(select_C)) &&
                   ($past(nickel)||$past(dime)||$past(quarter))
                   |-> change_returned == 2'b00);

  // Idle hold (no coins, no selects)
  assert property (@(posedge clk) disable iff (rst)
                   !($past(nickel)||$past(dime)||$past(quarter)||
                     $past(select_A)||$past(select_B)||$past(select_C))
                   |-> (total_amount==$past(total_amount) &&
                        product_selected==$past(product_selected) &&
                        change_returned==$past(change_returned)));

  // Product selection has priority C > B > A
  // Sufficient funds: subtract cost, return truncated previous total_amount, set selected product
  assert property (@(posedge clk) disable iff (rst)
                   ($past(select_A)||$past(select_B)||$past(select_C)) && ($past(total_amount) >= $past(cost))
                   |-> (total_amount      == $past(total_amount) - $past(cost)) &&
                       (change_returned   == $past(total_amount[1:0])) &&
                       (product_selected  == ($past(select_C) ? 2'b11 :
                                              $past(select_B) ? 2'b10 :
                                                                2'b01)));

  // Insufficient funds: clear everything
  assert property (@(posedge clk) disable iff (rst)
                   ($past(select_A)||$past(select_B)||$past(select_C)) && ($past(total_amount) < $past(cost))
                   |-> (total_amount==0 && change_returned==0 && product_selected==0));

  // product_selected only changes on select
  assert property (@(posedge clk) disable iff (rst)
                   !($past(select_A)||$past(select_B)||$past(select_C))
                   |-> product_selected == $past(product_selected));

  // ----------------
  // Useful covers
  // ----------------
  // Vend each product
  cover property (@(posedge clk) (total_amount >= cost) && select_A && dispense);
  cover property (@(posedge clk) (total_amount >= cost) && select_B && dispense);
  cover property (@(posedge clk) (total_amount >= cost) && select_C && dispense);

  // Insufficient funds selection path
  cover property (@(posedge clk) (total_amount < cost) && select_B);

  // Multiple coins in one cycle without select
  cover property (@(posedge clk) (nickel && dime && quarter) && !(select_A||select_B||select_C));

  // Selects with priority (A and B, no C)
  cover property (@(posedge clk) disable iff (rst)
                  $past(total_amount) >= $past(cost) &&
                  $past(select_A) && $past(select_B) && !$past(select_C)
                  |-> product_B && !product_A && !product_C);

  // Coins and select same cycle (coins ignored on vend)
  cover property (@(posedge clk) disable iff (rst)
                  ($past(nickel)||$past(dime)||$past(quarter)) &&
                  ($past(select_A)||$past(select_B)||$past(select_C)) &&
                  ($past(total_amount) >= $past(cost))
                  |-> total_amount == $past(total_amount) - $past(cost));

endmodule

// Bind into DUT
bind vending_machine vending_machine_sva vm_sva_i (
  .clk(clk),
  .rst(rst),
  .nickel(nickel),
  .dime(dime),
  .quarter(quarter),
  .select_A(select_A),
  .select_B(select_B),
  .select_C(select_C),
  .dispense(dispense),
  .change_10(change_10),
  .change_25(change_25),
  .product_A(product_A),
  .product_B(product_B),
  .product_C(product_C),
  .total_amount(total_amount),
  .product_selected(product_selected),
  .change_returned(change_returned),
  .cost(cost)
);