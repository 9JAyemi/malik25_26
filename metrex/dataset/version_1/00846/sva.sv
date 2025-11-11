// Drop this SVA block inside the vending_machine module (or bind it) for concise, high-value checking.
// synthesis translate_off
// pragma translate_off

default clocking cb @(posedge clk); endclocking
default disable iff (!reset)

function automatic [7:0] price_of_button (input logic [1:0] b);
  case (b)
    2'b01: price_of_button = PRICE_1;
    2'b10: price_of_button = PRICE_2;
    2'b11: price_of_button = PRICE_3;
    2'b00: price_of_button = PRICE_4;
    default: price_of_button = '0;
  endcase
endfunction

function automatic [7:0] val_of_coin (input logic [1:0] c);
  case (c)
    2'b01: val_of_coin = 8'd5;
    2'b10: val_of_coin = 8'd10;
    2'b11: val_of_coin = 8'd25;
    2'b00: val_of_coin = 8'd50;
    default: val_of_coin = '0;
  endcase
endfunction

// Reset and state sanity
assert property ( !reset |-> state==IDLE && price==0 && money==0 && change==0 &&
                  coin_value==0 && disp_price==0 && disp_money==0 && disp_change==0 );
assert property ( state inside {IDLE, DISP_PRICE, INSERT_COIN, DISP_CHANGE} );

// Allowed transitions only
assert property ( state==IDLE       |=> state inside {IDLE, DISP_PRICE} );
assert property ( state==DISP_PRICE |=> state inside {DISP_PRICE, INSERT_COIN} );
assert property ( state==INSERT_COIN|=> state inside {DISP_PRICE, DISP_CHANGE} );
assert property ( state==DISP_CHANGE|=> state inside {IDLE, INSERT_COIN} );

// IDLE behavior
assert property ( state==IDLE && button==2'b00 |=> state==IDLE );
assert property ( state==IDLE && button!=2'b00 |=> state==DISP_PRICE &&
                  price == price_of_button($past(button)) );
assert property ( state==DISP_PRICE && $past(state)==IDLE |-> $past(button)!=2'b00 );

// Display mirrors internal regs
assert property ( disp_money == money );
assert property ( disp_change == change );
assert property ( state != IDLE |-> disp_price == price );
assert property ( state==IDLE && button==2'b00 |-> disp_price==0 );

// Price immutability while active (until IDLE clear)
assert property ( state!=IDLE |-> $stable(price) );

// Coin handling in DISP_PRICE (this will catch coin_value/MONEY NBA bug)
assert property ( state==DISP_PRICE && coin!=2'b00 |=> state==INSERT_COIN &&
                  money == $past(money) + val_of_coin($past(coin)) &&
                  coin_value == val_of_coin($past(coin)) );
// No coin => no money change
assert property ( state==DISP_PRICE && coin==2'b00 |-> $stable(money) );

// INSERT_COIN settle
assert property ( state==INSERT_COIN && money >= price |=> state==DISP_CHANGE &&
                  money == $past(money) - $past(price) &&
                  change == $past(money) - $past(price) );
assert property ( state==INSERT_COIN && money <  price |=> state==DISP_PRICE &&
                  coin_value == 0 );

// DISP_CHANGE behavior (this will catch coin_value/CHANGE NBA bug)
assert property ( state==DISP_CHANGE && coin!=2'b00 |=> state==INSERT_COIN &&
                  change == $past(change) + val_of_coin($past(coin)) &&
                  coin_value == val_of_coin($past(coin)) );
assert property ( state==DISP_CHANGE && coin==2'b00 |=> state==IDLE &&
                  price==0 && money==0 && change==0 && coin_value==0 &&
                  disp_price==0 && disp_money==0 && disp_change==0 );

// Simple functional covers
cover property ( state==IDLE && button==2'b01 |=> state==DISP_PRICE );
cover property ( state==IDLE && button==2'b10 |=> state==DISP_PRICE );
cover property ( state==IDLE && button==2'b11 |=> state==DISP_PRICE );
cover property ( state==IDLE && button==2'b00 |=> state==IDLE );

cover property ( state==DISP_PRICE && coin==2'b01 |=> state==INSERT_COIN );
cover property ( state==DISP_PRICE && coin==2'b10 |=> state==INSERT_COIN );
cover property ( state==DISP_PRICE && coin==2'b11 |=> state==INSERT_COIN );

cover property ( state==INSERT_COIN && money >= price |=> state==DISP_CHANGE );
cover property ( state==INSERT_COIN && money <  price |=> state==DISP_PRICE );

cover property ( state==DISP_CHANGE && coin==2'b00 |=> state==IDLE );

// pragma translate_on
// synthesis translate_on