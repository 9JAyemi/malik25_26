// SVA for vending_machine
// Binds into the DUT to check key behavior and provide concise coverage.

module vending_machine_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  data,
  input  logic        purchase,
  input  logic [3:0]  display,
  input  logic        item_dispensed,
  input  logic [1:0]  state,
  input  logic [3:0]  item_selected,
  input  logic [3:0]  item_price,
  input  logic [3:0]  item_dispensed_temp
);
  // Mirror DUT encodings/prices
  localparam logic [1:0] IDLE=2'b00, SELECTING=2'b01, DISPENSING=2'b10;
  localparam logic [3:0] ITEM_1_PRICE=4'd2, ITEM_2_PRICE=4'd3, ITEM_3_PRICE=4'd4;

  function automatic bit valid_sel (logic [3:0] d);
    return (d==4'b0001) || (d==4'b0010) || (d==4'b0100);
  endfunction

  function automatic logic [3:0] price_of (logic [3:0] d);
    case (d)
      4'b0001: return ITEM_1_PRICE;
      4'b0010: return ITEM_2_PRICE;
      4'b0100: return ITEM_3_PRICE;
      default: return 4'd0;
    endcase
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset effects (checked one cycle after reset assertion)
  assert property (reset |=> state==IDLE && item_selected==0 && item_price==0 && item_dispensed_temp==0 && !item_dispensed);

  // State encoding legal
  assert property (1 |-> (state inside {IDLE,SELECTING,DISPENSING}));

  // Display behavior per state (as implemented)
  assert property (state==IDLE       |-> display==4'b0001 && !item_dispensed);
  assert property (state==SELECTING  |-> display==item_price);
  assert property (state==DISPENSING |-> display==4'b0100 && item_dispensed);

  // item_dispensed only during DISPENSING and should be a 1-cycle pulse
  assert property (item_dispensed |-> state==DISPENSING);
  assert property (item_dispensed |=> !item_dispensed);

  // State transitions
  assert property (state==IDLE && purchase                                |=> state==SELECTING);
  assert property (state==IDLE && !purchase                               |=> state==IDLE);
  assert property (state==SELECTING && purchase && valid_sel(data)        |=> state==DISPENSING);
  assert property (state==SELECTING && !(purchase && valid_sel(data))     |=> state==SELECTING);
  assert property (state==DISPENSING                                      |=> state==IDLE);

  // Price decode updates 1 cycle after sample while in SELECTING
  assert property ($past(state)==SELECTING |-> item_price==price_of($past(data)));

  // Selected item captures data on valid purchase in SELECTING
  assert property (state==SELECTING && purchase && valid_sel(data) |=> item_selected==$past(data));

  // No dispense without previous cycle SELECTING+purchase
  assert property (state==DISPENSING |-> $past(state==SELECTING && purchase));

  // Known values (no X/Z) on key signals
  assert property (!$isunknown({state,display,item_dispensed,item_price,item_selected}));

  // Optional: temp register cleared after DISPENSING
  assert property ($past(state)==DISPENSING |-> item_dispensed_temp==0);

  // Coverage
  cover property (state==IDLE ##1 purchase ##1 state==SELECTING ##1
                  (purchase && valid_sel(data)) ##1 state==DISPENSING ##1
                  state==IDLE && !item_dispensed);

  cover property (state==SELECTING && data==4'b0001 ##1 purchase ##1 state==DISPENSING);
  cover property (state==SELECTING && data==4'b0010 ##1 purchase ##1 state==DISPENSING);
  cover property (state==SELECTING && data==4'b0100 ##1 purchase ##1 state==DISPENSING);

  cover property (state==SELECTING && !valid_sel(data) ##1 purchase ##1 state==SELECTING);
endmodule

// Bind into all instances of vending_machine
bind vending_machine vending_machine_sva sva (
  .clk(clk),
  .reset(reset),
  .data(data),
  .purchase(purchase),
  .display(display),
  .item_dispensed(item_dispensed),
  .state(state),
  .item_selected(item_selected),
  .item_price(item_price),
  .item_dispensed_temp(item_dispensed_temp)
);