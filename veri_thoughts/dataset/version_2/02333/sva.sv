module top_module_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic [3:0] binary,
    input logic [3:0] BCD_HIGH,
    input logic [3:0] BCD_LOW
);
    // BCD_LOW is always 0..9.
    check_bcd_low_range: assert property (
        @(posedge clk) (BCD_LOW <= 4'd9)
    );

    // BCD_HIGH is always 0 or 1.
    check_bcd_high_range: assert property (
        @(posedge clk) (BCD_HIGH <= 4'd1)
    );

    // If BCD_HIGH is 1, BCD_LOW must be 0..5 (since value <= 15).
    check_bcd_high1_low_max5: assert property (
        @(posedge clk) (BCD_HIGH == 4'd1) |-> (BCD_LOW <= 4'd5)
    );

    // On load, next cycle BCD outputs equal binary's BCD.
    check_load_sets_bcd_next: assert property (
        @(posedge clk) load |=> ( (BCD_HIGH == ($past(binary) / 10)) && (BCD_LOW == ($past(binary) % 10)) )
    );

    // When counting up (no load), next BCD equals (previous value + 1) mod 16.
    check_increment_updates_bcd_next: assert property (
        @(posedge clk) (!load && up_down) |=> (
            (BCD_HIGH == ((($past(BCD_HIGH)*10 + $past(BCD_LOW) + 1) % 16) / 10)) &&
            (BCD_LOW  == ((($past(BCD_HIGH)*10 + $past(BCD_LOW) + 1) % 16) % 10))
        )
    );

    // When counting down (no load), next BCD equals (previous value - 1) mod 16.
    check_decrement_updates_bcd_next: assert property (
        @(posedge clk) (!load && !up_down) |=> (
            (BCD_HIGH == (((($past(BCD_HIGH)*10 + $past(BCD_LOW) + 15) % 16) / 10))) &&
            (BCD_LOW  == (((($past(BCD_HIGH)*10 + $past(BCD_LOW) + 15) % 16) % 10)))
        )
    );

    // Increment wrap-around: from 15 -> 0 when counting up (no load).
    check_inc_wrap_15_to_0: assert property (
        @(posedge clk) (!load && up_down && ($past(BCD_HIGH) == 4'd1) && ($past(BCD_LOW) == 4'd5)) |=> 
            (BCD_HIGH == 4'd0) && (BCD_LOW == 4'd0)
    );

    // Decrement wrap-around: from 0 -> 15 when counting down (no load).
    check_dec_wrap_0_to_15: assert property (
        @(posedge clk) (!load && !up_down && ($past(BCD_HIGH) == 4'd0) && ($past(BCD_LOW) == 4'd0)) |=> 
            (BCD_HIGH == 4'd1) && (BCD_LOW == 4'd5)
    );

    // Increment carry: from 9 -> 10 when counting up (no load).
    check_inc_carry_9_to_10: assert property (
        @(posedge clk) (!load && up_down && ($past(BCD_HIGH) == 4'd0) && ($past(BCD_LOW) == 4'd9)) |=> 
            (BCD_HIGH == 4'd1) && (BCD_LOW == 4'd0)
    );

    // Decrement borrow: from 10 -> 9 when counting down (no load).
    check_dec_borrow_10_to_9: assert property (
        @(posedge clk) (!load && !up_down && ($past(BCD_HIGH) == 4'd1) && ($past(BCD_LOW) == 4'd0)) |=> 
            (BCD_HIGH == 4'd0) && (BCD_LOW == 4'd9)
    );
endmodule