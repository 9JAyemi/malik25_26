module button_counter_sva (
    input logic clk,
    input logic button,
    input logic [2:0] count,
    input logic [1:0] state
);
    // When button is LOW, count holds its value into the next cycle.
    check_count_hold_when_button_low: assert property (
        @(posedge clk) !button |=> (count == $past(count))
    );

    // When button is LOW, state holds its value into the next cycle.
    check_state_hold_when_button_low: assert property (
        @(posedge clk) !button |=> (state == $past(state))
    );

    // When button is HIGH, count increments by 1 (modulo 8) into the next cycle.
    check_count_increment_when_button_high: assert property (
        @(posedge clk) button |=> (count == ($past(count) + 3'd1))
    );

    // When button is HIGH and state==0, next state is 1.
    check_state_advance_0_to_1: assert property (
        @(posedge clk) (button && (state == 2'd0)) |=> (state == 2'd1)
    );

    // When button is HIGH and state==1, next state is 2.
    check_state_advance_1_to_2: assert property (
        @(posedge clk) (button && (state == 2'd1)) |=> (state == 2'd2)
    );

    // When button is HIGH and state==2, next state is 3.
    check_state_advance_2_to_3: assert property (
        @(posedge clk) (button && (state == 2'd2)) |=> (state == 2'd3)
    );

    // When button is HIGH and state==3, next state is 0.
    check_state_advance_3_to_0: assert property (
        @(posedge clk) (button && (state == 2'd3)) |=> (state == 2'd0)
    );

    // When button is HIGH and count==7, next count wraps to 0.
    check_count_wrap_7_to_0: assert property (
        @(posedge clk) (button && (count == 3'd7)) |=> (count == 3'd0)
    );

    // Two consecutive cycles of button HIGH increment count by 2 (modulo 8).
    check_two_cycle_count_increment: assert property (
        @(posedge clk) button[*2] |=> (count == ($past(count,2) + 3'd2))
    );

    // Four consecutive cycles of button HIGH return state to its original value.
    check_state_period_4_when_held_high: assert property (
        @(posedge clk) button[*4] |=> (state == $past(state,4))
    );

    // Eight consecutive cycles of button HIGH return count to its original value.
    check_count_period_8_when_held_high: assert property (
        @(posedge clk) button[*8] |=> (count == $past(count,8))
    );

    // Two consecutive cycles of button LOW keep both count and state unchanged over 2 cycles.
    check_hold_over_two_low_cycles: assert property (
        @(posedge clk) (!button)[*2] |=> (count == $past(count,2)) && (state == $past(state,2))
    );
endmodule