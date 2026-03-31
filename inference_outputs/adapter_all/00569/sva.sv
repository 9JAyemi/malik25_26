module RegisterAdd_sva (
    input logic FSM_selector_C,
    input logic [1:0] FSM_sequential_state_reg_reg,
    input logic clk_IBUF_BUFG,
    input logic AR
);
    // Clock: clk_IBUF_BUFG (posedge). Reset: none. Logic: sequential (registered add with clear).

    // On clear, next cycle state must be 00.
    check_clear_sets_zero: assert property (
        @(posedge clk_IBUF_BUFG) FSM_selector_C |=> (FSM_sequential_state_reg_reg == 2'b00)
    );

    // On no clear, next cycle state equals prev state + prev AR (mod 4).
    check_add_when_no_clear: assert property (
        @(posedge clk_IBUF_BUFG) !FSM_selector_C |=> (FSM_sequential_state_reg_reg == $past(FSM_sequential_state_reg_reg) + $past(AR))
    );

    // If no clear and AR==0, state holds its value.
    check_hold_when_ar_zero: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b0)) |=> (FSM_sequential_state_reg_reg == $past(FSM_sequential_state_reg_reg))
    );

    // If no clear and AR==1, state increments by 1 (mod 4).
    check_increment_by_one: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b1)) |=> (FSM_sequential_state_reg_reg == $past(FSM_sequential_state_reg_reg) + 2'd1)
    );

    // If no clear and AR==3, state increments by 3 (mod 4).
    check_increment_by_three: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 3'b11)) |=> (FSM_sequential_state_reg_reg == $past(FSM_sequential_state_reg_reg) + 2'd3)
    );

    // If no clear and AR==2, state increments by 2 (mod 4).
    check_increment_by_two: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 2'b10)) |=> (FSM_sequential_state_reg_reg == $past(FSM_sequential_state_reg_reg) + 2'd2)
    );

    // If no clear and AR==1, next state is not 00 (since prev state != 00).
    check_no_zero_after_inc_one: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b1)) |=> (FSM_sequential_state_reg_reg != 2'b00)
    );

    // If no clear and AR==3, next state is not 00 (since prev state != 00).
    check_no_zero_after_inc_three: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 3'b11)) |=> (FSM_sequential_state_reg_reg != 2'b00)
    );

    // If no clear and AR==2, next state is not 00 (since prev state != 00).
    check_no_zero_after_inc_two: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 2'b10)) |=> (FSM_sequential_state_reg_reg != 2'b00)
    );

    // If no clear and AR==0, next state is not 01 (since prev state != 01).
    check_no_one_after_hold: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b0)) |=> (FSM_sequential_state_reg_reg != 2'b01)
    );

    // If no clear and AR==0, next state is not 10 (since prev state != 10).
    check_no_two_after_hold: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b0)) |=> (FSM_sequential_state_reg_reg != 2'b10)
    );

    // If no clear and AR==0, next state is not 11 (since prev state != 11).
    check_no_three_after_hold: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b0)) |=> (FSM_sequential_state_reg_reg != 2'b11)
    );

endmodule