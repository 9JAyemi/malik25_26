module RegisterAdd_sva (
    input logic FSM_selector_C,
    input logic [1:0] FSM_sequential_state_reg_reg,
    input logic clk_IBUF_BUFG,
    input logic AR
);

// When FSM_selector_C is high, the next state is 00.
    check_reset_forces_zero: assert property (
        @(posedge clk_IBUF_BUFG) FSM_selector_C |=> (FSM_sequential_state_reg_reg == 2'b00)
    );

// When FSM_selector_C is low, the next state increments by AR modulo 4.
    check_increment_by_ar: assert property (
        @(posedge clk_IBUF_BUFG) !FSM_selector_C |=> (FSM_sequential_state_reg_reg == ($past(FSM_sequential_state_reg_reg) + $past(AR)))
    );

// When AR is 0, the next state holds its value.
    check_hold_when_ar_zero: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b0)) |=> (FSM_sequential_state_reg_reg == $past(FSM_sequential_state_reg_reg))
    );

// When AR is 1, the next state increments by 1 modulo 4.
    check_increment_by_one: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b1)) |=> (FSM_sequential_state_reg_reg == ($past(FSM_sequential_state_reg_reg) + 2'd1))
    );

// When AR is 2, the next state increments by 2 modulo 4.
    check_increment_by_two: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 2'b10)) |=> (FSM_sequential_state_reg_reg == ($past(FSM_sequential_state_reg_reg) + 2'd2))
    );

// When AR is 3, the next state increments by 3 modulo 4.
    check_increment_by_three: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 2'b11)) |=> (FSM_sequential_state_reg_reg == ($past(FSM_sequential_state_reg_reg) + 2'd3))
    );

endmodule
