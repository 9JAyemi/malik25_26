module RegisterAdd_sva (
    input logic       FSM_selector_C,
    input logic [1:0] FSM_sequential_state_reg_reg,
    input logic       clk_IBUF_BUFG,
    input logic       AR
);

    // Selector forces the state register to 00 on the next clock.
    check_selector_clears_state: assert property (
        @(posedge clk_IBUF_BUFG)
        FSM_selector_C |=> (FSM_sequential_state_reg_reg == 2'b00)
    );

    // With selector low and AR low, state 00 holds.
    check_hold_00_when_ar_low: assert property (
        @(posedge clk_IBUF_BUFG)
        (!FSM_selector_C && !AR && (FSM_sequential_state_reg_reg == 2'b00)) |=> (FSM_sequential_state_reg_reg == 2'b00)
    );

    // With selector low and AR low, state 01 holds.
    check_hold_01_when_ar_low: assert property (
        @(posedge clk_IBUF_BUFG)
        (!FSM_selector_C && !AR && (FSM_sequential_state_reg_reg == 2'b01)) |=> (FSM_sequential_state_reg_reg == 2'b01)
    );

    // With selector low and AR low, state 10 holds.
    check_hold_10_when_ar_low: assert property (
        @(posedge clk_IBUF_BUFG)
        (!FSM_selector_C && !AR && (FSM_sequential_state_reg_reg == 2'b10)) |=> (FSM_sequential_state_reg_reg == 2'b10)
    );

    // With selector low and AR low, state 11 holds.
    check_hold_11_when_ar_low: assert property (
        @(posedge clk_IBUF_BUFG)
        (!FSM_selector_C && !AR && (FSM_sequential_state_reg_reg == 2'b11)) |=> (FSM_sequential_state_reg_reg == 2'b11)
    );

    // With selector low and AR high, state 00 increments to 01.
    check_increment_00_to_01: assert property (
        @(posedge clk_IBUF_BUFG)
        (!FSM_selector_C && AR && (FSM_sequential_state_reg_reg == 2'b00)) |=> (FSM_sequential_state_reg_reg == 2'b01)
    );

    // With selector low and AR high, state 01 increments to 10.
    check_increment_01_to_10: assert property (
        @(posedge clk_IBUF_BUFG)
        (!FSM_selector_C && AR && (FSM_sequential_state_reg_reg == 2'b01)) |=> (FSM_sequential_state_reg_reg == 2'b10)
    );

    // With selector low and AR high, state 10 increments to 11.
    check_increment_10_to_11: assert property (
        @(posedge clk_IBUF_BUFG)
        (!FSM_selector_C && AR && (FSM_sequential_state_reg_reg == 2'b10)) |=> (FSM_sequential_state_reg_reg == 2'b11)
    );

    // With selector low and AR high, state 11 wraps to 00.
    check_increment_11_to_00: assert property (
        @(posedge clk_IBUF_BUFG)
        (!FSM_selector_C && AR && (FSM_sequential_state_reg_reg == 2'b11)) |=> (FSM_sequential_state_reg_reg == 2'b00)
    );

endmodule