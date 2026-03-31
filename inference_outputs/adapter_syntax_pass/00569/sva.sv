module RegisterAdd_sva (
    input logic [1:0] FSM_sequential_state_reg_reg,
    input logic FSM_selector_C,
    input logic clk_IBUF_BUFG,
    input logic AR
);

    // When FSM_selector_C is high, the next state is forced to 00.
    check_clear_on_selector: assert property (
        @(posedge clk_IBUF_BUFG) FSM_selector_C |=> (FSM_sequential_state_reg_reg == 2'b00)
    );

    // When FSM_selector_C is low, the next state increments by AR modulo 4.
    check_increment_on_ar: assert property (
        @(posedge clk_IBUF_BUFG) !FSM_selector_C |=> (FSM_sequential_state_reg_reg == ($past(FSM_sequential_state_reg_reg) + $past(AR)))
    );

    // The upper bit of the state always stays zero after each clocked update.
    check_upper_bit_zero: assert property (
        @(posedge clk_IBUF_BUFG) 1'b1 |=> (FSM_sequential_state_reg_reg[1] == 1'b0)
    );

    // A zero increment leaves the state unchanged when selector is low.
    check_zero_increment_holds: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b0)) |=> (FSM_sequential_state_reg_reg == $past(FSM_sequential_state_reg_reg))
    );

    // A one increment wraps the state from 1 to 0 when selector is low.
    check_one_increment_wraps: assert property (
        @(posedge clk_IBUF_BUFG) (!FSM_selector_C && (AR == 1'b1)) |=> (FSM_sequential_state_reg_reg == 2'b00)
    );

endmodule