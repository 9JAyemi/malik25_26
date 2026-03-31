```systemverilog
module RegisterAdd_sva (
    input logic FSM_selector_C,
    input logic [1:0] FSM_sequential_state_reg_reg,
    input logic clk_IBUF_BUFG,
    input logic AR
);
    ///// Sequential logic behavior /////
    // FSM_sequential_state_reg_reg should be reset to 2'b00 when FSM_selector_C is HIGH.
    reset_to_zero: assert property (
        @(posedge clk_IBUF_BUFG) disable iff (!clk_IBUF_BUFG) FSM_selector_C |-> (FSM_sequential_state_reg_reg == 2'b00)
    );
    // FSM_sequential_state_reg_reg should increment by AR when FSM_selector_C is LOW.
    increment_on_ar: assert property (
        @(posedge clk_IBUF_BUFG) disable iff (!clk_IBUF_BUFG) !FSM_selector_C |-> FSM_sequential_state_reg_reg == FSM_sequential_state_reg_reg + AR
    );
endmodule
```