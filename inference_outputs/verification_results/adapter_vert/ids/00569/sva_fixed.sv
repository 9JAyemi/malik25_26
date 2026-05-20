module RegisterAdd_sva (
    input logic AR,
    input logic FSM_selector_C,
    input logic FSM_sequential_state_reg_reg,
    input logic clk_IBUF_BUFG,
    input logic b00,
    input logic b1
);

property ResetSynceotid; @(posedge clk_IBUF_BUFG) (FSM_selector_C) |-> (FSM_sequential_state_reg_reg == 2'b00) ; endproperty
assert property (ResetSynceotid);

property SyncCheckeotid; @(posedge clk_IBUF_BUFG) (FSM_selector_C) != 1'b1  |-> (FSM_sequential_state_reg_reg == FSM_sequential_state_reg_reg + AR) ; endproperty
assert property (SyncCheckeotid);

endmodule