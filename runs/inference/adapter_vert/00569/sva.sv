property ResetSynceotid; @(posedge clk_IBUF_BUFG) (FSM_selector_C) |-> (FSM_sequential_state_reg_reg == 2'b00) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_IBUF_BUFG) (FSM_selector_C) != 1'b1  |-> (FSM_sequential_state_reg_reg == FSM_sequential_state_reg_reg + AR) ; endproperty 
 