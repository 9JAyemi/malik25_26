property AddSynceotid; @(posedge clk_in_12) (add_sub_ctrl) |-> (add_sub_out) == (a + b) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_12) (add_sub_ctrl) != 1'b1  |-> (add_sub_out) == (a - b) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_12) (mux_enable) |-> (Q) == (add_sub_out[3:0]) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_12) (mux_enable) != 1'b1  |-> (Q) == 4'h0 ; endproperty 
 
 property EnableSynceotid; @(posedge clk_in_12) (add_sub_ctrl) == (mux_enable) ; endproperty 
 