property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (nand0_out == (A2 && A1)) && (nand1_out == (B2 && B1)) && (and0_out_Y == (nand0_out && nand1_out)) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (Y) |-> (nand0_out == (A2 && A1)) && (nand1_out == (B2 && B1)) && (and0_out_Y == (nand0_out && nand1_out)) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (Y) |-> (nand0_out == (A2 && A1)) && (nand1_out == (B2 && B1)) && (and0_out_Y == (nand0_out && nand1_out)) ;endproperty 
 