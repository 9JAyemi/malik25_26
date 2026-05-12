property SyncIneotid; @(negedge clk_in_1) (A) and (B) |-> nand1_out == 2'b0x ;endproperty 
 
 property SyncIneotid; @(negedge clk_in_1) (C) and (D) |-> nand2_out == 2'b0x ;endproperty 
 
 property SyncIneotid; @(negedge clk_in_1) (nand1_out) and (nand2_out) |-> nand3_out == 2'b0x ;endproperty 
 
 property SyncIneotid; @(negedge clk_in_1) (nand3_out) and (nand3_out) |-> Z == 2'b10 ;endproperty 
 
 property SyncIneotid; @(negedge clk_in_1) (Z) and (Z) |-> Z == 2'b01 ;endproperty 
 