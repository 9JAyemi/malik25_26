property SyncCheckeotid; @(posedge clk_osc_19) (A1) && (A2) && (B1) && (C1) && (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (A1) && (A2) && ! (B1) && (C1) && (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (A1) && (A2) &&  (B1) && ! (C1) && (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (A1) && (A2) &&  (B1) &&  (C1) && ! (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) ! (A1) && ! (A2) &&  (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) ! (A1) && ! (A2) && ! (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) ! (A1) && ! (A2) &&  (B1) && ! (C1) &&  (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) ! (A1) && ! (A2) &&  (B1) &&  (C1) && ! (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) ! (A1) &&  (A2) &&  (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) ! (A1) &&  (A2) && ! (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) ! (A1) &&  (A2) &&  (B1) && ! (C1) &&  (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) ! (A1) &&  (A2) &&  (B1) &&  (C1) && ! (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19)  (A1) && ! (A2) &&  (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19)  (A1) && ! (A2) && ! (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19)  (A1) && ! (A2) &&  (B1) && ! (C1) &&  (D1) |-> (Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19)  (A1) && ! (A2) &&  (B1) &&  (C1) && ! (D1) |-> (Y) ; endproperty 
 
 endmodule
