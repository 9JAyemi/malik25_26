property ClockSynceotid; @(posedge clk_in_13) (Boo_ba1) |-> (f1_dotnamed) == (Boo_ba1 << 1) ; endproperty 
 
 property AddSynceotid; @(posedge clk_in_13) (Boo_ba2) &&  (b) |-> (f2_dotnamed) == (Boo_ba2 + b) ; endproperty 
 
 property SyncSubeotid; @(posedge clk_in_13) (Boo_ba3) &&  (c) |-> (f3_dotnamed) == (Boo_ba3 - c) ; endproperty 
 
 property SyncAdder; @(posedge clk_in_13) (Boo_ba1) |-> (f4_dotnamed) == (f1_dotnamed + f2_dotnamed + f3_dotnamed) ; endproperty 
 