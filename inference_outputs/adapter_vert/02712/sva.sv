property DataSynceotid; @(posedge clk_in_1) (sel_b1) |-> (parity) == (~xor_out) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (sel_b1) |-> (data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) ! (sel_b1) |-> (parity) == (xor_out) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) ! (sel_b1) |-> (data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]) ; endproperty 
 