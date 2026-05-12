property InvertOnRiseeotid; @(posedge clk_in_12) (i_binary) |-> (o_inverted) == ({~i_binary[3], i_binary[2:0]}); endproperty 
 
 property SyncIneotid; @(posedge clk_in_12) (i_binary) != 4'b0000 |-> (o_inverted) != 4'b0000; endproperty 
 
 property SyncIneotid; @(posedge clk_in_12) (i_binary) != 4'b1111 |-> (o_inverted) != 4'b1111; endproperty 
 
 property SyncIneotid; @(posedge clk_in_12) (i_binary) != 7'b1000000 |-> (o_inverted) != 7'b0111111; endproperty 
 
 property SyncIneotid; @(posedge clk_in_12) (i_binary) != 7'b0111111 |-> (o_inverted) != 7'b1000000; endproperty 
 