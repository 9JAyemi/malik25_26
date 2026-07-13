property EnableSynceotid; @(posedge clk_enable_19) (enable) |-> (enc) == 7'b0111111 ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h1 ) |-> (enc) == 7'b0000110 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h2 ) |-> (enc) == 7'b1011011 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h3 ) |-> (enc) == 7'b1001111 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h4 ) |-> (enc) == 7'b1100110 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h5 ) |-> (enc) == 7'b1101101 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h6 ) |-> (enc) == 7'b1111101 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h7 ) |-> (enc) == 7'b0000111 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h8 ) |-> (enc) == 7'b1111111 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h9 ) |-> (enc) == 7'b1101111 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'ha ) |-> (enc) == 7'b1110111 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'hb ) |-> (enc) == 7'b1111100 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'hc ) |-> (enc) == 7'b0111001 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'hd ) |-> (enc) == 7'b1011110 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'he ) |-> (enc) == 7'b1111001 ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'hf ) |-> (enc) == 7'b1110001 ; endproperty 
 
 