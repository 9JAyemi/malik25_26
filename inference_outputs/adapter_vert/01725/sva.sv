property ValidAddrCheckeotid; @(posedge clk_in_1) (addr) == (12'h000) |-> (mod) == 8'h0 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (8'h10) |-> (mod) == 8'h1 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf00) |-> (mod) == 8'h2 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf01) |-> (mod) == 8'h3 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf02) |-> (mod) == 8'h4 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf03) |-> (mod) == 8'h5 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf04) |-> (mod) == 8'h6 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf05) |-> (mod) == 8'h7 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf06) |-> (mod) == 8'h8 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf07) |-> (mod) == 10'h2 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf08) |-> (mod) == 11'hb ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (12'hf0a) |-> (mod) == 9'h9 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (addr) != 12'h000 && @(posedge clk_in_1) (addr) != 8'h10 && @(posedge clk_in_1) (addr) != 12'hf00 && @(posedge clk_in_1) (addr) != 12'hf01 && @(posedge clk_in_1) (addr) != 12'hf02 && @(posedge clk_in_1) (addr) != 12'hf03 && @(posedge clk_in_1) (addr) != 12'hf04 && @(posedge clk_in_1) (addr) != 12'hf05 && @(posedge clk_in_1) (addr) != 12'hf06 && @(posedge clk_in_1) (addr) != 12'hf07 && @(posedge clk_in_1) (addr) != 12'hf08 && @(posedge clk_in_1) (addr) != 12'hf0a  |-> (mod) == 8'h0 ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (mod) == 8'h1 |-> (eff_addr) == {8'h00,addr[23:0]} ; endproperty 
 
 property ValidAddrRuneotid; @(posedge clk_in_1) (mod) != 8'h1  |-> (eff_addr) == {12'h000,addr[19:0]} ; endproperty 
 