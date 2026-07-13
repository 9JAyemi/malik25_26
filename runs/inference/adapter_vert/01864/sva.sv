property ValidSecteotid; @(posedge clk_in_1) (sector) == (3'd1) |-> (flash_sector) == (3'b000); endproperty 
 
 property ValidSecteotid; @(posedge clk_in_1) (sector) == (3'd2) |-> (flash_sector) == (3'b001); endproperty 
 
 property ValidSecteotid; @(posedge clk_in_1) (sector) == (3'd3) |-> (flash_sector) == (3'b010); endproperty 
 
 property ValidSecteotid; @(posedge clk_in_1) (sector) == (3'd4) |-> (flash_sector) == (3'b011); endproperty 
 
 property ValidSecteotid; @(posedge clk_in_1) (sector) == (3'd5) |-> (flash_sector) == (3'b100); endproperty 
 
 property ValidSecteotid; @(posedge clk_in_1) (sector) != 3'd1 && (sector) != 3'd2 && (sector) != 3'd3 && (sector) != 3'd4 && (sector) != 3'd5  |-> (flash_sector) == 3'b000; endproperty 
 