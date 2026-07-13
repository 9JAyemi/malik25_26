property MemLockeotid; @(posedge clk_gen_1) (mem_addr) |-> (enc_data) == (mem_data ^ key) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_gen_1) (mem_data) != (key) |-> (enc_data) != (mem_data) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_gen_1) (mem_data) != (key) ||  (mem_addr) != 7'b0000000  |-> (enc_data) != (mem_data) ;endproperty 
 