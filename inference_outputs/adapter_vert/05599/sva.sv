property ResetSynceotid; @(posedge clk) (reset) |-> out == 4'b0 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (reset) != 1'b1 && (load) |-> out == data[3:0] ;endproperty 
 
 property ValidDataeotid; @(posedge clk) (reset) != 1'b1 && !(load)  && (select) |-> out == {in[2:0], in[3]} ;endproperty 
 
 property ValidDataeotid; @(posedge clk) (reset) != 1'b1 && !(load)  && !(select)  |-> out == {in[0], in[3:1]} ;endproperty 
 