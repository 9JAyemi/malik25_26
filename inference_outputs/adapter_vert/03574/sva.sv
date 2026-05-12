property Squareeotid; @(posedge clk_in_19) (num) |-> (square) == (num * num); endproperty 
 
 property Squareeotid; @(posedge clk_in_19) (num) != 4'b0000 |-> (square) != 8'b00000000; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b1111 |-> (square) != 8'h39; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b1110 |-> (square) != 8'h36; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b1101 |-> (square) != 8'h35; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b1100 |-> (square) != 8'h34; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b1011 |-> (square) != 8'h31; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b1010 |-> (square) != 8'h30; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b1001 |-> (square) != 8'h29; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b1000 |-> (square) != 8'h28; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b0111 |-> (square) != 8'h23; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b0110 |-> (square) != 8'h22; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b0101 |-> (square) != 8'h19; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b0100 |-> (square) != 8'h18; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b0011 |-> (square) != 8'h0b; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b0010 |-> (square) != 8'h0a; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b0001 |-> (square) != 8'h05; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b0000 |-> (square) != 8'h00; endproperty 
 
 