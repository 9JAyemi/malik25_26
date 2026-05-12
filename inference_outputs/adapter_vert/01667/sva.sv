property ValidTickeotid; @(posedge clk_in_1) (button1 | button2 | button3) & ~coin |-> product1 == 1'b1 ; endproperty 
 
 property ValidTickeotid; @(posedge clk_in_1) (button1 | button2 | button3) & ~coin |-> product2 == 1'b1 ; endproperty 
 
 property ValidTickeotid; @(posedge clk_in_1) (button1 | button2 | button3) & ~coin |-> product3 == 1'b1 ; endproperty 
 
 property ValidTickeotid; @(posedge clk_in_1) (button1 | button2 | button3) & ~coin |-> change == 1'b1 ; endproperty 
 
 property ValidTickeotid; @(posedge clk_in_1)  (button1 != 1'b1 && button2 != 1'b1 && button3 != 1'b1)  |-> product1 == 1'b0 ; endproperty 
 
 property ValidTickeotid; @(posedge clk_in_1)  (button1 != 1'b1 && button2 != 1'b1 && button3 != 1'b1)  |-> product2 == 1'b0 ; endproperty 
 
 property ValidTickeotid; @(posedge clk_in_1)  (button1 != 1'b1 && button2 != 1'b1 && button3 != 1'b1)  |-> product3 == 1'b0 ; endproperty 
 
 property ValidTickeotid; @(posedge clk_in_1)  (button1 != 1'b1 && button2 != 1'b1 && button3 != 1'b1)  |-> change == 1'b0 ; endproperty 
 