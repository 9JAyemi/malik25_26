property LockOneotid; @(posedge clk_in_1) (key_input) == (9'b0000000001) |-> (led_output) == 5'b00001 ; endproperty 
 
 property LockOneotid; @(posedge clk_in_1) (key_input) == (9'b0000000010) |-> (led_output) == 5'b00010 ; endproperty 
 
 property LockOneotid; @(posedge clk_in_1) (key_input) == (9'b0000000100) |-> (led_output) == 5'b00100 ; endproperty 
 
 property LockOneotid; @(posedge clk_in_1) (key_input) == (9'b0000001000) |-> (led_output) == 5'b01000 ; endproperty 
 
 property LockOneotid; @(posedge clk_in_1) (key_input) == (9'b0000010000) |-> (led_output) == 5'b10000 ; endproperty 
 
 property ResetOnClockeotid; @(posedge clk_in_1) (key_input) == (9'b0000100000) |-> (led_output) == 5'b00000 ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (key_input) == (9'b0001000000) |-> (led_output) == 5'b11111 ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (key_input) != 9'b0000000001 && @(posedge clk_in_1) (key_input) != 9'b0000000010 && @(posedge clk_in_1) (key_input) != 9'b0000000100 && @(posedge clk_in_1) (key_input) != 9'b0000001000 && @(posedge clk_in_1) (key_input) != 9'b0000010000 && @(posedge clk_in_1) (key_input) != 9'b0000100000 && @(posedge clk_in_1) (key_input) != 9'b0001000000  |-> (led_output) == 5'bxxxxx; endproperty 
 