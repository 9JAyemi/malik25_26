module LedOutput_sva (
    input logic key_input,
    input logic led_output,
    input logic b00000,
    input logic b0000000001,
    input logic b0000000010,
    input logic b0000000100,
    input logic b0000001000,
    input logic b0000010000,
    input logic b00001,
    input logic b0000100000,
    input logic b00010,
    input logic b0001000000,
    input logic b00100,
    input logic b01000,
    input logic b10000,
    input logic b11111,
    input logic bxxxxx,
    input logic clk_in_1
);

property LockOneotid; @(posedge clk_in_1) (key_input) == (9'b0000000001) |-> (led_output) == 5'b00001 ; endproperty
assert property (LockOneotid);

property LockOneotid_2; @(posedge clk_in_1) (key_input) == (9'b0000000010) |-> (led_output) == 5'b00010 ; endproperty
assert property (LockOneotid_2);

property LockOneotid_3; @(posedge clk_in_1) (key_input) == (9'b0000000100) |-> (led_output) == 5'b00100 ; endproperty
assert property (LockOneotid_3);

property LockOneotid_4; @(posedge clk_in_1) (key_input) == (9'b0000001000) |-> (led_output) == 5'b01000 ; endproperty
assert property (LockOneotid_4);

property LockOneotid_5; @(posedge clk_in_1) (key_input) == (9'b0000010000) |-> (led_output) == 5'b10000 ; endproperty
assert property (LockOneotid_5);

property ResetOnClockeotid; @(posedge clk_in_1) (key_input) == (9'b0000100000) |-> (led_output) == 5'b00000 ; endproperty
assert property (ResetOnClockeotid);

property ValidInputeotid; @(posedge clk_in_1) (key_input) == (9'b0001000000) |-> (led_output) == 5'b11111 ; endproperty
assert property (ValidInputeotid);

property ValidInputeotid_2; @(posedge clk_in_1) (key_input) != 9'b0000000001 && @(posedge clk_in_1) (key_input) != 9'b0000000010 && @(posedge clk_in_1) (key_input) != 9'b0000000100 && @(posedge clk_in_1) (key_input) != 9'b0000001000 && @(posedge clk_in_1) (key_input) != 9'b0000010000 && @(posedge clk_in_1) (key_input) != 9'b0000100000 && @(posedge clk_in_1) (key_input) != 9'b0001000000  |-> (led_output) == 5'bxxxxx; endproperty
assert property (ValidInputeotid_2);

endmodule