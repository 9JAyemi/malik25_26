module square_module_sva (
    input logic num,
    input logic square,
    input logic b0000,
    input logic b00000000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1000,
    input logic b1001,
    input logic b1010,
    input logic b1011,
    input logic b1100,
    input logic b1101,
    input logic b1110,
    input logic b1111,
    input logic clk_in_19,
    input logic h00,
    input logic h05,
    input logic h0a,
    input logic h0b,
    input logic h18,
    input logic h19,
    input logic h22,
    input logic h23,
    input logic h28,
    input logic h29,
    input logic h30,
    input logic h31,
    input logic h34,
    input logic h35,
    input logic h36,
    input logic h39
);

property Squareeotid; @(posedge clk_in_19) (num) |-> (square) == (num * num); endproperty
assert property (Squareeotid);

property Squareeotid_2; @(posedge clk_in_19) (num) != 4'b0000 |-> (square) != 8'b00000000; endproperty
assert property (Squareeotid_2);

property ValidInputeotid; @(posedge clk_in_19) (num) != 4'b1111 |-> (square) != 8'h39; endproperty
assert property (ValidInputeotid);

property ValidInputeotid_2; @(posedge clk_in_19) (num) != 4'b1110 |-> (square) != 8'h36; endproperty
assert property (ValidInputeotid_2);

property ValidInputeotid_3; @(posedge clk_in_19) (num) != 4'b1101 |-> (square) != 8'h35; endproperty
assert property (ValidInputeotid_3);

property ValidInputeotid_4; @(posedge clk_in_19) (num) != 4'b1100 |-> (square) != 8'h34; endproperty
assert property (ValidInputeotid_4);

property ValidInputeotid_5; @(posedge clk_in_19) (num) != 4'b1011 |-> (square) != 8'h31; endproperty
assert property (ValidInputeotid_5);

property ValidInputeotid_6; @(posedge clk_in_19) (num) != 4'b1010 |-> (square) != 8'h30; endproperty
assert property (ValidInputeotid_6);

property ValidInputeotid_7; @(posedge clk_in_19) (num) != 4'b1001 |-> (square) != 8'h29; endproperty
assert property (ValidInputeotid_7);

property ValidInputeotid_8; @(posedge clk_in_19) (num) != 4'b1000 |-> (square) != 8'h28; endproperty
assert property (ValidInputeotid_8);

property ValidInputeotid_9; @(posedge clk_in_19) (num) != 4'b0111 |-> (square) != 8'h23; endproperty
assert property (ValidInputeotid_9);

property ValidInputeotid_10; @(posedge clk_in_19) (num) != 4'b0110 |-> (square) != 8'h22; endproperty
assert property (ValidInputeotid_10);

property ValidInputeotid_11; @(posedge clk_in_19) (num) != 4'b0101 |-> (square) != 8'h19; endproperty
assert property (ValidInputeotid_11);

property ValidInputeotid_12; @(posedge clk_in_19) (num) != 4'b0100 |-> (square) != 8'h18; endproperty
assert property (ValidInputeotid_12);

property ValidInputeotid_13; @(posedge clk_in_19) (num) != 4'b0011 |-> (square) != 8'h0b; endproperty
assert property (ValidInputeotid_13);

property ValidInputeotid_14; @(posedge clk_in_19) (num) != 4'b0010 |-> (square) != 8'h0a; endproperty
assert property (ValidInputeotid_14);

property ValidInputeotid_15; @(posedge clk_in_19) (num) != 4'b0001 |-> (square) != 8'h05; endproperty
assert property (ValidInputeotid_15);

property ValidInputeotid_16; @(posedge clk_in_19) (num) != 4'b0000 |-> (square) != 8'h00; endproperty
assert property (ValidInputeotid_16);

endmodule