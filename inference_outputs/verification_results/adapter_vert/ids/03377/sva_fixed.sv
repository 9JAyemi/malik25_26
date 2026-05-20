module hex_display_sva (
    input logic enable,
    input logic enc,
    input logic in,
    input logic b0000110,
    input logic b0000111,
    input logic b0111001,
    input logic b0111111,
    input logic b1001111,
    input logic b1011011,
    input logic b1011110,
    input logic b1100110,
    input logic b1101101,
    input logic b1101111,
    input logic b1110001,
    input logic b1110111,
    input logic b1111001,
    input logic b1111100,
    input logic b1111101,
    input logic b1111111,
    input logic clk_enable_19,
    input logic h1,
    input logic h2,
    input logic h3,
    input logic h4,
    input logic h5,
    input logic h6,
    input logic h7,
    input logic h8,
    input logic h9,
    input logic ha,
    input logic hb,
    input logic hc,
    input logic hd,
    input logic he,
    input logic hf
);

property EnableSynceotid; @(posedge clk_enable_19) (enable) |-> (enc) == 7'b0111111 ; endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h1 ) |-> (enc) == 7'b0000110 ; endproperty
assert property (EnableSynceotid_2);

property ValidIneotid; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h2 ) |-> (enc) == 7'b1011011 ; endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h3 ) |-> (enc) == 7'b1001111 ; endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h4 ) |-> (enc) == 7'b1100110 ; endproperty
assert property (ValidIneotid_3);

property ValidIneotid_4; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h5 ) |-> (enc) == 7'b1101101 ; endproperty
assert property (ValidIneotid_4);

property ValidIneotid_5; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h6 ) |-> (enc) == 7'b1111101 ; endproperty
assert property (ValidIneotid_5);

property ValidIneotid_6; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h7 ) |-> (enc) == 7'b0000111 ; endproperty
assert property (ValidIneotid_6);

property ValidIneotid_7; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h8 ) |-> (enc) == 7'b1111111 ; endproperty
assert property (ValidIneotid_7);

property ValidIneotid_8; @(posedge clk_enable_19) (enable) &&  (  in  == 4'h9 ) |-> (enc) == 7'b1101111 ; endproperty
assert property (ValidIneotid_8);

property ValidIneotid_9; @(posedge clk_enable_19) (enable) &&  (  in  == 4'ha ) |-> (enc) == 7'b1110111 ; endproperty
assert property (ValidIneotid_9);

property ValidIneotid_10; @(posedge clk_enable_19) (enable) &&  (  in  == 4'hb ) |-> (enc) == 7'b1111100 ; endproperty
assert property (ValidIneotid_10);

property ValidIneotid_11; @(posedge clk_enable_19) (enable) &&  (  in  == 4'hc ) |-> (enc) == 7'b0111001 ; endproperty
assert property (ValidIneotid_11);

property ValidIneotid_12; @(posedge clk_enable_19) (enable) &&  (  in  == 4'hd ) |-> (enc) == 7'b1011110 ; endproperty
assert property (ValidIneotid_12);

property ValidIneotid_13; @(posedge clk_enable_19) (enable) &&  (  in  == 4'he ) |-> (enc) == 7'b1111001 ; endproperty
assert property (ValidIneotid_13);

property ValidIneotid_14; @(posedge clk_enable_19) (enable) &&  (  in  == 4'hf ) |-> (enc) == 7'b1110001 ; endproperty
assert property (ValidIneotid_14);

endmodule