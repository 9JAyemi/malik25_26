module nand_decoder_sva (
    input logic and_out,
    input logic in,
    input logic not1_out,
    input logic not2_out,
    input logic not3_out,
    input logic not4_out,
    input logic clk_in_1
);

property ValidIneotid; @(posedge clk_in_1) (in) |-> (and_out) ;endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (in) |-> (not1_out) ;endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_in_1) (in) |-> (not2_out) ;endproperty
assert property (ValidIneotid_3);

property ValidIneotid_4; @(posedge clk_in_1) (in) |-> (not3_out) ;endproperty
assert property (ValidIneotid_4);

property ValidIneotid_5; @(posedge clk_in_1) (in) |-> (not4_out) ;endproperty
assert property (ValidIneotid_5);

endmodule