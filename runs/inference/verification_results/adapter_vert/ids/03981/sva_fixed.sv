module DEMUX_3to8_sva (
    input logic in,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3,
    input logic out4,
    input logic out5,
    input logic out6,
    input logic out7,
    input logic sel0,
    input logic sel1,
    input logic sel2,
    input logic b0,
    input logic b1,
    input logic clk_in_1
);

property ValidIneotid; @(posedge clk_in_1) (in) |-> (out0 == 1'b1) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (in) &&  (  (sel2 == 0) && (sel1 == 0) && (sel0 == 0)  ) |-> (out0 == 1'b1) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_in_1) (in) &&  (  (sel2 == 0) && (sel1 == 0) && (sel0 == 1)  ) |-> (out0 == 1'b0) && (out1 == 1'b1) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty
assert property (ValidIneotid_3);

property ValidIneotid_4; @(posedge clk_in_1) (in) &&  (  (sel2 == 0) && (sel1 == 1) && (sel0 == 0)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b1) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty
assert property (ValidIneotid_4);

property ValidIneotid_5; @(posedge clk_in_1) (in) &&  (  (sel2 == 0) && (sel1 == 1) && (sel0 == 1)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b1) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty
assert property (ValidIneotid_5);

property ValidIneotid_6; @(posedge clk_in_1) (in) &&  (  (sel2 == 1) && (sel1 == 0) && (sel0 == 0)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b1) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty
assert property (ValidIneotid_6);

property ValidIneotid_7; @(posedge clk_in_1) (in) &&  (  (sel2 == 1) && (sel1 == 0) && (sel0 == 1)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b1) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty
assert property (ValidIneotid_7);

property ValidIneotid_8; @(posedge clk_in_1) (in) &&  (  (sel2 == 1) && (sel1 == 1) && (sel0 == 0)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b1) && (out7 == 1'b0) ;endproperty
assert property (ValidIneotid_8);

property ValidIneotid_9; @(posedge clk_in_1) (in) &&  (  (sel2 == 1) && (sel1 == 1) && (sel0 == 1)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b1) ;endproperty
assert property (ValidIneotid_9);

endmodule