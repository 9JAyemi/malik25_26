module oh_mux4_sva (
    input logic DW,
    input logic error,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out,
    input logic sel0,
    input logic sel1,
    input logic sel2,
    input logic sel3,
    input logic clk_in_1
);

property ValidDataeotid; @(posedge clk_in_1) (sel0) |-> (out[DW-1:0] == in0[DW-1:0]); endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (sel1) |-> (out[DW-1:0] == in1[DW-1:0]); endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_1) (sel2) |-> (out[DW-1:0] == in2[DW-1:0]); endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_1) (sel3) |-> (out[DW-1:0] == in3[DW-1:0]); endproperty
assert property (ValidDataeotid_4);

property ValidSynceotid; @(posedge clk_in_1) (sel0) &&  (  (sel1) ||  (sel2) ||  (sel3)  ) |->  (error)  ; endproperty
assert property (ValidSynceotid);

property ValidSynceotid_2; @(posedge clk_in_1) (sel1) &&  (  (sel0) ||  (sel2) ||  (sel3)  ) |->  (error)  ; endproperty
assert property (ValidSynceotid_2);

property ValidSynceotid_3; @(posedge clk_in_1) (sel2) &&  (  (sel0) ||  (sel1) ||  (sel3)  ) |->  (error)  ; endproperty
assert property (ValidSynceotid_3);

property ValidSynceotid_4; @(posedge clk_in_1) (sel3) &&  (  (sel0) ||  (sel1) ||  (sel2)  ) |->  (error)  ; endproperty
assert property (ValidSynceotid_4);

endmodule