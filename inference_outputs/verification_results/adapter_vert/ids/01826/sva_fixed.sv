module hls_contrast_streibs_sva (
    input logic acc_result,
    input logic din0,
    input logic din1,
    input logic din2,
    input logic dout,
    input logic tmp_mul,
    input logic clk_gen_19
);

property ValidDataeotid; @(posedge clk_gen_19) (din0) |-> (tmp_mul) ;endproperty
assert property (ValidDataeotid);

property ValidAccumulateeotid; @(posedge clk_gen_19) (din0) &&  (din1) &&  (din2) |-> (acc_result) ;endproperty
assert property (ValidAccumulateeotid);

property ValidDataeotid_2; @(posedge clk_gen_19) (din0) &&  (din1) &&  (din2) |-> (dout) ;endproperty
assert property (ValidDataeotid_2);

endmodule