module sqrt_calc_sva (
    input logic done,
    input logic x,
    input logic x_int,
    input logic y_n,
    input logic y_n1,
    input logic b0,
    input logic b1,
    input logic clk_reset_19,
    input logic h80
);

property ResetSynceotid; @(negedge clk_reset_19) (x) |-> (x_int) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_19) (x) |-> (y_n) == 8'h80 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_19) (x) &&  (  (y_n1 >= y_n-1 && y_n1 <= y_n+1)  ) |-> (done) == 1'b1 ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_19) (x) &&  (  !(  (y_n1 >= y_n-1 && y_n1 <= y_n+1)  )  ) |-> (y_n) == (y_n1) && (done) == 1'b0 ;endproperty
assert property (ResetSynceotid_4);

endmodule