module fourBitAdder_sva (
    input logic A,
    input logic B,
    input logic Cin,
    input logic Cout,
    input logic Sum,
    input logic temp_sum,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (A) |-> (temp_sum) == (A + B + Cin); endproperty
assert property (AdderSynceotid);

property ValidSumeotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (Sum) == (temp_sum[3:0]); endproperty
assert property (ValidSumeotid);

property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (Cout) == (temp_sum[4]); endproperty
assert property (CarrySynceotid);

endmodule