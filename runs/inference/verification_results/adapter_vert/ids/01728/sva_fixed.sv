module mult_select_sva (
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic X,
    input logic clk_in_11
);

property ClockSynceotid; @(posedge clk_in_11) (A1) && (A2) &&  ( !B1_N ) |-> (X) ;endproperty
assert property (ClockSynceotid);

property ValidSynceotid; @(posedge clk_in_11)  ( !A1 ) && (A2) &&  ( B1_N ) |-> (X) ;endproperty
assert property (ValidSynceotid);

endmodule