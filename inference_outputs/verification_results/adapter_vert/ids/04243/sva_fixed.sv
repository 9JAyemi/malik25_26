module mux2_sva (
    input logic A0,
    input logic A1,
    input logic S,
    input logic clk_in_17
);

property ClockSynceotid; @(posedge clk_in_17) (S) == (1) && (A1) != (A0) ; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_in_17) (S) != 1 && (A0) != (A1) ; endproperty
assert property (SyncIneotid);

property SyncCheckeotid; @(posedge clk_in_17) (S) != 1 && (A1) != (A0) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_17) (S) == 1 && (A0) != (A1) ; endproperty
assert property (SyncCheckeotid_2);

endmodule