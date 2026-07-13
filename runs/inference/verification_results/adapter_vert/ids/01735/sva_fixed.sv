module tri_buf_sva (
    input logic A,
    input logic TE_B,
    input logic Z,
    input logic b0,
    input logic clk_in_19
);

property ClockSynceotid; @(posedge clk_in_19) (TE_B) |-> (Z) == 1'b0 ; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_in_19) (TE_B) |-> (A) == 1'b0 ; endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_19) ! (TE_B)  |-> (Z) ==  (A) ; endproperty
assert property (SyncIneotid_2);

endmodule