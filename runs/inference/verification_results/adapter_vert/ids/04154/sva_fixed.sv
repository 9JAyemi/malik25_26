module invert_msb_sva (
    input logic i_binary,
    input logic o_inverted,
    input logic b0000,
    input logic b0111111,
    input logic b1000000,
    input logic b1111,
    input logic clk_in_12
);

property InvertOnRiseeotid; @(posedge clk_in_12) (i_binary) |-> (o_inverted) == ({~i_binary[3], i_binary[2:0]}); endproperty
assert property (InvertOnRiseeotid);

property SyncIneotid; @(posedge clk_in_12) (i_binary) != 4'b0000 |-> (o_inverted) != 4'b0000; endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_12) (i_binary) != 4'b1111 |-> (o_inverted) != 4'b1111; endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_12) (i_binary) != 7'b1000000 |-> (o_inverted) != 7'b0111111; endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk_in_12) (i_binary) != 7'b0111111 |-> (o_inverted) != 7'b1000000; endproperty
assert property (SyncIneotid_4);

endmodule