module pipereg_w26_sva (
    input logic clk,
    input logic d,
    input logic en,
    input logic q,
    input logic resetn,
    input logic squashn
);

property ResetSynceotid; @(posedge clk) (resetn==0 || squashn==0) |-> q == 0 ; endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (resetn!=0 && squashn!=0) && (en==1) |-> q == d ; endproperty
assert property (EnableSynceotid);

endmodule