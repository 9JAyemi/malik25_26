module sky130_fd_sc_ms__a221oi_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic Y,
    input logic and0_out,
    input logic and1_out,
    input logic nor0_out_Y,
    input logic clock_div_13
);

property ClockSynceotid; @(posedge clock_div_13) (Y) |-> (and0_out == (B1 && B2)) && (and1_out == (A1 && A2)) && (nor0_out_Y != (and0_out || C1 || and1_out)); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock_div_13) (Y) |-> (and0_out == (B1 && B2)) && (and1_out == (A1 && A2)) && (nor0_out_Y != (and0_out || C1 || and1_out)); endproperty
assert property (ClockSynceotid_2);

property SyncSafeeotid; @(posedge clock_div_13) (Y) |-> (and0_out == (B1 && B2)) && (and1_out == (A1 && A2)) && (nor0_out_Y != (and0_out || C1 || and1_out)); endproperty
assert property (SyncSafeeotid);

endmodule