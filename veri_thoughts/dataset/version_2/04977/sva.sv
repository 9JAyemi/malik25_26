module signal_converter_sva (
    input logic clk,
    input logic [1:0] Y,
    input logic VOUT,
    input logic VREF,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y ignores A1/A2 and matches the B inputs.
    check_y_matches_b_inputs: assert property (
        @(posedge clk) Y == {B1, B2}
    );

    // VOUT selects VPWR for even Y and VGND for odd Y.
    check_vout_follows_y_lsb: assert property (
        @(posedge clk) VOUT == (Y[0] ? VGND : VPWR)
    );

    // VREF selects VPB for Y below 2 and VNB otherwise.
    check_vref_follows_y_msb: assert property (
        @(posedge clk) VREF == (Y[1] ? VNB : VPB)
    );

    // VOUT is ultimately controlled by B2 through Y.
    check_vout_matches_b2: assert property (
        @(posedge clk) VOUT == (B2 ? VGND : VPWR)
    );

    // VREF is ultimately controlled by B1 through Y.
    check_vref_matches_b1: assert property (
        @(posedge clk) VREF == (B1 ? VNB : VPB)
    );

endmodule