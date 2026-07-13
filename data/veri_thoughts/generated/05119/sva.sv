module oh_iddr_sva #(parameter DW = 1) (
    input logic              clk,
    input logic              ce0,
    input logic              ce1,
    input logic [DW/2-1:0]   din,
    input logic [DW-1:0]     dout,
    input logic [DW/2-1:0]   din_sl,
    input logic [DW/2-1:0]   din_sh,
    input logic              ce0_negedge
);

    typedef logic [DW-1:0] dout_t;

    // clk is the only clock; there is no reset in this RTL.
    // ce0_negedge is the prior posedge copy of ce0.
    check_ce0_negedge_pipeline: assert property (
        @(posedge clk)
        ($past(1'b1) === 1'b1) |-> (ce0_negedge === $past(ce0))
    );

    // din_sl captures din on a posedge when ce0 was asserted.
    check_din_sl_capture: assert property (
        @(posedge clk)
        (($past(1'b1) === 1'b1) && ($past(ce0) === 1'b1)) |-> (din_sl === $past(din))
    );

    // din_sl holds when ce0 was not asserted.
    check_din_sl_hold: assert property (
        @(posedge clk)
        (($past(1'b1) === 1'b1) && ($past(ce0) !== 1'b1)) |-> (din_sl === $past(din_sl))
    );

    // din_sh captures din on a negedge when ce0_negedge was asserted.
    check_din_sh_capture: assert property (
        @(negedge clk)
        (($past(1'b1) === 1'b1) && ($past(ce0_negedge) === 1'b1)) |-> (din_sh === $past(din))
    );

    // din_sh holds when ce0_negedge was not asserted.
    check_din_sh_hold: assert property (
        @(negedge clk)
        (($past(1'b1) === 1'b1) && ($past(ce0_negedge) !== 1'b1)) |-> (din_sh === $past(din_sh))
    );

    // dout captures the concatenated sampled halves when ce1 was asserted.
    check_dout_capture: assert property (
        @(posedge clk)
        (($past(1'b1) === 1'b1) && ($past(ce1) === 1'b1)) |-> (dout === dout_t'({$past(din_sh), $past(din_sl)}))
    );

    // dout holds when ce1 was not asserted.
    check_dout_hold: assert property (
        @(posedge clk)
        (($past(1'b1) === 1'b1) && ($past(ce1) !== 1'b1)) |-> (dout === $past(dout))
    );

endmodule

bind oh_iddr oh_iddr_sva #(.DW(DW)) oh_iddr_sva_bind (
    .clk(clk),
    .ce0(ce0),
    .ce1(ce1),
    .din(din),
    .dout(dout),
    .din_sl(din_sl),
    .din_sh(din_sh),
    .ce0_negedge(ce0_negedge)
);