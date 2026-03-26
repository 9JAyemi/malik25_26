module control_sva (
    input logic         clk,
    input logic         rst,
    input logic [143:0] flit0c,
    input logic [143:0] flit1c,
    input logic [143:0] flitl0,
    input logic [143:0] flitl1,
    input logic         port0_co,
    input logic         port1_co,
    input logic         portl0_co,
    input logic         portl1_co,
    input logic         ack0,
    input logic         ack1
);

    // A reset cycle clears all registered outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(rst) |-> ((port0_co  === 1'b0) &&
                        (port1_co  === 1'b0) &&
                        (portl0_co === 1'b0) &&
                        (portl1_co === 1'b0) &&
                        (ack0      === 1'b0) &&
                        (ack1      === 1'b0))
    );

    // port0_co stores flit0c[0], or 0 after reset.
    check_port0_co_update: assert property (
        @(posedge clk) disable iff ($initstate)
        port0_co === ($past(rst) ? 1'b0 : $past(flit0c[0]))
    );

    // port1_co stores flit1c[0], or 0 after reset.
    check_port1_co_update: assert property (
        @(posedge clk) disable iff ($initstate)
        port1_co === ($past(rst) ? 1'b0 : $past(flit1c[0]))
    );

    // portl0_co stores flitl0[0], or 0 after reset.
    check_portl0_co_update: assert property (
        @(posedge clk) disable iff ($initstate)
        portl0_co === ($past(rst) ? 1'b0 : $past(flitl0[0]))
    );

    // portl1_co stores flitl1[0], or 0 after reset.
    check_portl1_co_update: assert property (
        @(posedge clk) disable iff ($initstate)
        portl1_co === ($past(rst) ? 1'b0 : $past(flitl1[0]))
    );

    // ack0 reflects whether flitl0 was nonzero, or 0 after reset.
    check_ack0_update: assert property (
        @(posedge clk) disable iff ($initstate)
        ack0 === ($past(rst) ? 1'b0 : ($past(flitl0) != 144'b0))
    );

    // ack1 reflects whether flitl1 was nonzero, or 0 after reset.
    check_ack1_update: assert property (
        @(posedge clk) disable iff ($initstate)
        ack1 === ($past(rst) ? 1'b0 : ($past(flitl1) != 144'b0))
    );

endmodule