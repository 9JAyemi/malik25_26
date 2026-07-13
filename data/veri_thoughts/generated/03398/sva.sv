module pipeline_2_latch_sva(
    input logic clk,
    input logic [31:0] abusWire1,
    input logic [31:0] bbusWire1,
    input logic [31:0] DselectWire1,
    input logic [31:0] immWire1,
    input logic [2:0] SWire1,
    input logic CinWire1,
    input logic immBit1,
    input logic [31:0] abusWire2,
    input logic [31:0] bbusWire2,
    input logic [31:0] immWire2,
    input logic [2:0] SWire2,
    input logic CinWire2,
    input logic [31:0] DselectWire2,
    input logic immBit2
);

    // abusWire2 captures abusWire1 from the prior clock.
    check_abus_transfer: assert property (
        @(posedge clk) 1'b1 |=> (abusWire2 == $past(abusWire1))
    );

    // bbusWire2 captures bbusWire1 from the prior clock.
    check_bbus_transfer: assert property (
        @(posedge clk) 1'b1 |=> (bbusWire2 == $past(bbusWire1))
    );

    // DselectWire2 captures DselectWire1 from the prior clock.
    check_dselect_transfer: assert property (
        @(posedge clk) 1'b1 |=> (DselectWire2 == $past(DselectWire1))
    );

    // immWire2 captures immWire1 from the prior clock.
    check_imm_transfer: assert property (
        @(posedge clk) 1'b1 |=> (immWire2 == $past(immWire1))
    );

    // SWire2 captures SWire1 from the prior clock.
    check_s_transfer: assert property (
        @(posedge clk) 1'b1 |=> (SWire2 == $past(SWire1))
    );

    // CinWire2 captures CinWire1 from the prior clock.
    check_cin_transfer: assert property (
        @(posedge clk) 1'b1 |=> (CinWire2 == $past(CinWire1))
    );

    // immBit2 captures immBit1 from the prior clock.
    check_immbit_transfer: assert property (
        @(posedge clk) 1'b1 |=> (immBit2 == $past(immBit1))
    );

endmodule