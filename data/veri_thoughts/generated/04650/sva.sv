module ConstantSelection_sva (
    input logic clk,
    input logic SNnotDB,
    input logic DBnotSN,
    input logic [7:0] RomExpConCtl,
    input logic Constantb,
    input logic Constantc,
    input logic Constantd,
    input logic Constante,
    input logic Constantf,
    input logic Constantg,
    input logic Constanth
);

    // Constantb is always low because Func1 is contradictory.
    check_constantb_tied_low: assert property (
        @(posedge clk) Constantb == 1'b0
    );

    // Constantc is always low because Func1 is contradictory.
    check_constantc_tied_low: assert property (
        @(posedge clk) Constantc == 1'b0
    );

    // Constantd directly reflects Func1, which is always low.
    check_constantd_tied_low: assert property (
        @(posedge clk) Constantd == 1'b0
    );

    // Constante matches the Func0 and DBnotSN decode.
    check_constante_decode: assert property (
        @(posedge clk) Constante == (RomExpConCtl[0] & ~RomExpConCtl[1] & DBnotSN)
    );

    // Constantf matches the simplified Func0 decode.
    check_constantf_decode: assert property (
        @(posedge clk) Constantf == (RomExpConCtl[0] & ~RomExpConCtl[1])
    );

    // Constantg matches the Func0 and SNnotDB decode.
    check_constantg_decode: assert property (
        @(posedge clk) Constantg == (RomExpConCtl[0] & ~RomExpConCtl[1] & SNnotDB)
    );

    // Constanth is the inversion of the Func0 and SNnotDB term.
    check_constanth_decode: assert property (
        @(posedge clk) Constanth == ~(RomExpConCtl[0] & ~RomExpConCtl[1] & SNnotDB)
    );

    // Constantg is the logical complement of Constanth.
    check_constantg_complements_constanth: assert property (
        @(posedge clk) Constantg == ~Constanth
    );

    // Constante can only be high when Constantf is high.
    check_constante_implies_constantf: assert property (
        @(posedge clk) Constante |-> Constantf
    );

    // Constantg can only be high when Constantf is high.
    check_constantg_implies_constantf: assert property (
        @(posedge clk) Constantg |-> Constantf
    );

endmodule