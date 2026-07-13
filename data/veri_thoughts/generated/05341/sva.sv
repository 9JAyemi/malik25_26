module syncflop_sva (
    input logic DEST_CLK,
    input logic D_SET,
    input logic D_RST,
    input logic RESET,
    input logic TOGGLE_IN,
    input logic D_OUT,
    input logic sync1,
    input logic sync2,
    input logic syncprev,
    input logic srflop,
    input logic syncxor,
    input logic srinput
);

    // syncxor is the XOR of the last two synchronizer stages.
    check_syncxor_definition: assert property (
        @(posedge DEST_CLK) disable iff (RESET)
        syncxor == (sync2 ^ syncprev)
    );

    // srinput is asserted by either D_SET or a syncxor pulse.
    check_srinput_definition: assert property (
        @(posedge DEST_CLK) disable iff (RESET)
        srinput == (syncxor | D_SET)
    );

    // D_OUT is the OR of srflop and syncxor.
    check_d_out_definition: assert property (
        @(posedge DEST_CLK) disable iff (RESET)
        D_OUT == (srflop | syncxor)
    );

    // A sampled reset leaves all sequential state cleared on the next clock sample.
    check_reset_release_clears_state: assert property (
        @(posedge DEST_CLK) disable iff (RESET)
        (!$initstate && $past(RESET)) |-> (!sync1 && !sync2 && !syncprev && !srflop)
    );

    // A sampled reset also leaves the pulse path and output low on the next clock sample.
    check_reset_release_clears_output: assert property (
        @(posedge DEST_CLK) disable iff (RESET)
        (!$initstate && $past(RESET)) |-> (!syncxor && !D_OUT)
    );

    // D_RST clears srflop by the next clock sample.
    check_d_rst_clears_srflop: assert property (
        @(posedge DEST_CLK) disable iff (RESET)
        D_RST |=> !srflop
    );

    // After D_RST, the output can only reflect the current syncxor pulse.
    check_d_rst_removes_latched_output: assert property (
        @(posedge DEST_CLK) disable iff (RESET)
        D_RST |=> (D_OUT == syncxor)
    );

endmodule