module shift_reg_sva (
    input logic CLK,
    input logic RST,
    input logic LD,
    input logic [3:0] D,
    input logic [3:0] OUT
);

    // Reset clears the register chain by the next clock.
    check_reset_clears_chain: assert property (
        @(posedge CLK) RST |=> (OUT == 4'b0000)
    );

    // Load captures D into the register chain on the next clock.
    check_load_captures_chain: assert property (
        @(posedge CLK) disable iff (RST)
        LD |=> (OUT == $past(D))
    );

    // Without load, the register chain shifts by one bit.
    check_shift_updates_chain: assert property (
        @(posedge CLK) disable iff (RST)
        !LD |=> (OUT == $past(OUT))
    );

    // Reset has priority over load when both are asserted.
    check_reset_priority_over_load: assert property (
        @(posedge CLK) RST && LD |=> (OUT == 4'b0000)
    );

    // Load has priority over shift when both are asserted without reset.
    check_load_priority_over_shift: assert property (
        @(posedge CLK) disable iff (RST)
        !RST && LD && !LD |=> (OUT == $past(D))
    );

endmodule