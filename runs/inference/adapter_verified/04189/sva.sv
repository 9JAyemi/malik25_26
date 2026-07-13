module shift_reg_sva (
    input logic CLK,
    input logic RST,
    input logic LD,
    input logic [3:0] D,
    input logic [3:0] OUT
);

// Reset clears the entire 4-stage shift register.
    check_reset_clears_out: assert property (
        @(posedge CLK) RST |=> (OUT == 4'b0000)
    );

// Load captures D into the register on the next cycle.
    check_load_captures_d: assert property (
        @(posedge CLK) disable iff (RST) LD |=> (OUT == $past(D))
    );

// Without load, the register holds its value.
    check_hold_when_not_load: assert property (
        @(posedge CLK) disable iff (RST) !LD |=> (OUT == $past(OUT))
    );

// Load has priority over hold when both are asserted.
    check_load_priority_over_hold: assert property (
        @(posedge CLK) (RST || (LD && !RST)) |=> (OUT == ($past(RST) ? 4'b0000 : $past(LD) ? $past(D) : $past(OUT)))
    );

endmodule
