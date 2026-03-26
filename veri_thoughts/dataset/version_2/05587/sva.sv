module lfsr_sva (
    input logic        Clk,
    input logic        Reset,
    input logic [15:0] Seed,
    input logic        Enable,
    input logic [15:0] Data,
    input logic        Done,
    input logic [15:0] Lfsr
);

    // Reset clears all registered state.
    check_reset_clears_state: assert property (
        @(posedge Clk) Reset |-> ((Lfsr == 16'h0000) && (Data == 16'h0000) && (Done == 1'b0))
    );

    // Enable drives Done high on the next cycle.
    check_enable_sets_done: assert property (
        @(posedge Clk) disable iff (Reset)
        Enable |=> (Done == 1'b1)
    );

    // Disable drives Done low on the next cycle.
    check_disable_clears_done: assert property (
        @(posedge Clk) disable iff (Reset)
        !Enable |=> (Done == 1'b0)
    );

    // Data holds its value when Enable is low.
    check_disable_holds_data: assert property (
        @(posedge Clk) disable iff (Reset)
        !Enable |=> $stable(Data)
    );

    // Lfsr holds its value when Enable is low.
    check_disable_holds_lfsr: assert property (
        @(posedge Clk) disable iff (Reset)
        !Enable |=> $stable(Lfsr)
    );

    // Data captures the previous Lfsr value when enabled.
    check_enable_captures_lfsr_into_data: assert property (
        @(posedge Clk) disable iff (Reset)
        Enable |=> (Data == $past(Lfsr))
    );

    // Lfsr updates with the implemented feedback taps when enabled.
    check_enable_updates_lfsr: assert property (
        @(posedge Clk) disable iff (Reset)
        Enable |=> (Lfsr == { $past(Lfsr[14:0]), $past(Lfsr[0] ^ Lfsr[2] ^ Lfsr[3] ^ Lfsr[5]) })
    );

endmodule