module cycle_counter_sva (
    input logic [2:0] cycle,
    input logic       clk,
    input logic       enn
);

    // Clock: clk. No reset is present in the RTL.
    // Mixed logic: registered modulo-8 counter with combinational output cycle.

    // enn high synchronously clears the counter to zero.
    check_clear_on_enn: assert property (
        @(posedge clk) enn |=> cycle == 3'b000
    );

    // With enn low and no rollover, the counter increments by one.
    check_increment_when_enn_low: assert property (
        @(posedge clk) (!enn && cycle != 3'b111) |=> cycle == ($past(cycle) + 3'b001)
    );

    // With enn low at the maximum value, the counter wraps to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) (!enn && cycle == 3'b111) |=> cycle == 3'b000
    );

    // Eight consecutive count cycles return to the starting value.
    check_full_modulo_cycle: assert property (
        @(posedge clk) (!enn)[*8] |=> cycle == $past(cycle, 8)
    );

    // A clear followed by one count cycle produces a value of one.
    check_clear_then_count: assert property (
        @(posedge clk) enn ##1 !enn |=> cycle == 3'b001
    );

endmodule