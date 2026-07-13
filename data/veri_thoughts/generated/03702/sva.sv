module counter_sva (
    input logic       CLK,
    input logic       RESET,
    input logic       LOAD,
    input logic [7:0] LOAD_DATA,
    input logic [7:0] COUNT
);

    // RESET clears COUNT on the next clock.
    check_reset_clears_count: assert property (
        @(posedge CLK) RESET |=> (COUNT == 8'h00)
    );

    // RESET overrides LOAD when both are asserted.
    check_reset_priority_over_load: assert property (
        @(posedge CLK) (RESET && LOAD) |=> (COUNT == 8'h00)
    );

    // LOAD copies LOAD_DATA into COUNT on the next clock.
    check_load_updates_count: assert property (
        @(posedge CLK) disable iff (RESET)
        LOAD |=> (COUNT == $past(LOAD_DATA))
    );

    // Without LOAD, COUNT increments by one on the next clock.
    check_increment_when_idle: assert property (
        @(posedge CLK) disable iff (RESET)
        !LOAD |=> (COUNT == ($past(COUNT) + 8'd1))
    );

    // After reset release with no load, counting restarts from zero.
    check_count_starts_after_reset: assert property (
        @(posedge CLK) (RESET ##1 (!RESET && !LOAD)) |=> (COUNT == 8'h01)
    );

    // A loaded value increments on the following idle cycle.
    check_increment_after_load: assert property (
        @(posedge CLK) disable iff (RESET)
        (LOAD ##1 (!LOAD)) |=> (COUNT == ($past(LOAD_DATA, 2) + 8'd1))
    );

endmodule