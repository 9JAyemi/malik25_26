module binary_counter_sva (
    input logic clk,
    input logic EN,
    input logic RST,
    input logic [3:0] COUNT
);

// Reset low forces COUNT to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !RST |-> (COUNT == 4'b0000)
    );

// When enabled, COUNT increments by one on the next clock.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (!RST)
        EN |=> (COUNT == ($past(COUNT) + 4'd1))
    );

// When disabled, COUNT holds its previous value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!RST)
        !EN |=> (COUNT == $past(COUNT))
    );

// COUNT wraps from 15 back to 0 when enabled.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!RST)
        (EN && (COUNT == 4'hF)) |=> (COUNT == 4'h0)
    );

endmodule
