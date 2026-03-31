module binary_counter_sva (
    input logic clk,
    input logic EN,
    input logic RST,
    input logic [3:0] COUNT
);

    // Active-low reset forces COUNT to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !RST |-> (COUNT == 4'b0000)
    );

    // When enabled outside reset, COUNT increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (!RST) EN |-> (COUNT == ($past(COUNT) + 4'd1))
    );

    // When disabled outside reset, COUNT holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!RST) !EN |-> (COUNT == $past(COUNT))
    );

    // COUNT can only change when enabled outside reset.
    check_change_requires_enable: assert property (
        @(posedge clk) disable iff (!RST) (COUNT != $past(COUNT)) |-> EN
    );

    // COUNT wraps from 15 back to 0 when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!RST) (EN && (COUNT == 4'hF)) |-> (COUNT == 4'h0)
    );

endmodule