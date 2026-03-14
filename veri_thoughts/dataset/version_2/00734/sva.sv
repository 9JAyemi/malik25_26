module counter_sva (
    input logic rst,
    input logic en,
    input logic clk,
    input logic [3:0] count
);

    ///// Reset behavior /////
    // When reset is asserted LOW, count is forced to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) (rst == 1'b0) |-> (count == 4'b0000)
    );

    ///// Enable-controlled counting /////
    // When enable is LOW, hold the previous count (outside reset).
    check_hold_when_en_low: assert property (
        @(posedge clk) disable iff (!rst) (en == 1'b0) |-> (count == $past(count))
    );

    // When enable is HIGH and previous count != 15, increment by 1.
    check_increment_when_en_high_no_wrap: assert property (
        @(posedge clk) disable iff (!rst) (en == 1'b1) && ($past(count) != 4'hF) |-> (count == ($past(count) + 4'd1))
    );

    // When enable is HIGH and previous count == 15, wrap to 0.
    check_increment_when_en_high_wrap: assert property (
        @(posedge clk) disable iff (!rst) (en == 1'b1) && ($past(count) == 4'hF) |-> (count == 4'h0)
    );

    // Any change in count (outside reset) implies enable is HIGH that cycle.
    check_change_implies_en_high: assert property (
        @(posedge clk) disable iff (!rst) (count != $past(count)) |-> (en == 1'b1)
    );

    // When enable is HIGH (outside reset), count must change every cycle.
    check_must_change_when_en_high: assert property (
        @(posedge clk) disable iff (!rst) (en == 1'b1) |-> (count != $past(count))
    );

    // If enable is HIGH and count is 0 (outside reset), previous count was 15 (wrap origin).
    check_wrap_only_from_max: assert property (
        @(posedge clk) disable iff (!rst) (en == 1'b1) && (count == 4'h0) |-> ($past(count) == 4'hF)
    );

endmodule