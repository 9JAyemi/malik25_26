module EHRU_1_sva #(
    parameter DATA_SZ = 1
)(
    input logic                CLK,
    input logic [DATA_SZ-1:0]  read_0,
    input logic [DATA_SZ-1:0]  write_0,
    input logic                EN_write_0
);
    // Next-cycle read_0 equals prior cycle's mux of (EN_write_0 ? write_0 : read_0).
    check_next_value_function: assert property (
        @(posedge CLK) 1'b1 |=> (read_0 == ($past(EN_write_0) ? $past(write_0) : $past(read_0)))
    );

    // When enable is 1, read_0 loads write_0 on the next cycle.
    check_load_on_enable: assert property (
        @(posedge CLK) EN_write_0 |=> (read_0 == $past(write_0))
    );

    // When enable is 0, read_0 holds its value on the next cycle.
    check_hold_on_disable: assert property (
        @(posedge CLK) !EN_write_0 |=> (read_0 == $past(read_0))
    );

    // Any change in read_0 implies enable was 1 in the prior cycle.
    check_change_implies_enable: assert property (
        @(posedge CLK) 1'b1 |=> ($changed(read_0) |-> $past(EN_write_0))
    );

    // If read_0 changes, the new value equals the prior cycle's write_0.
    check_change_matches_prev_write: assert property (
        @(posedge CLK) 1'b1 |=> ($changed(read_0) |-> (read_0 == $past(write_0)))
    );

    // If enable was 1 and read_0 did not change, prior write_0 equaled prior read_0.
    check_no_change_when_loading_same_data: assert property (
        @(posedge CLK) 1'b1 |=> ( $past(EN_write_0) && !$changed(read_0) |-> ($past(write_0) == $past(read_0)) )
    );

    // If enable is 0 for two consecutive cycles, read_0 remains unchanged across them.
    check_hold_two_cycles: assert property (
        @(posedge CLK) (!EN_write_0 && $past(!EN_write_0)) |=> (read_0 == $past(read_0))
    );
endmodule