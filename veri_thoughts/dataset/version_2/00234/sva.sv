module absolute_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic ld,
    input logic signed [31:0] in,
    input logic [3:0] load_data,
    input logic [35:0] out
);

    // After a reset cycle, the counter contribution is cleared.
    check_reset_clears_counter: assert property (
        @(posedge clk)
        rst |=> (out == {4'b0000, ((in < 32'sd0) ? -in : in)})
    );

    // The output is always the absolute input plus a 4-bit counter value.
    check_counter_contribution_range: assert property (
        @(posedge clk) disable iff (rst)
        (out >= {4'b0000, ((in < 32'sd0) ? -in : in)}) &&
        ((out - {4'b0000, ((in < 32'sd0) ? -in : in)}) <= 36'd15)
    );

    // When en is high, the counter increments modulo 16 on the next cycle.
    check_enable_increments_counter: assert property (
        @(posedge clk) disable iff (rst)
        en |=> ((out - {4'b0000, ((in < 32'sd0) ? -in : in)}) ==
                (($past(out - {4'b0000, ((in < 32'sd0) ? -in : in)}) + 36'd1) & 36'hF))
    );

    // When ld is high and en is low, the next counter value comes from load_data.
    check_load_updates_counter: assert property (
        @(posedge clk) disable iff (rst)
        (!en && ld) |=> (out == ({4'b0000, ((in < 32'sd0) ? -in : in)} + {32'b0, $past(load_data)}))
    );

    // When neither en nor ld is high, the counter value holds.
    check_hold_preserves_counter: assert property (
        @(posedge clk) disable iff (rst)
        (!en && !ld) |=> ((out - {4'b0000, ((in < 32'sd0) ? -in : in)}) ==
                          $past(out - {4'b0000, ((in < 32'sd0) ? -in : in)}))
    );

endmodule