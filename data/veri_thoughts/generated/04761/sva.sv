module state_machine_sva (
    input logic        clk,
    input logic        rst,
    input logic        inp,
    input logic [31:0] outp,
    input logic [1:0]  state,
    input logic [31:0] count
);

    localparam logic [1:0] IDLE   = 2'b00;
    localparam logic [1:0] ACTIVE = 2'b01;

    // In ACTIVE, outp mirrors count.
    check_outp_matches_count_in_active: assert property (
        @(posedge clk) disable iff (rst)
        (state == ACTIVE) |-> (outp == count)
    );

    // Outside ACTIVE, outp is zero.
    check_outp_zero_when_not_active: assert property (
        @(posedge clk) disable iff (rst)
        (state != ACTIVE) |-> (outp == 32'd0)
    );

    // IDLE with inp high enters ACTIVE and clears count.
    check_idle_to_active_on_input: assert property (
        @(posedge clk) disable iff (rst)
        (state == IDLE && inp) |=> (state == ACTIVE && count == 32'd0)
    );

    // IDLE with inp low holds state and count.
    check_idle_holds_without_input: assert property (
        @(posedge clk) disable iff (rst)
        (state == IDLE && !inp) |=> (state == IDLE && count == $past(count))
    );

    // ACTIVE with inp high stays ACTIVE and increments count.
    check_active_increments_on_input: assert property (
        @(posedge clk) disable iff (rst)
        (state == ACTIVE && inp) |=> (state == ACTIVE && count == ($past(count) + 32'd1))
    );

    // ACTIVE with inp low returns to IDLE and holds count.
    check_active_to_idle_on_input_low: assert property (
        @(posedge clk) disable iff (rst)
        (state == ACTIVE && !inp) |=> (state == IDLE && count == $past(count))
    );

endmodule