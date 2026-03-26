module address_counter_sva #(
    parameter integer COUNT_WIDTH = 13
) (
    input  logic                    clken,
    input  logic                    trig,
    input  logic                    clk,
    input  logic [31:0]             address,
    input  logic [3:0]              wen,
    input  logic                    trig_reg,
    input  logic                    trig_detected,
    input  logic                    wen_reg,
    input  logic [COUNT_WIDTH-1:0]  count
);

    localparam logic [COUNT_WIDTH-1:0] count_max = {COUNT_WIDTH{1'b1}};

    // Initial state matches the RTL initial assignments.
    check_initial_state: assert property (
        @(posedge clk) $initstate |-> (count == '0) && !trig_detected && !wen_reg && (address == 32'd0) && (wen == 4'b0000)
    );

    // Address is the current count shifted left by two.
    check_address_from_count: assert property (
        @(posedge clk) address == 32'(count << 2)
    );

    // WEN is a 4-bit replication of wen_reg.
    check_wen_from_wen_reg: assert property (
        @(posedge clk) wen == {4{wen_reg}}
    );

    // trig_reg samples trig on every clock.
    check_trig_reg_tracks_trig: assert property (
        @(posedge clk) 1'b1 |=> (trig_reg == $past(trig))
    );

    // count holds when clken is not asserted.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) (clken !== 1'b1) |=> $stable(count)
    );

    // count increments by one when enabled below count_max.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) (clken === 1'b1) && (count !== count_max) |=> (count == ($past(count) + 1'b1))
    );

    // count wraps to zero when enabled at count_max.
    check_count_wraps_at_max: assert property (
        @(posedge clk) (clken === 1'b1) && (count === count_max) |=> (count == '0)
    );

    // trig_detected sets when a trig rising edge is detected.
    check_trig_detected_sets_on_rise: assert property (
        @(posedge clk) ((trig & ~trig_reg) === 1'b1) |=> trig_detected
    );

    // trig_detected clears at count_max when no new rise is detected.
    check_trig_detected_clears_at_max: assert property (
        @(posedge clk) ((trig & ~trig_reg) !== 1'b1) && (count === count_max) |=> !trig_detected
    );

    // trig_detected otherwise retains its prior value.
    check_trig_detected_holds_otherwise: assert property (
        @(posedge clk) ((trig & ~trig_reg) !== 1'b1) && (count !== count_max) |=> $stable(trig_detected)
    );

    // wen_reg captures trig_detected at count_max when enabled.
    check_wen_reg_captures_trig_detected: assert property (
        @(posedge clk) (clken === 1'b1) && (count === count_max) |=> (wen_reg == $past(trig_detected))
    );

    // wen_reg holds when the terminal-count update is not taken.
    check_wen_reg_holds_otherwise: assert property (
        @(posedge clk) (clken !== 1'b1 || count !== count_max) |=> $stable(wen_reg)
    );

endmodule