module gatedcap_sva (
    input  logic        ld,
    input  logic        clk,
    input  logic        rst,
    input  logic        vcap,
    input  logic [31:0] count,
    input  logic [31:0] discharge_count,
    input  logic [31:0] charge_count,
    input  logic        charging,
    input  logic        discharging
);

    // A reset cycle leaves all state cleared on the following sampled cycle.
    check_reset_clears_state: assert property (
        @(posedge clk) disable iff (rst)
        $past(rst) |-> (vcap == 1'b0) &&
                       (count == 32'd0) &&
                       (discharge_count == 32'd0) &&
                       (charge_count == 32'd0) &&
                       (charging == 1'b0) &&
                       (discharging == 1'b0)
    );

    // While charging below the terminal count, only count increments.
    check_charging_increments_count: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) &&
        ($past(charging) == 1'b1) &&
        ($past(count) != 32'd499999)
        |-> (count == ($past(count) + 32'd1)) &&
            (charging == 1'b1) &&
            (discharging === $past(discharging)) &&
            (vcap === $past(vcap)) &&
            (discharge_count === $past(discharge_count)) &&
            (charge_count === $past(charge_count))
    );

    // Hitting the charging terminal count switches into discharging.
    check_charging_enters_discharging: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) &&
        ($past(charging) == 1'b1) &&
        ($past(count) == 32'd499999)
        |-> (count == 32'd0) &&
            (charging == 1'b0) &&
            (discharging == 1'b1) &&
            (vcap === $past(vcap)) &&
            (discharge_count === $past(discharge_count)) &&
            (charge_count === $past(charge_count))
    );

    // Discharging with zero vcap clears the machine back to idle.
    check_discharging_stops_at_zero_vcap: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) &&
        ($past(charging) == 1'b0) &&
        ($past(discharging) == 1'b1) &&
        ($past(vcap) == 1'b0)
        |-> (vcap == 1'b0) &&
            (count == 32'd0) &&
            (discharge_count == 32'd0) &&
            (charge_count == 32'd0) &&
            (charging == 1'b0) &&
            (discharging == 1'b0)
    );

    // While discharging between vcap steps, discharge_count increments.
    check_discharging_increments_discharge_count: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) &&
        ($past(charging) == 1'b0) &&
        ($past(discharging) == 1'b1) &&
        ($past(vcap) != 1'b0) &&
        ($past(discharge_count) != 32'd49999)
        |-> (discharge_count == ($past(discharge_count) + 32'd1)) &&
            (vcap === $past(vcap)) &&
            (count === $past(count)) &&
            (charge_count === $past(charge_count)) &&
            (charging == 1'b0) &&
            (discharging == 1'b1)
    );

    // Reaching the discharge interval resets discharge_count and drops vcap.
    check_discharging_decrements_vcap: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) &&
        ($past(charging) == 1'b0) &&
        ($past(discharging) == 1'b1) &&
        ($past(vcap) != 1'b0) &&
        ($past(discharge_count) == 32'd49999)
        |-> (discharge_count == 32'd0) &&
            (vcap == 1'b0) &&
            (count === $past(count)) &&
            (charge_count === $past(charge_count)) &&
            (charging == 1'b0) &&
            (discharging == 1'b1)
    );

    // An ld request from idle clears state and starts charging.
    check_idle_ld_starts_charging: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) &&
        ($past(charging) == 1'b0) &&
        ($past(discharging) == 1'b0) &&
        ($past(ld) == 1'b1)
        |-> (vcap == 1'b0) &&
            (count == 32'd0) &&
            (discharge_count == 32'd0) &&
            (charge_count == 32'd0) &&
            (charging == 1'b1) &&
            (discharging == 1'b0)
    );

    // Idle with no ld request leaves all state unchanged.
    check_idle_without_ld_holds_state: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) &&
        ($past(charging) == 1'b0) &&
        ($past(discharging) == 1'b0) &&
        ($past(ld) == 1'b0)
        |-> (vcap === $past(vcap)) &&
            (count === $past(count)) &&
            (discharge_count === $past(discharge_count)) &&
            (charge_count === $past(charge_count)) &&
            (charging == 1'b0) &&
            (discharging == 1'b0)
    );

endmodule