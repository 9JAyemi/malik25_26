module fpoint_qsys_addsub_single_altpriority_encoder_lha_sva (
    input logic [3:0] data,
    input logic [1:0] q
);
    // No clock/reset in RTL; purely combinational. Properties clocked on $global_clock.
    // Functional behavior: q[0]=data[0]?1:data[1]; q[1]=data[2]?1:data[3].

    // q[0] equals OR of data[1:0].
    check_q0_is_or_lower: assert property (
        @(posedge $global_clock) q[0] == (data[0] | data[1])
    );

    // q[1] equals OR of data[3:2].
    check_q1_is_or_upper: assert property (
        @(posedge $global_clock) q[1] == (data[2] | data[3])
    );

    // If data[0] is 1 then q[0] must be 1.
    check_q0_high_when_d0_high: assert property (
        @(posedge $global_clock) (data[0] == 1'b1) |-> (q[0] == 1'b1)
    );

    // If data[0] is 0 then q[0] equals data[1].
    check_q0_eq_d1_when_d0_low: assert property (
        @(posedge $global_clock) (data[0] == 1'b0) |-> (q[0] == data[1])
    );

    // If data[2] is 1 then q[1] must be 1.
    check_q1_high_when_d2_high: assert property (
        @(posedge $global_clock) (data[2] == 1'b1) |-> (q[1] == 1'b1)
    );

    // If data[2] is 0 then q[1] equals data[3].
    check_q1_eq_d3_when_d2_low: assert property (
        @(posedge $global_clock) (data[2] == 1'b0) |-> (q[1] == data[3])
    );

    // Lower pair 00 forces q[0] to 0.
    check_q0_zero_on_lower_zero: assert property (
        @(posedge $global_clock) (data[1:0] == 2'b00) |-> (q[0] == 1'b0)
    );

    // Upper pair 00 forces q[1] to 0.
    check_q1_zero_on_upper_zero: assert property (
        @(posedge $global_clock) (data[3:2] == 2'b00) |-> (q[1] == 1'b0)
    );

    // Changes in upper pair do not affect q[0] if lower pair is stable.
    check_q0_independent_of_upper: assert property (
        @(posedge $global_clock) ($changed(data[3:2]) && $stable(data[1:0])) |-> $stable(q[0])
    );

    // Changes in lower pair do not affect q[1] if upper pair is stable.
    check_q1_independent_of_lower: assert property (
        @(posedge $global_clock) ($changed(data[1:0]) && $stable(data[3:2])) |-> $stable(q[1])
    );

endmodule