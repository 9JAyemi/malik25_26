module counter_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic done,
    input logic [3:0] out
);
    // Reset drives out and done to zero.
    reset_forces_zero: assert property (
        @(posedge clk) rst |-> (out == 4'b0000) && (done == 1'b0)
    );

    // When enable is HIGH, done is driven LOW in the same cycle.
    done_low_when_enable: assert property (
        @(posedge clk) disable iff (rst) enable |-> (done == 1'b0)
    );

    // When enable is LOW, done is driven HIGH in the same cycle.
    done_high_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !enable |-> (done == 1'b1)
    );

    // A falling edge on done implies enable is HIGH in that cycle.
    done_fall_implies_enable: assert property (
        @(posedge clk) disable iff (rst) $fell(done) |-> (enable == 1'b1)
    );

    // A rising edge on done implies enable is LOW in that cycle.
    done_rise_implies_no_enable: assert property (
        @(posedge clk) disable iff (rst) $rose(done) |-> (enable == 1'b0)
    );

    // When enable is HIGH, next out increments by 1 modulo 16.
    out_increments_when_enable: assert property (
        @(posedge clk) disable iff (rst) enable |=> (out == ($past(out) + 4'd1)[3:0])
    );

    // When enable is LOW, next out holds its previous value.
    out_holds_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !enable |=> (out == $past(out))
    );

    // Any change in out implies enable was HIGH in the previous cycle.
    out_change_implies_prev_enable: assert property (
        @(posedge clk) disable iff (rst) (out != $past(out)) |-> $past(enable)
    );

    // Two consecutive enables add 2 to out modulo 16.
    two_enables_add_two: assert property (
        @(posedge clk) disable iff (rst) (enable ##1 enable) |=> (out == ($past(out,2) + 4'd2)[3:0])
    );

    // Two consecutive disables keep out unchanged across both cycles.
    two_disables_hold: assert property (
        @(posedge clk) disable iff (rst) (!enable ##1 !enable) |=> (out == $past(out,2))
    );
endmodule