module top_module_sva (
    input logic t,
    input logic clk,
    input logic [1:0] out
);
    // Clock: clk (posedge). Reset: none. Logic: sequential TFFs + combinational mapping (out mirrors flip_flop).
    // Key next-state: out[0]' = $past(out[0]) ^ t; out[1]' = $past(out[1]) ^ $past(out[0]).

    // LSB updates with XOR of prior LSB and current t.
    check_lsb_updates_with_t: assert property (
        @(posedge clk) out[0] == ($past(out[0]) ^ t)
    );

    // MSB toggles iff prior LSB was 1.
    check_msb_updates_with_prev_lsb: assert property (
        @(posedge clk) out[1] == ($past(out[1]) ^ $past(out[0]))
    );

    // Out0 does not toggle when t is 0.
    check_out0_stable_when_t0: assert property (
        @(posedge clk) (!t) |-> (out[0] == $past(out[0]))
    );

    // Out0 toggles when t is 1.
    check_out0_toggle_when_t1: assert property (
        @(posedge clk) (t) |-> (out[0] != $past(out[0]))
    );

    // Out1 does not toggle when prior out0 was 0.
    check_out1_stable_when_prev_lsb0: assert property (
        @(posedge clk) ($past(out[0]) == 1'b0) |-> (out[1] == $past(out[1]))
    );

    // Out1 toggles when prior out0 was 1.
    check_out1_toggle_when_prev_lsb1: assert property (
        @(posedge clk) ($past(out[0]) == 1'b1) |-> (out[1] != $past(out[1]))
    );

    // With t==0 and prior state 00, stay at 00.
    check_t0_transition_00: assert property (
        @(posedge clk) (!t && ($past(out) == 2'b00)) |-> (out == 2'b00)
    );

    // With t==0 and prior state 01, go to 11.
    check_t0_transition_01: assert property (
        @(posedge clk) (!t && ($past(out) == 2'b01)) |-> (out == 2'b11)
    );

    // With t==0 and prior state 10, stay at 10.
    check_t0_transition_10: assert property (
        @(posedge clk) (!t && ($past(out) == 2'b10)) |-> (out == 2'b10)
    );

    // With t==0 and prior state 11, go to 01.
    check_t0_transition_11: assert property (
        @(posedge clk) (!t && ($past(out) == 2'b11)) |-> (out == 2'b01)
    );

    // With t==1 and prior state 00, go to 01.
    check_t1_transition_00: assert property (
        @(posedge clk) (t && ($past(out) == 2'b00)) |-> (out == 2'b01)
    );

    // With t==1 and prior state 01, go to 10.
    check_t1_transition_01: assert property (
        @(posedge clk) (t && ($past(out) == 2'b01)) |-> (out == 2'b10)
    );

    // With t==1 and prior state 10, go to 11.
    check_t1_transition_10: assert property (
        @(posedge clk) (t && ($past(out) == 2'b10)) |-> (out == 2'b11)
    );

    // With t==1 and prior state 11, go to 00.
    check_t1_transition_11: assert property (
        @(posedge clk) (t && ($past(out) == 2'b11)) |-> (out == 2'b00)
    );

endmodule