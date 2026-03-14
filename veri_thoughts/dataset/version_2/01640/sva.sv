module up_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count_out
);

    // On the first cycle after reset deasserts, count_out is 0.
    check_reset_release_zero: assert property (
        @(posedge clk) disable iff (rst)
        $past(rst) && !rst |-> (count_out == 4'd0)
    );

    // When not in reset for two consecutive cycles, count_out increments by 1.
    check_increment_no_reset: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && !rst |-> (count_out == $past(count_out) + 4'd1)
    );

    // Without reset, wrap from 0xF to 0x0 on the next cycle.
    check_wrap_from_f_to_0: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && !rst && ($past(count_out) == 4'hF) |-> (count_out == 4'h0)
    );

    // LSB toggles every non-reset cycle.
    check_lsb_toggles: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && !rst |-> (count_out[0] == ~$past(count_out[0]))
    );

    // Bit1 toggles when there is a carry from bit0.
    check_bit1_toggle_on_carry: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && !rst && $past(count_out[0]) |-> (count_out[1] == ~$past(count_out[1]))
    );

    // Bit1 holds when there is no carry from bit0.
    check_bit1_stable_no_carry: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && !rst && !$past(count_out[0]) |-> (count_out[1] == $past(count_out[1]))
    );

    // Bit2 toggles when there is a carry from bits[1:0].
    check_bit2_toggle_on_carry: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && !rst && ($past(count_out[1:0]) == 2'b11) |-> (count_out[2] == ~$past(count_out[2]))
    );

    // Bit2 holds when there is no carry from bits[1:0].
    check_bit2_stable_no_carry: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && !rst && ($past(count_out[1:0]) != 2'b11) |-> (count_out[2] == $past(count_out[2]))
    );

    // Bit3 toggles when there is a carry from bits[2:0].
    check_bit3_toggle_on_carry: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && !rst && ($past(count_out[2:0]) == 3'b111) |-> (count_out[3] == ~$past(count_out[3]))
    );

    // Bit3 holds when there is no carry from bits[2:0].
    check_bit3_stable_no_carry: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && !rst && ($past(count_out[2:0]) != 3'b111) |-> (count_out[3] == $past(count_out[3]))
    );

endmodule