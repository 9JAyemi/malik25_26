module counter_3bit_sva (
    input logic clk,
    input logic rst,    // active-high synchronous reset
    input logic en,
    input logic [2:0] count
);
    // Reset high causes count to be zero on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) rst |=> (count == 3'b000)
    );

    // If reset is held high across cycles, count is zero.
    reset_holds_zero: assert property (
        @(posedge clk) ($past(rst) && rst) |-> (count == 3'b000)
    );

    // With en=1 (and prior cycle out of reset), count increments by 1 next cycle.
    increment_on_en: assert property (
        @(posedge clk) disable iff (rst) (en && $past(!rst)) |=> (count == $past(count) + 3'b001)
    );

    // With en=0 (and prior cycle out of reset), count holds its value next cycle.
    hold_on_disable: assert property (
        @(posedge clk) disable iff (rst) (!en && $past(!rst)) |=> (count == $past(count))
    );

    // Any change in count (without reset) implies en was 1 in the previous cycle.
    change_implies_prev_en: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst) && (count != $past(count))) |-> $past(en)
    );

    // When en=1 and previous count was 7, next count wraps to 0.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (rst) (en && $past(!rst) && ($past(count) == 3'b111)) |=> (count == 3'b000)
    );

    // With en=1, LSB toggles each cycle.
    lsb_toggles_on_en: assert property (
        @(posedge clk) disable iff (rst) (en && $past(!rst)) |=> (count[0] != $past(count[0]))
    );

    // With en=1, bit1 equals prev(bit1) XOR prev(bit0).
    bit1_xor_carry_on_en: assert property (
        @(posedge clk) disable iff (rst) (en && $past(!rst)) |=> (count[1] == ($past(count[1]) ^ $past(count[0])))
    );

    // With en=1, bit2 equals prev(bit2) XOR (prev(bit1)&prev(bit0)).
    bit2_xor_carry_on_en: assert property (
        @(posedge clk) disable iff (rst) (en && $past(!rst)) |=> (count[2] == ($past(count[2]) ^ ($past(count[1]) & $past(count[0]))))
    );

    // Without reset, next count is either unchanged or incremented by 1.
    only_hold_or_inc: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> ((count == $past(count)) || (count == $past(count) + 3'b001))
    );
endmodule