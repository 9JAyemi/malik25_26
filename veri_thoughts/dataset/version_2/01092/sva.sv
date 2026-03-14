module RNG_sva #(
    parameter int w = 8
)(
    input  logic             clk,
    input  logic             rst,       // active-high asynchronous reset in RTL
    input  logic [w-1:0]     rand_num
);

    ///// Reset behavior /////
    // When reset is asserted at the clock edge, rand_num must be all zeros.
    check_reset_clears_rand: assert property (
        @(posedge clk) rst |-> (rand_num == {w{1'b0}})
    );

    // While reset stays asserted across clock edges, rand_num remains zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) (rst && $past(rst)) |-> $stable(rand_num)
    );

    ///// Next-state transform (clocked LFSR update as coded) /////
    // After a non-reset cycle, MSB is forced to 0 due to width extension on assignment.
    check_msb_zero_next: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (rand_num[w-1] == 1'b0)
    );

    // After a non-reset cycle, lower bits shift down by one (new [w-3:0] = old [w-2:1]).
    if (w >= 3) begin : gen_shift_vector
        check_lowbits_shift_next: assert property (
            @(posedge clk) disable iff (rst)
                $past(!rst) |-> (rand_num[w-3:0] == $past(rand_num[w-2:1]))
        );
    end

    // After a non-reset cycle, bit [w-2] equals XOR of prior [3:0] taps.
    if (w >= 4) begin : gen_feedback_tap
        check_feedback_bit_next: assert property (
            @(posedge clk) disable iff (rst)
                $past(!rst) |-> (rand_num[w-2] == ($past(rand_num[0]) ^ $past(rand_num[1]) ^ $past(rand_num[2]) ^ $past(rand_num[3])))
        );
    end

    // Once rand_num is zero in a non-reset cycle, it stays zero on the next cycle.
    check_zero_absorbing: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && ($past(rand_num) == {w{1'b0}}) |-> (rand_num == {w{1'b0}})
    );

endmodule