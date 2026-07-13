module top_module_sva (
    input logic clk,
    input logic reset,          // synchronous active-high
    input logic [3:0] signed_mag,
    input logic select,
    input logic [7:0] q
);

// Reset clears q on the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 8'h00)
    );

// With select=0, q equals zero-extended signed_mag.
    check_select0_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (!select) |=> (q == {4'h0, $signed(signed_mag)})
    );

// With select=1, q equals zero-extended counter value.
    check_select1_counter: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (q == {4'h0, $past(counter_out)})
    );

// With select=0 and signed_mag[3]==0, q equals zero-extended signed_mag.
    check_select0_mag_positive: assert property (
        @(posedge clk) disable iff (reset)
        (!select && !signed_mag[3]) |=> (q == {4'h0, $signed(signed_mag)})
    );

// With select=0 and signed_mag[3]==1, q equals zero-extended two's complement.
    check_select0_mag_negative: assert property (
        @(posedge clk) disable iff (reset)
        (!select && signed_mag[3]) |=> (q == {4'h0, $signed(~(signed_mag - 4'd1))})
    );

// With select=1, q[3:0] increments by one each cycle.
    check_select1_counter_increment: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (q[3:0] == ($past(q[3:0]) + 4'd1))
    );

// With select=0 and signed_mag[3]==0, q[3:0] equals signed_mag.
    check_select0_mag_positive_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (!select && !signed_mag[3]) |=> (q[3:0] == $signed(signed_mag))
    );

// With select=0 and signed_mag[3]==1, q[3:0] equals two's complement of signed_mag.
    check_select0_mag_negative_twos_comp: assert property (
        @(posedge clk) disable iff (reset)
        (!select && signed_mag[3]) |=> (q[3:0] == $signed(~(signed_mag - 4'd1)))
    );

endmodule
