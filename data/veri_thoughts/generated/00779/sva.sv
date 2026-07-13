module TOP_sva (
    input logic in,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3,
    input logic out,
    input logic [1:0] counter,
    input logic [3:0] bits
);
    ///// Counter behavior /////
    // Counter increments by 1 (mod 4) each posedge of 'in'.
    check_counter_increments: assert property (
        @(posedge in) $past(1'b1) |-> (counter == $past(counter) + 2'd1)
    );

    ///// Bits array update /////
    // The bit indexed by previous cycle's counter (pre-increment) is updated to previous 'in' value.
    check_bits_write_value: assert property (
        @(posedge in) $past(1'b1) |-> (bits[($past(counter) - 2'd1)] == $past(in))
    );
    // bits[0] is unchanged if it was not the written index last cycle.
    check_bits0_stable_when_not_written: assert property (
        @(posedge in) ($past(1'b1) && (($past(counter) - 2'd1) != 2'd0)) |-> (bits[0] == $past(bits[0]))
    );
    // bits[1] is unchanged if it was not the written index last cycle.
    check_bits1_stable_when_not_written: assert property (
        @(posedge in) ($past(1'b1) && (($past(counter) - 2'd1) != 2'd1)) |-> (bits[1] == $past(bits[1]))
    );
    // bits[2] is unchanged if it was not the written index last cycle.
    check_bits2_stable_when_not_written: assert property (
        @(posedge in) ($past(1'b1) && (($past(counter) - 2'd1) != 2'd2)) |-> (bits[2] == $past(bits[2]))
    );
    // bits[3] is unchanged if it was not the written index last cycle.
    check_bits3_stable_when_not_written: assert property (
        @(posedge in) ($past(1'b1) && (($past(counter) - 2'd1) != 2'd3)) |-> (bits[3] == $past(bits[3]))
    );

    ///// Output registers /////
    // out0 captures bits[0] from the previous cycle.
    check_out0_follows_bits0: assert property (
        @(posedge in) $past(1'b1) |-> (out0 == $past(bits[0]))
    );
    // out1 captures bits[1] from the previous cycle.
    check_out1_follows_bits1: assert property (
        @(posedge in) $past(1'b1) |-> (out1 == $past(bits[1]))
    );
    // out2 captures bits[2] from the previous cycle.
    check_out2_follows_bits2: assert property (
        @(posedge in) $past(1'b1) |-> (out2 == $past(bits[2]))
    );
    // out3 captures bits[3] from the previous cycle.
    check_out3_follows_bits3: assert property (
        @(posedge in) $past(1'b1) |-> (out3 == $past(bits[3]))
    );
    // out captures the previous value of out0 (LSB of the concatenation).
    check_out_follows_prev_out0: assert property (
        @(posedge in) $past(1'b1) |-> (out == $past(out0))
    );
endmodule