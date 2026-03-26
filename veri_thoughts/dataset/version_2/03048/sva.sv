module rs232in_sva (
    input logic        clock,
    input logic        serial_in,
    input logic        attention,
    input logic [7:0]  received_data,
    input logic [16:0] ttyclk,
    input logic [31:0] ttyclk_bit,
    input logic [31:0] ttyclk_start,
    input logic [7:0]  shift_in,
    input logic [4:0]  count,
    input logic        rxd,
    input logic        rxd2
);

    // The two-stage input synchronizer shifts serial_in through rxd and rxd2.
    check_input_synchronizer: assert property (
        @(posedge clock)
        1'b1 |=> (rxd == $past(serial_in)) &&
                 (rxd2 == $past(rxd))
    );

    // While the timer is active, only ttyclk decrements and attention stays low.
    check_ttyclk_countdown: assert property (
        @(posedge clock)
        (!ttyclk[16]) |=> (ttyclk == ($past(ttyclk) - 17'd1)) &&
                          (count == $past(count)) &&
                          (shift_in == $past(shift_in)) &&
                          (received_data == $past(received_data)) &&
                          !attention
    );

    // On each non-final sample, the shift register captures rxd2 and count decrements.
    check_bit_sample_nonfinal: assert property (
        @(posedge clock)
        (ttyclk[16] && (count > 5'd1)) |=> (ttyclk == $past(ttyclk_bit[16:0])) &&
                                           (count == ($past(count) - 5'd1)) &&
                                           (shift_in == {$past(rxd2), $past(shift_in[7:1])}) &&
                                           (received_data == $past(received_data)) &&
                                           !attention
    );

    // On the final sample, the last shifted byte is presented and attention is asserted.
    check_bit_sample_final: assert property (
        @(posedge clock)
        (ttyclk[16] && (count == 5'd1)) |=> (ttyclk == $past(ttyclk_bit[16:0])) &&
                                            (count == 5'd0) &&
                                            (shift_in == {$past(rxd2), $past(shift_in[7:1])}) &&
                                            (received_data == {$past(rxd2), $past(shift_in[7:1])}) &&
                                            attention
    );

    // A low rxd2 when idle starts a new receive window and loads count with 8.
    check_start_bit_detect: assert property (
        @(posedge clock)
        (ttyclk[16] && (count == 5'd0) && !rxd2) |=> (ttyclk == $past(ttyclk_start[16:0])) &&
                                                    (count == 5'd8) &&
                                                    (shift_in == $past(shift_in)) &&
                                                    (received_data == $past(received_data)) &&
                                                    !attention
    );

    // When idle and no start bit is seen, the receiver state holds and attention stays low.
    check_idle_hold: assert property (
        @(posedge clock)
        (ttyclk[16] && (count == 5'd0) && rxd2) |=> (ttyclk == $past(ttyclk)) &&
                                                   (count == $past(count)) &&
                                                   (shift_in == $past(shift_in)) &&
                                                   (received_data == $past(received_data)) &&
                                                   !attention
    );

    // Attention is asserted exactly when the prior cycle sampled the final bit.
    check_attention_update: assert property (
        @(posedge clock)
        1'b1 |=> (attention == ($past(ttyclk[16]) && ($past(count) == 5'd1)))
    );

    // received_data changes only on the final bit sample and otherwise holds its value.
    check_received_data_update: assert property (
        @(posedge clock)
        1'b1 |=> (($past(ttyclk[16]) && ($past(count) == 5'd1)) ?
                  (received_data == {$past(rxd2), $past(shift_in[7:1])}) :
                  (received_data == $past(received_data)))
    );

endmodule