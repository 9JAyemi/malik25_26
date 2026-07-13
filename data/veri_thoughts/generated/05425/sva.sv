module spi_slave_sva (
    input logic clk,
    input logic rst_n,
    input logic sck,
    input logic mosi,
    input logic ssel,
    input logic miso,
    input logic recived_status,
    input logic [2:0] sckr,
    input logic [2:0] sselr,
    input logic [1:0] mosir,
    input logic [2:0] bitcnt,
    input logic [7:0] bytecnt,
    input logic byte_received,
    input logic [7:0] byte_data_received,
    input logic [7:0] received_memory,
    input logic [7:0] byte_data_sent,
    input logic [7:0] cnt,
    input logic ssel_active,
    input logic sck_risingedge,
    input logic sck_fallingedge,
    input logic ssel_startmessage,
    input logic ssel_endmessage,
    input logic mosi_data
);

    // Reset drives all storage elements and outputs low.
    check_reset_state: assert property (
        @(posedge clk)
        !rst_n |-> (sckr == 3'h0) &&
                  (sselr == 3'h0) &&
                  (mosir == 2'h0) &&
                  (bitcnt == 3'b000) &&
                  (bytecnt == 8'h0) &&
                  (byte_received == 1'b0) &&
                  (byte_data_received == 8'h0) &&
                  (received_memory == 8'h0) &&
                  (byte_data_sent == 8'h0) &&
                  (cnt == 8'h0) &&
                  (recived_status == 1'b0) &&
                  (miso == 1'b0)
    );

    // sckr shifts in sck every clk.
    check_sckr_shift: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (sckr == {$past(sckr[1:0]), $past(sck)})
    );

    // sselr shifts in ssel every clk.
    check_sselr_shift: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (sselr == {$past(sselr[1:0]), $past(ssel)})
    );

    // mosir shifts in mosi every clk.
    check_mosir_shift: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (mosir == {$past(mosir[0]), $past(mosi)})
    );

    // sck_risingedge decodes 01 in sckr[2:1].
    check_sck_risingedge_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        (sck_risingedge == (sckr[2:1] == 2'b01))
    );

    // sck_fallingedge decodes 10 in sckr[2:1].
    check_sck_fallingedge_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        (sck_fallingedge == (sckr[2:1] == 2'b10))
    );

    // ssel_active is the inverted synchronized select.
    check_ssel_active_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ssel_active == ~sselr[1])
    );

    // ssel_startmessage decodes a falling ssel edge.
    check_ssel_startmessage_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ssel_startmessage == (sselr[2:1] == 2'b10))
    );

    // ssel_endmessage decodes a rising ssel edge.
    check_ssel_endmessage_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ssel_endmessage == (sselr[2:1] == 2'b01))
    );

    // mosi_data is the delayed MOSI sample.
    check_mosi_data_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mosi_data == mosir[1])
    );

    // bitcnt clears when inactive, increments on rising SCK, else holds.
    check_bitcnt_update: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (bitcnt == (!$past(ssel_active) ? 3'b000 :
                              ($past(sck_risingedge) ? ($past(bitcnt) + 3'b001) :
                                                       $past(bitcnt))))
    );

    // Receive shift register updates only on active rising SCK.
    check_byte_data_received_update: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (byte_data_received ==
                  (($past(ssel_active) && $past(sck_risingedge)) ?
                   {$past(byte_data_received[6:0]), $past(mosi_data)} :
                   $past(byte_data_received)))
    );

    // byte_received is the delayed pulse for bitcnt==7 on active rising SCK.
    check_byte_received_generation: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (byte_received ==
                  $past(ssel_active && sck_risingedge && (bitcnt == 3'b111)))
    );

    // bytecnt increments only when byte_received is high.
    check_bytecnt_update: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (bytecnt ==
                  ($past(byte_received) ? ($past(bytecnt) + 8'h1) :
                                          $past(bytecnt)))
    );

    // received_memory increments only for matching received bytes.
    check_received_memory_update: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (received_memory ==
                  (($past(byte_received) &&
                    ($past(byte_data_received) == $past(bytecnt))) ?
                   ($past(received_memory) + 8'h1) :
                   $past(received_memory)))
    );

    // cnt increments only when byte_received is high.
    check_cnt_update: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (cnt ==
                  ($past(byte_received) ? ($past(cnt) + 8'h1) :
                                          $past(cnt)))
    );

    // cnt and bytecnt move in lockstep.
    check_cnt_matches_bytecnt: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cnt == bytecnt)
    );

    // recived_status sets at 64 and stays set until reset.
    check_recived_status_update: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (recived_status ==
                  ($past(recived_status) || ($past(received_memory) == 8'd64)))
    );

    // byte_data_sent loads cnt or shifts left on active falling SCK.
    check_byte_data_sent_update: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (byte_data_sent ==
                  (($past(ssel_active) && $past(sck_fallingedge)) ?
                   (($past(bitcnt) == 3'b000) ? $past(cnt) :
                                                {$past(byte_data_sent[6:0]), 1'b0}) :
                   $past(byte_data_sent)))
    );

    // miso is always the MSB of byte_data_sent.
    check_miso_mapping: assert property (
        @(posedge clk) disable iff (!rst_n)
        (miso == byte_data_sent[7])
    );

endmodule