module spi_slave_0_base_sva(
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

    // SCK is sampled into the 3-bit synchronizer.
    check_sck_sampler: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> sckr == {$past(sckr[1:0]), $past(sck)}
    );

    // SSEL is sampled into the 3-bit synchronizer.
    check_ssel_sampler: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> sselr == {$past(sselr[1:0]), $past(ssel)}
    );

    // MOSI is sampled into the 2-bit synchronizer.
    check_mosi_sampler: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> mosir == {$past(mosir[0]), $past(mosi)}
    );

    // Rising-edge detect matches the sampled SCK history.
    check_sck_risingedge_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        sck_risingedge == (sckr[2:1] == 2'b01)
    );

    // Falling-edge detect matches the sampled SCK history.
    check_sck_fallingedge_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        sck_fallingedge == (sckr[2:1] == 2'b10)
    );

    // Active-low slave select decode matches the sampled SSEL history.
    check_ssel_active_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        ssel_active == ~sselr[1]
    );

    // Start-of-message detect matches the sampled SSEL history.
    check_ssel_startmessage_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        ssel_startmessage == (sselr[2:1] == 2'b10)
    );

    // End-of-message detect matches the sampled SSEL history.
    check_ssel_endmessage_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        ssel_endmessage == (sselr[2:1] == 2'b01)
    );

    // The MOSI data tap is the delayed MOSI sample.
    check_mosi_data_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        mosi_data == mosir[1]
    );

    // Bit counter clears whenever the slave is not selected.
    check_bitcnt_clears_when_inactive: assert property (
        @(posedge clk) disable iff (!rst_n)
        !ssel_active |=> bitcnt == 3'b000
    );

    // Bit counter increments on each sampled SCK rising edge while selected.
    check_bitcnt_increments_on_risingedge: assert property (
        @(posedge clk) disable iff (!rst_n)
        ssel_active && sck_risingedge |=> bitcnt == ($past(bitcnt) + 3'b001)
    );

    // Bit counter holds when selected but no sampled SCK rising edge occurs.
    check_bitcnt_holds_without_risingedge: assert property (
        @(posedge clk) disable iff (!rst_n)
        ssel_active && !sck_risingedge |=> bitcnt == $past(bitcnt)
    );

    // Received byte data shifts in MOSI on each sampled SCK rising edge.
    check_byte_data_received_shifts_on_risingedge: assert property (
        @(posedge clk) disable iff (!rst_n)
        ssel_active && sck_risingedge |=> byte_data_received == {$past(byte_data_received[6:0]), $past(mosi_data)}
    );

    // A byte is flagged received after the eighth sampled rising edge.
    check_byte_received_on_last_bit: assert property (
        @(posedge clk) disable iff (!rst_n)
        ssel_active && sck_risingedge && (bitcnt == 3'b111) |=> byte_received
    );

    // No byte-received pulse occurs unless the last-bit condition was met.
    check_byte_received_only_on_last_bit: assert property (
        @(posedge clk) disable iff (!rst_n)
        !(ssel_active && sck_risingedge && (bitcnt == 3'b111)) |=> !byte_received
    );

    // Byte counter increments on each byte-received pulse.
    check_bytecnt_increments_on_byte_received: assert property (
        @(posedge clk) disable iff (!rst_n)
        byte_received |=> bytecnt == ($past(bytecnt) + 8'h01)
    );

    // Byte counter holds when no byte-received pulse occurs.
    check_bytecnt_holds_without_byte_received: assert property (
        @(posedge clk) disable iff (!rst_n)
        !byte_received |=> bytecnt == $past(bytecnt)
    );

    // The transmit count mirrors the received-byte count.
    check_cnt_tracks_bytecnt: assert property (
        @(posedge clk) disable iff (!rst_n)
        cnt == bytecnt
    );

    // Received-memory increments only for matching byte value and count.
    check_received_memory_increments_on_match: assert property (
        @(posedge clk) disable iff (!rst_n)
        byte_received && (byte_data_received == bytecnt) |=> received_memory == ($past(received_memory) + 8'h01)
    );

    // Received-memory holds when no matching byte-received event occurs.
    check_received_memory_holds_without_match: assert property (
        @(posedge clk) disable iff (!rst_n)
        (!byte_received || (byte_data_received != bytecnt)) |=> received_memory == $past(received_memory)
    );

    // Transmit data loads the current count at the start of a byte on SCK falling edge.
    check_byte_data_sent_loads_cnt: assert property (
        @(posedge clk) disable iff (!rst_n)
        ssel_active && sck_fallingedge && (bitcnt == 3'b000) |=> byte_data_sent == $past(cnt)
    );

    // Transmit data shifts left with zero fill on later falling edges.
    check_byte_data_sent_shifts_after_load: assert property (
        @(posedge clk) disable iff (!rst_n)
        ssel_active && sck_fallingedge && (bitcnt != 3'b000) |=> byte_data_sent == {$past(byte_data_sent[6:0]), 1'b0}
    );

    // Transmit data holds when no active falling-edge event occurs.
    check_byte_data_sent_holds_without_fallingedge: assert property (
        @(posedge clk) disable iff (!rst_n)
        !(ssel_active && sck_fallingedge) |=> byte_data_sent == $past(byte_data_sent)
    );

    // MISO always reflects the MSB of the transmit shift register.
    check_miso_matches_transmit_msb: assert property (
        @(posedge clk) disable iff (!rst_n)
        miso == byte_data_sent[7]
    );

    // Status reflects whether received-memory equaled 64 on the prior cycle.
    check_received_status_from_memory: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> recived_status == ($past(received_memory) == 8'd64)
    );

endmodule