Below is a concise, high‑quality SVA block you can drop inside quick_spi_hard (e.g., at the end of the module) to thoroughly check key behaviors, timing, and data mapping. It references internal signals for strong checking. Guarded for simulation only.

`ifndef SYNTHESIS
// Assertions/coverage for quick_spi_hard
// Place inside the module quick_spi_hard
// Default clocking and reset
default clocking cb @(posedge clk); endclocking
default disable iff (!reset_n)

// Helper: total SCLK toggles for the active transaction (latched in transaction_toggles)
function automatic int tot_toggles();
  return (OUTGOING_DATA_WIDTH*2) + transaction_toggles;
endfunction

// Reference function for byte-order mapping (mirrors DUT put_data)
function automatic [`MAX_DATA_WIDTH-1:0] put_data_ref(input [`MAX_DATA_WIDTH-1:0] data, input order);
  reg [`MAX_DATA_WIDTH-1:0] result;
  reg [7:0] shift;
  begin
    shift = `MAX_DATA_WIDTH - (((OUTGOING_DATA_WIDTH > 1) ? (OUTGOING_DATA_WIDTH / 8) : 0)
                               + ((OUTGOING_DATA_WIDTH > (((OUTGOING_DATA_WIDTH > 1)?(OUTGOING_DATA_WIDTH/8):0)*8)) ? 1 : 0)) * 8;
    if (order == `BIG_ENDIAN) begin
      result = {data[7:0], data[15:8], data[23:16], data[31:24], data[39:32], data[47:40], data[55:48], data[63:56]};
      put_data_ref = (shift > 0) ? (result >> shift) : result;
    end
    else begin
      put_data_ref = data;
    end
  end
endfunction

// 1) Reset values
assert property (cb
  !reset_n |-> (end_of_transaction==1'b0
                && mosi==MOSI_IDLE_VALUE
                && sclk==CPOL
                && ss_n=={NUMBER_OF_SLAVES{1'b1}}
                && sclk_toggle_count==0
                && state==IDLE
                && incoming_data=={INCOMING_DATA_WIDTH{1'b0}})
) else $error("Reset values mismatch");

// 2) No transaction without enable
assert property (cb
  (state==IDLE && start_transaction && !enable) |=> (state==IDLE && ss_n=={NUMBER_OF_SLAVES{1'b1}})
) else $error("Transaction started without enable");

// 3) Start -> ACTIVE handshake and transaction_toggles latch correctness
assert property (cb
  (state==IDLE && enable && start_transaction)
  |=> (state==ACTIVE
       && transaction_toggles == ((operation==READ)? ALL_READ_SCLK_TOGGLES : EXTRA_WRITE_SCLK_TOGGLES))
) else $error("Start->ACTIVE or transaction_toggles latch incorrect");

// 4) Outgoing data buffer mapping after start (byte order)
assert property (cb
  (state==IDLE && enable && start_transaction)
  |=> (outgoing_data_buffer
       == put_data_ref({{(`MAX_DATA_WIDTH-OUTGOING_DATA_WIDTH){1'b0}}, outgoing_data}, BYTES_ORDER)[OUTGOING_DATA_WIDTH-1:0])
) else $error("Outgoing data buffer byte-order mapping incorrect");

// 5) Slave selection: one selected (within one cycle), stable during ACTIVE
// Selected slave goes low within 1 cycle of entering ACTIVE
assert property (cb
  (state==IDLE && enable && start_transaction)
  |-> ##[0:1] (ss_n[slave]==1'b0)
) else $error("SS not asserted in time after start");
// Only one slave asserted during ACTIVE (after first toggle begins)
assert property (cb
  (state==ACTIVE && sclk_toggle_count>0) |-> ($countones(~ss_n)==1 && ss_n[slave]==1'b0)
) else $error("Multiple or wrong SS active during ACTIVE");
// Slave index stable during ACTIVE
assert property (cb
  (state==ACTIVE) |=> $stable(slave)
) else $error("Slave changed during ACTIVE");

// 6) SCLK behavior
// No spurious SCLK changes when not permitted
assert property (cb
  (state!=ACTIVE || ss_n[slave]==1'b1 || (sclk_toggle_count>=tot_toggles()))
  |=> $stable(sclk)
) else $error("SCLK changed outside allowed window");
// When permitted, SCLK changes every cycle and counter increments by 1
assert property (cb
  (state==ACTIVE && ss_n[slave]==1'b0 && sclk_toggle_count < tot_toggles())
  |=> ($changed(sclk) && sclk_toggle_count == $past(sclk_toggle_count)+1)
) else $error("SCLK toggle or counter increment missing during ACTIVE");

// 7) End-of-transaction pulse and cleanup
// EOT conditions in same cycle
assert property (cb
  (state==ACTIVE && sclk_toggle_count==tot_toggles())
  |-> (ss_n[slave]==1'b1 && mosi==MOSI_IDLE_VALUE && sclk==CPOL && end_of_transaction==1'b1)
) else $error("EOT cleanup outputs incorrect");
// Next cycle after EOT: WAIT, pulse width, counter reset
assert property (cb
  (state==ACTIVE && sclk_toggle_count==tot_toggles())
  |=> (state==WAIT && end_of_transaction==1'b0 && sclk_toggle_count==0)
) else $error("Post-EOT state/counter incorrect");
// Incoming data captured at EOT for READ
assert property (cb
  (state==ACTIVE && sclk_toggle_count==tot_toggles() && operation==READ)
  |-> (incoming_data == $past(incoming_data_buffer))
) else $error("Incoming data not captured correctly on READ");

// 8) MOSI idle when not ACTIVE
assert property (cb
  (state!=ACTIVE) |-> (mosi==MOSI_IDLE_VALUE)
) else $error("MOSI not idle outside ACTIVE");

// 9) MOSI data timing vs outgoing_data_buffer
// LSB-first: on transmit half-cycles emit LSB, then shift by 1
generate if (BITS_ORDER == `LSB_FIRST) begin
  assert property (cb
    (state==ACTIVE && spi_clock_phase==1'b1 && sclk_toggle_count < (OUTGOING_DATA_WIDTH*2)-1)
    |=> (mosi == $past(outgoing_data_buffer[0])
         && outgoing_data_buffer == ($past(outgoing_data_buffer) >> 1))
  ) else $error("LSB-first MOSI/shift mismatch");
end else begin
// MSB-first: emit [7-bit_counter], shift by 8 when counter==7
  assert property (cb
    (state==ACTIVE && spi_clock_phase==1'b1 && sclk_toggle_count < (OUTGOING_DATA_WIDTH*2)-1)
    |=> (mosi == $past(outgoing_data_buffer[7 - $past(bit_counter)]))
  ) else $error("MSB-first MOSI value mismatch");
  assert property (cb
    (state==ACTIVE && spi_clock_phase==1'b1 && sclk_toggle_count < (OUTGOING_DATA_WIDTH*2)-1 && $past(bit_counter)==3'd7)
    |=> (outgoing_data_buffer == ($past(outgoing_data_buffer) >> 8))
  ) else $error("MSB-first byte shift timing mismatch");
end endgenerate

// 10) SCLK idle level outside ACTIVE (including reset, IDLE, WAIT)
assert property (cb
  (state!=ACTIVE) |-> (sclk==CPOL)
) else $error("SCLK not at CPOL when inactive");

// 11) Coverage: one READ and one WRITE transaction completion
cover property (cb
  (state==IDLE && enable && start_transaction && operation==WRITE)
  ##[1:$] (state==ACTIVE && sclk_toggle_count==tot_toggles())
);
cover property (cb
  (state==IDLE && enable && start_transaction && operation==READ)
  ##[1:$] (state==ACTIVE && sclk_toggle_count==tot_toggles() && end_of_transaction)
);
`endif