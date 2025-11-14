// spi_slave SVA (bindable). Focused, concise, and parameter-aware (flags 8-bit assumptions).

module spi_slave_sva #(parameter int msg_len = 8)
(
  input  logic                          CLK,
  input  logic                          SCK, MOSI, SSEL,
  input  logic                          MISO,
  input  logic [msg_len-1:0]            MSG,

  // internal DUT state (hier-bound)
  input  logic [2:0]                    SCKr,
  input  logic [2:0]                    SSELr,
  input  logic [1:0]                    MOSIr,
  input  logic                          SCK_risingedge,
  input  logic                          SSEL_active,
  input  logic                          MOSI_data,
  input  logic [$clog2(msg_len+1)-1:0]  bitcnt,
  input  logic                          is_msg_received,
  input  logic [msg_len-1:0]            msg_data_received
);

  localparam int BITCNT_W = $clog2(msg_len+1);

  default clocking cb @(posedge CLK); endclocking

  // Design assumption (DUT hard-codes 8-bit behavior)
  a_only_8_supported: assert property (msg_len == 8);

  // Synchronizers behave as shift registers
  a_sync_sck:  assert property (SCKr  == { $past(SCKr[1:0]),  $past(SCK)  });
  a_sync_ssel: assert property (SSELr == { $past(SSELr[1:0]), $past(SSEL) });
  a_sync_mosi: assert property (MOSIr == { $past(MOSIr[0]),   $past(MOSI) });

  // Derived strobes / pulses
  a_sckre_one_shot:   assert property (SCK_risingedge |=> !SCK_risingedge);
  a_ssel_active_def:  assert property (SSEL_active == ~SSELr[1]);

  // Counter behavior
  a_cnt_reset_when_inactive: assert property (!SSEL_active |-> (bitcnt == '0));
  a_cnt_increments_on_sck:   assert property (SSEL_active && SCK_risingedge |=> bitcnt == $past(bitcnt) + 1);
  a_cnt_stable_otherwise:    assert property (SSEL_active && !SCK_risingedge |=> bitcnt == $past(bitcnt));

  // Shift register behavior (MSB-first)
  a_shift_on_edge: assert property (
    SSEL_active && SCK_risingedge && (bitcnt < msg_len)
    |=> msg_data_received == { $past(msg_data_received[msg_len-2:0]), $past(MOSI_data) }
  );
  a_no_shift_when_full_or_idle: assert property (
    (!SSEL_active) || (SSEL_active && SCK_risingedge && (bitcnt >= msg_len)) || (SSEL_active && !SCK_risingedge)
    |=> msg_data_received == $past(msg_data_received)
  );

  // Message flag timing (fires on the last bit)
  a_flag_def:         assert property (is_msg_received |-> (SSEL_active && SCK_risingedge && (bitcnt == msg_len-1)));
  a_flag_on_last_bit: assert property ((SSEL_active && SCK_risingedge && (bitcnt == msg_len-1)) |-> is_msg_received);
  a_flag_low_idle:    assert property (!SSEL_active |-> !is_msg_received);

  // Outputs
  a_miso_constant_zero: assert property (MISO == 1'b0);
  a_msg_drives_storage: assert property (MSG == msg_data_received);

  // Compact coverage
  c_full_frame:      cover property (SSEL_active ##1 (SSEL_active && SCK_risingedge)[*msg_len-1]
                                     ##1 (SSEL_active && SCK_risingedge && is_msg_received));
  c_cap_zero_bit:    cover property (SSEL_active && SCK_risingedge && (MOSI_data == 1'b0));
  c_cap_one_bit:     cover property (SSEL_active && SCK_risingedge && (MOSI_data == 1'b1));
  c_abort_midframe:  cover property (SSEL_active ##[1:$] !SSEL_active && (bitcnt != '0));

endmodule

bind spi_slave spi_slave_sva #(.msg_len(msg_len)) u_spi_slave_sva (
  .CLK(CLK),
  .SCK(SCK),
  .MOSI(MOSI),
  .SSEL(SSEL),
  .MISO(MISO),
  .MSG(MSG),
  .SCKr(SCKr),
  .SSELr(SSELr),
  .MOSIr(MOSIr),
  .SCK_risingedge(SCK_risingedge),
  .SSEL_active(SSEL_active),
  .MOSI_data(MOSI_data),
  .bitcnt(bitcnt),
  .is_msg_received(is_msg_received),
  .msg_data_received(msg_data_received)
);