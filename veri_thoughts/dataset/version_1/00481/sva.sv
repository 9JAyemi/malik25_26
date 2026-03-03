// SVA for CRC_serial_m_lfs_XOR
// Concise, high-quality functional checks and minimal coverage

module CRC_serial_m_lfs_XOR_sva #(
  parameter int HASH_LENGTH = 64
)(
  input  logic                      clk,
  input  logic                      rst_n,
  input  logic                      i_message,
  input  logic [HASH_LENGTH-1:0]    i_cur_parity,
  input  logic [HASH_LENGTH-1:0]    o_next_parity
);

  // Must match DUT
  localparam [0:64] HASH_VALUE = 65'b11001001011011000101011110010101110101111000011100001111010000101;

  // Basic param sanity (immediate)
  initial begin
    assert (HASH_LENGTH >= 1 && HASH_LENGTH <= 65)
      else $error("CRC_serial_m_lfs_XOR: HASH_LENGTH out of range [1..65]");
  end

  // Helpers
  function automatic logic fb_bit(input logic msg, input logic [HASH_LENGTH-1:0] cur);
    fb_bit = msg ^ cur[HASH_LENGTH-1];
  endfunction

  function automatic logic [HASH_LENGTH-1:0] shift_right_1(input logic [HASH_LENGTH-1:0] cur);
    if (HASH_LENGTH == 1) shift_right_1 = '0;
    else                  shift_right_1 = {cur[HASH_LENGTH-2:0], 1'b0};
  endfunction

  function automatic logic [HASH_LENGTH-1:0] tap_vec();
    logic [HASH_LENGTH-1:0] t;
    for (int j = 0; j < HASH_LENGTH; j++) begin
      if (j == 0) t[j] = 1'b1;
      else        t[j] = HASH_VALUE[j];
    end
    return t;
  endfunction

  function automatic logic [HASH_LENGTH-1:0] expected_next(
    input logic msg, input logic [HASH_LENGTH-1:0] cur
  );
    logic fb;
    fb = fb_bit(msg, cur);
    expected_next = shift_right_1(cur) ^ ({HASH_LENGTH{fb}} & tap_vec());
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X/Z on outputs when inputs are known
  assert property ( !$isunknown({i_message, i_cur_parity}) |-> !$isunknown(o_next_parity) );

  // Full functional equivalence (single concise vector check)
  assert property ( o_next_parity == expected_next(i_message, i_cur_parity) );

  // Bit 0 check (feedback term)
  assert property ( o_next_parity[0] == fb_bit(i_message, i_cur_parity) );

  // Pass-through behavior when feedback is 0
  assert property ( (fb_bit(i_message, i_cur_parity) == 1'b0)
                    |-> (o_next_parity == shift_right_1(i_cur_parity)) );

  // Minimal, meaningful coverage
  cover property ( fb_bit(i_message, i_cur_parity) == 1'b0 );
  cover property ( fb_bit(i_message, i_cur_parity) == 1'b1 );

endmodule

// Bind into the DUT. Assumes clk and rst_n are visible in the instance scope.
bind CRC_serial_m_lfs_XOR
  CRC_serial_m_lfs_XOR_sva #(.HASH_LENGTH(HASH_LENGTH))
    crc_sva ( .clk(clk), .rst_n(rst_n),
              .i_message(i_message),
              .i_cur_parity(i_cur_parity),
              .o_next_parity(o_next_parity) );