// SVA checker for CRC_serial_m_lfs_XOR
// - Uses a sampling clock to check purely combinational behavior
// - Concise, full functional equivalence, X-checks, and useful coverage

module CRC_serial_m_lfs_XOR_sva
  #(parameter int HASH_LENGTH = 64)
(
  input  logic                     clk,
  input  logic                     rst_n,
  input  logic                     i_message,
  input  logic [HASH_LENGTH-1:0]   i_cur_parity,
  input  logic [HASH_LENGTH-1:0]   o_next_parity
);

  // Must match DUT
  localparam bit [0:64] HASH_VALUE = 65'b11001001011011000101011110010101110101111000011100001111010000101;

  // Parameter guards
  initial begin
    assert (HASH_LENGTH >= 1)
      else $error("CRC_serial_m_lfs_XOR: HASH_LENGTH must be >=1");
    assert (HASH_LENGTH <= 65)
      else $error("CRC_serial_m_lfs_XOR: HASH_LENGTH must be <=65");
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Helper: recompute expected next parity
  function automatic logic [HASH_LENGTH-1:0] calc_next
    (input logic [HASH_LENGTH-1:0] cur, input logic msg);
    logic fb;
    logic [HASH_LENGTH-1:0] nxt;
    fb     = msg ^ cur[HASH_LENGTH-1];
    nxt[0] = fb;
    for (int j=1; j<HASH_LENGTH; j++) begin
      nxt[j] = HASH_VALUE[j] ? (cur[j-1] ^ fb) : cur[j-1];
    end
    return nxt;
  endfunction

  // X/Z check: known inputs => known outputs
  a_no_x: assert property (!$isunknown({i_message, i_cur_parity})) |-> !$isunknown(o_next_parity)
    else $error("o_next_parity contains X/Z for known inputs");

  // Full functional equivalence in one assertion
  a_equiv: assert property (o_next_parity == calc_next(i_cur_parity, i_message))
    else $error("o_next_parity mismatch with specified polynomial and LFSR update");

  // Useful coverage
  logic fb;
  assign fb = i_message ^ i_cur_parity[HASH_LENGTH-1];

  c_fb0: cover property (fb == 1'b0);
  c_fb1: cover property (fb == 1'b1);

  // Exercise both XOR-path outcomes for tapped bits, and observe activity for untapped bits
  genvar i;
  generate
    for (i=1; i<HASH_LENGTH; i++) begin : C
      if (HASH_VALUE[i]) begin
        c_tap_eq:  cover property (fb == 1'b0 && o_next_parity[i] == i_cur_parity[i-1]);
        c_tap_xor: cover property (fb == 1'b1 && o_next_parity[i] == ~i_cur_parity[i-1]);
      end else begin
        c_shift0: cover property (o_next_parity[i] == 1'b0);
        c_shift1: cover property (o_next_parity[i] == 1'b1);
      end
    end
  endgenerate

endmodule

// Example bind (provide any convenient sampling clock/reset from your TB):
// bind CRC_serial_m_lfs_XOR CRC_serial_m_lfs_XOR_sva #(.HASH_LENGTH(HASH_LENGTH))
//   u_crc_sva ( .clk(tb_clk),
//               .rst_n(tb_rst_n),
//               .i_message(i_message),
//               .i_cur_parity(i_cur_parity),
//               .o_next_parity(o_next_parity) );