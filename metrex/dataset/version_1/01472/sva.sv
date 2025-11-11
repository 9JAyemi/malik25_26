// SVA for adler_checksum
// Bind into DUT; checks key FSM behavior, data path updates, and output protocol.

module adler_checksum_sva #(parameter int PRIME = 65521,
                            parameter int BLOCK_SIZE = 16)
(
  input logic         clk,
  input logic         reset,
  input logic  [7:0]  data_in,
  input logic  [31:0] data_len,
  input logic  [15:0] checksum,
  input logic         valid,

  // Internal DUT signals
  input logic  [31:0] byte_count,
  input logic  [15:0] rolling_sum,
  input logic  [15:0] block_sum,
  input logic  [1:0]  state,
  input logic  [7:0]  data_in_reg,
  input logic  [15:0] checksum_reg
);

  localparam int IDLE = 0;
  localparam int PROCESSING = 1;
  localparam int CHECKSUM = 2;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (synchronous)
  assert property (@(posedge clk)
    reset |-> (state==IDLE && byte_count==0 && rolling_sum==16'd1 &&
               block_sum==16'd0 && checksum==16'd0 && valid==1'b0));

  // Legal state encoding
  assert property (state inside {IDLE, PROCESSING, CHECKSUM});

  // Input register capture
  assert property (data_in_reg == $past(data_in));

  // Keep data_len stable during PROCESSING
  assert property ($past(state)==PROCESSING |-> data_len == $past(data_len));

  // IDLE invariants
  assert property (state==IDLE |-> (byte_count==0 && rolling_sum==16'd1 && block_sum==16'd0));

  // PROCESSING: next-state decision
  assert property (
    $past(state)==PROCESSING && !($past(byte_count)==BLOCK_SIZE || $past(byte_count)==$past(data_len))
    |-> state==PROCESSING);

  assert property (
    $past(state)==PROCESSING && ($past(byte_count)==BLOCK_SIZE || $past(byte_count)==$past(data_len))
    |-> state==CHECKSUM);

  // PROCESSING: datapath updates
  assert property ($past(state)==PROCESSING
    |-> rolling_sum == (($past(rolling_sum) + $past(data_in_reg)) % PRIME)
     && block_sum   == (($past(block_sum)   + $past(data_in_reg)) % PRIME)
     && byte_count  == ($past(byte_count) + 1));

  // CHECKSUM: control and resets take effect next cycle
  assert property ($past(state)==CHECKSUM |-> state==IDLE);
  assert property ($past(state)==CHECKSUM |-> byte_count==0 && rolling_sum==16'd1 && block_sum==16'd0);

  // CHECKSUM: valid derives from equality in the CHECKSUM cycle
  assert property ($past(state)==CHECKSUM |-> valid == ($past(checksum_reg) == $past(checksum)));

  // CHECKSUM: checksum output is previous checksum_reg; checksum_reg computes truncated sum
  assert property ($past(state)==CHECKSUM |-> checksum == $past(checksum_reg));
  assert property ($past(state)==CHECKSUM
    |-> checksum_reg == ((( $past(block_sum) << 16) + $past(rolling_sum)) & 16'hFFFF));

  // Invariants: modulo range
  assert property (rolling_sum < PRIME);
  assert property (block_sum   < PRIME);

  // valid and checksum only change on CHECKSUM cycle (except reset)
  assert property ($past(state)!=CHECKSUM |-> valid == $past(valid));
  assert property ($past(state)!=CHECKSUM |-> checksum == $past(checksum));

  // Coverage

  // Basic flow: IDLE -> PROCESSING (some cycles) -> CHECKSUM -> IDLE
  cover property (state==IDLE ##1 state==PROCESSING [*1:$] ##1 state==CHECKSUM ##1 state==IDLE);

  // Cover exit due to BLOCK_SIZE
  cover property ($past(state)==PROCESSING && $past(byte_count)==BLOCK_SIZE ##1 state==CHECKSUM);

  // Cover exit due to data_len
  cover property ($past(state)==PROCESSING && $past(byte_count)==$past(data_len) ##1 state==CHECKSUM);

  // Cover valid asserted and deasserted outcomes
  cover property ($past(state)==CHECKSUM && valid==1);
  cover property ($past(state)==CHECKSUM && valid==0);

endmodule

bind adler_checksum adler_checksum_sva #(.PRIME(PRIME), .BLOCK_SIZE(BLOCK_SIZE)) adler_checksum_sva_i (.*);