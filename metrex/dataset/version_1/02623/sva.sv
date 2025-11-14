// SVA for fifo_top
// Bind these assertions to the DUT
// Encodings (mirroring DUT intent)
module fifo_top_asserts #(
  parameter int DATA_WIDTH = 4,
  parameter int NUM_ENTRIES = 4,
  parameter int OPCODE_WIDTH = 2,
  parameter int LINE_WIDTH = DATA_WIDTH + OPCODE_WIDTH,
  parameter int NUM_ENTRIES_BIT = (NUM_ENTRIES<=2)?1:
                                  (NUM_ENTRIES<=4)?2:
                                  (NUM_ENTRIES<=8)?3:
                                  (NUM_ENTRIES<=16)?4:
                                  (NUM_ENTRIES<=32)?5:
                                  (NUM_ENTRIES<=64)?6:
                                  (NUM_ENTRIES<=128)?7:
                                  (NUM_ENTRIES<=256)?8:-1
) (
  // DUT ports
  input  logic                          clk,
  input  logic                          reset,
  input  logic [LINE_WIDTH-1:0]         vector_in,
  input  logic [DATA_WIDTH-1:0]         data_out,
  input  logic                          empty_flag,
  input  logic                          full_flag,
  // DUT internals
  input  logic [DATA_WIDTH-1:0]         fifo_data [NUM_ENTRIES],
  input  logic [NUM_ENTRIES-1:0]        fifo_valid_invalid_bit,
  input  logic [OPCODE_WIDTH-1:0]       control_in,
  input  logic [DATA_WIDTH-1:0]         data_in,
  input  logic [NUM_ENTRIES_BIT-1:0]    fifo_head_pos,
  input  logic [NUM_ENTRIES_BIT-1:0]    fifo_tail_pos
);

  localparam logic [1:0] READ       = 2'b01;
  localparam logic [1:0] WRITE      = 2'b10;
  localparam logic [1:0] DO_NOTHING = 2'b00;
  localparam logic [1:0] INVALID_OP = 2'b11;

  localparam logic DATA_VALID       = 1'b1;
  localparam logic DATA_INVALID     = 1'b0;

  localparam logic FIFO_FULL        = 1'b1;
  localparam logic FIFO_NOT_FULL    = 1'b0;
  localparam logic FIFO_EMPTY       = 1'b1;
  localparam logic FIFO_NOT_EMPTY   = 1'b0;

  default clocking cb @(posedge clk); endclocking
  // Use explicit reset checks where needed; otherwise disable-on-reset
  // Assertions

  // Reset state (intended safe FIFO reset)
  ap_reset_state: assert property (@cb reset |-> (
      fifo_head_pos == '0 && fifo_tail_pos == '0 &&
      fifo_valid_invalid_bit == '0 &&
      data_out == '0 &&
      empty_flag == FIFO_EMPTY && full_flag == FIFO_NOT_FULL
  ));

  // Decoding from vector_in
  ap_decode_ctrl: assert property (@cb !reset |-> control_in == vector_in[LINE_WIDTH-1 -: OPCODE_WIDTH]);
  ap_decode_data: assert property (@cb !reset |-> data_in    == vector_in[DATA_WIDTH-1:0]);

  // Pointer in-range
  ap_head_in_range: assert property (@cb disable iff (reset) fifo_head_pos < NUM_ENTRIES);
  ap_tail_in_range: assert property (@cb disable iff (reset) fifo_tail_pos < NUM_ENTRIES);

  // Flags reflect occupancy (empty iff 0 valid; full iff all valid)
  ap_empty_def: assert property (@cb disable iff (reset)
    (empty_flag == FIFO_EMPTY) == ($countones(fifo_valid_invalid_bit) == 0)
  );
  ap_full_def: assert property (@cb disable iff (reset)
    (full_flag == FIFO_FULL) == ($countones(fifo_valid_invalid_bit) == NUM_ENTRIES)
  );
  ap_flags_mutex: assert property (@cb disable iff (reset)
    !(empty_flag == FIFO_EMPTY && full_flag == FIFO_FULL)
  );

  // WRITE happens only when DUT gating allows; then write effects must occur
  let write_allowed = (control_in == WRITE) && (empty_flag == FIFO_EMPTY) && (full_flag == FIFO_NOT_FULL);
  ap_write_sets_data_and_valid: assert property (@cb disable iff (reset)
    write_allowed |=> (
      fifo_valid_invalid_bit[$past(fifo_head_pos)] == DATA_VALID &&
      fifo_data[$past(fifo_head_pos)] == $past(data_in)
    )
  );
  ap_write_adv_head: assert property (@cb disable iff (reset)
    write_allowed |=> fifo_head_pos ==
      (($past(fifo_head_pos) == NUM_ENTRIES-1) ? '0 : $past(fifo_head_pos) + 1)
  );
  ap_write_occ_incr: assert property (@cb disable iff (reset)
    write_allowed |=> $countones(fifo_valid_invalid_bit) == $past($countones(fifo_valid_invalid_bit)) + 1
  );
  // If WRITE not allowed, head must not advance
  ap_write_blocked_no_head_move: assert property (@cb disable iff (reset)
    (control_in == WRITE && !write_allowed) |=> fifo_head_pos == $past(fifo_head_pos)
  );

  // READ with valid entry at tail: data_out, invalidate bit, and advance tail
  let read_allowed = (control_in == READ) && (fifo_valid_invalid_bit[fifo_tail_pos] == DATA_VALID);
  ap_read_drives_data: assert property (@cb disable iff (reset)
    read_allowed |=> data_out == $past(fifo_data[$past(fifo_tail_pos)])
  );
  ap_read_clears_valid: assert property (@cb disable iff (reset)
    read_allowed |=> fifo_valid_invalid_bit[$past(fifo_tail_pos)] == DATA_INVALID
  );
  ap_read_adv_tail: assert property (@cb disable iff (reset)
    read_allowed |=> fifo_tail_pos == $past(fifo_tail_pos) + 1
  );
  ap_read_occ_decr: assert property (@cb disable iff (reset)
    read_allowed |=> $countones(fifo_valid_invalid_bit) == $past($countones(fifo_valid_invalid_bit)) - 1
  );

  // READ when invalid at tail: do not move tail
  let read_blocked = (control_in == READ) && (fifo_valid_invalid_bit[fifo_tail_pos] == DATA_INVALID);
  ap_read_blocked_no_tail_move: assert property (@cb disable iff (reset)
    read_blocked |=> fifo_tail_pos == $past(fifo_tail_pos)
  );
  // Optional: data_out was driven unknown in the read-blocked cycle
  ap_read_blocked_xdata: assert property (@cb disable iff (reset)
    read_blocked |=> $isunknown($past(data_out))
  );

  // Simple functional covers
  cv_write_then_read: cover property (@cb disable iff (reset)
    write_allowed ##1 read_allowed
  );
  cv_head_wrap: cover property (@cb disable iff (reset)
    write_allowed && (fifo_head_pos == NUM_ENTRIES-1) ##1 (fifo_head_pos == '0)
  );
  cv_tail_wrap: cover property (@cb disable iff (reset)
    read_allowed && ($past(fifo_tail_pos) == NUM_ENTRIES-1) ##1 (fifo_tail_pos == '0)
  );
  cv_default_opcode: cover property (@cb disable iff (reset)
    control_in inside {DO_NOTHING, INVALID_OP}
  );

endmodule

// Bind to the DUT (connect internal signals)
bind fifo_top fifo_top_asserts #(
  .DATA_WIDTH(DATA_WIDTH),
  .NUM_ENTRIES(NUM_ENTRIES),
  .OPCODE_WIDTH(OPCODE_WIDTH),
  .LINE_WIDTH(LINE_WIDTH),
  .NUM_ENTRIES_BIT(NUM_ENTRIES_BIT)
) fifo_top_asserts_i (
  .clk(clk),
  .reset(reset),
  .vector_in(vector_in),
  .data_out(data_out),
  .empty_flag(empty_flag),
  .full_flag(full_flag),
  .fifo_data(fifo_data),
  .fifo_valid_invalid_bit(fifo_valid_invalid_bit),
  .control_in(control_in),
  .data_in(data_in),
  .fifo_head_pos(fifo_head_pos),
  .fifo_tail_pos(fifo_tail_pos)
);