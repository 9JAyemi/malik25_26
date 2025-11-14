// SVA for alt_vipvfr131_vfr_controller
// Concise, high-signal-quality checks with essential coverage

module alt_vipvfr131_vfr_controller_asserts #(
  parameter MASTER_ADDRESS_WIDTH = 32,
  parameter MASTER_DATA_WIDTH    = 32,
  parameter CONTROL_PACKET_RESOLUTION_REQUIREDWIDTH = 16,
  parameter CONTROL_PACKET_INTERLACED_REQUIREDWIDTH = 4,
  parameter PACKET_ADDRESS_WIDTH = 32,
  parameter PACKET_SAMPLES_WIDTH = 32,
  parameter PACKET_WORDS_WIDTH   = 32
)(
  input  logic                                   clock,
  input  logic                                   reset,

  // DUT ports
  input  logic [MASTER_ADDRESS_WIDTH-1:0]        master_address,
  input  logic                                   master_write,
  input  logic [MASTER_DATA_WIDTH-1:0]           master_writedata,
  input  logic                                   master_interrupt_recieve,

  input  logic                                   go_bit,
  input  logic                                   next_bank,

  input  logic [CONTROL_PACKET_RESOLUTION_REQUIREDWIDTH-1:0] ctrl_packet_width_bank0,
  input  logic [CONTROL_PACKET_RESOLUTION_REQUIREDWIDTH-1:0] ctrl_packet_height_bank0,
  input  logic [CONTROL_PACKET_INTERLACED_REQUIREDWIDTH-1:0] ctrl_packet_interlaced_bank0,

  input  logic [PACKET_ADDRESS_WIDTH-1:0]        vid_packet_base_address_bank0,
  input  logic [PACKET_SAMPLES_WIDTH-1:0]        vid_packet_samples_bank0,
  input  logic [PACKET_WORDS_WIDTH-1:0]          vid_packet_words_bank0,

  input  logic [CONTROL_PACKET_RESOLUTION_REQUIREDWIDTH-1:0] ctrl_packet_width_bank1,
  input  logic [CONTROL_PACKET_RESOLUTION_REQUIREDWIDTH-1:0] ctrl_packet_height_bank1,
  input  logic [CONTROL_PACKET_INTERLACED_REQUIREDWIDTH-1:0] ctrl_packet_interlaced_bank1,

  input  logic [PACKET_ADDRESS_WIDTH-1:0]        vid_packet_base_address_bank1,
  input  logic [PACKET_SAMPLES_WIDTH-1:0]        vid_packet_samples_bank1,
  input  logic [PACKET_WORDS_WIDTH-1:0]          vid_packet_words_bank1,

  input  logic [CONTROL_PACKET_RESOLUTION_REQUIREDWIDTH-1:0] width_of_next_vid_packet,
  input  logic [CONTROL_PACKET_RESOLUTION_REQUIREDWIDTH-1:0] height_of_next_vid_packet,
  input  logic [CONTROL_PACKET_INTERLACED_REQUIREDWIDTH-1:0] interlaced_of_next_vid_packet,
  input  logic                                   do_control_packet,

  input  logic                                   running,
  input  logic                                   frame_complete,

  // Internal DUT regs (bound)
  input  logic [2:0]                             state,
  input  logic                                   bank_to_read
);

  // Mirror DUT encodings
  localparam [2:0] IDLE                               = 3'd0;
  localparam [2:0] SENDING_ADDRESS                    = 3'd1;
  localparam [2:0] SENDING_SAMPLES                    = 3'd2;
  localparam [2:0] SENDING_WORDS                      = 3'd3;
  localparam [2:0] SENDING_TYPE                       = 3'd4;
  localparam [2:0] SENDING_GO_AND_ENABLE_INTERRUPT    = 3'd5;
  localparam [2:0] WAITING_END_FRAME                  = 3'd6;

  localparam int PACKET_READER_GO_ADDRESS             = 0;
  localparam int PACKET_READER_STATUS_ADDRESS         = 1;
  localparam int PACKET_READER_INTERRUPT_ADDRESS      = 2;
  localparam int PACKET_READER_PACKET_ADDRESS_ADDRESS = 3;
  localparam int PACKET_READER_PACKET_TYPE_ADDRESS    = 4;
  localparam int PACKET_READER_PACKET_SAMPLES_ADDRESS = 5;
  localparam int PACKET_READER_PACKET_WORDS_ADDRESS   = 6;

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Reset sanity
  assert property (reset |-> state==IDLE && !master_write && !running && !frame_complete && !do_control_packet);

  // FSM transitions
  assert property (state==IDLE && !go_bit |=> state==IDLE);
  assert property (state==IDLE &&  go_bit |=> state==SENDING_ADDRESS);
  assert property (state==SENDING_ADDRESS                 |=> state==SENDING_SAMPLES);
  assert property (state==SENDING_SAMPLES                 |=> state==SENDING_WORDS);
  assert property (state==SENDING_WORDS                   |=> state==SENDING_TYPE);
  assert property (state==SENDING_TYPE                    |=> state==SENDING_GO_AND_ENABLE_INTERRUPT);
  assert property (state==SENDING_GO_AND_ENABLE_INTERRUPT |=> state==WAITING_END_FRAME);
  assert property (state==WAITING_END_FRAME && !master_interrupt_recieve |=> state==WAITING_END_FRAME);
  assert property (state==WAITING_END_FRAME &&  master_interrupt_recieve |=> state==IDLE);

  // Latching of bank and running on go
  assert property (state==IDLE && go_bit |=> running && bank_to_read==$past(next_bank));

  // Bank remains stable during an active transaction
  assert property ((state inside {SENDING_ADDRESS,SENDING_SAMPLES,SENDING_WORDS,SENDING_TYPE,SENDING_GO_AND_ENABLE_INTERRUPT,WAITING_END_FRAME}) |-> $stable(bank_to_read));

  // No writes in IDLE
  assert property (state==IDLE |-> !master_write);

  // Per-state address/data/write checks
  assert property (
    state==SENDING_ADDRESS |->
      master_write &&
      master_address==PACKET_READER_PACKET_ADDRESS_ADDRESS &&
      do_control_packet &&
      (
        (bank_to_read==1'b0 &&
          master_writedata==vid_packet_base_address_bank0 &&
          width_of_next_vid_packet==ctrl_packet_width_bank0 &&
          height_of_next_vid_packet==ctrl_packet_height_bank0 &&
          interlaced_of_next_vid_packet==ctrl_packet_interlaced_bank0) ||
        (bank_to_read==1'b1 &&
          master_writedata==vid_packet_base_address_bank1 &&
          width_of_next_vid_packet==ctrl_packet_width_bank1 &&
          height_of_next_vid_packet==ctrl_packet_height_bank1 &&
          interlaced_of_next_vid_packet==ctrl_packet_interlaced_bank1)
      )
  );

  assert property (
    state==SENDING_SAMPLES |->
      master_write &&
      master_address==PACKET_READER_PACKET_SAMPLES_ADDRESS &&
      !do_control_packet &&
      (
        (bank_to_read==1'b0 && master_writedata==vid_packet_samples_bank0) ||
        (bank_to_read==1'b1 && master_writedata==vid_packet_samples_bank1)
      )
  );

  assert property (
    state==SENDING_WORDS |->
      master_write &&
      master_address==PACKET_READER_PACKET_WORDS_ADDRESS &&
      (
        (bank_to_read==1'b0 && master_writedata==vid_packet_words_bank0) ||
        (bank_to_read==1'b1 && master_writedata==vid_packet_words_bank1)
      )
  );

  assert property (
    state==SENDING_TYPE |->
      master_write &&
      master_address==PACKET_READER_PACKET_TYPE_ADDRESS &&
      master_writedata==0
  );

  assert property (
    state==SENDING_GO_AND_ENABLE_INTERRUPT |->
      master_write &&
      master_address==PACKET_READER_GO_ADDRESS &&
      master_writedata==3
  );

  // Interrupt clear behavior in WAITING_END_FRAME
  assert property (
    state==WAITING_END_FRAME && !master_interrupt_recieve |->
      !master_write &&
      master_address==PACKET_READER_INTERRUPT_ADDRESS &&
      master_writedata==2
  );

  assert property (
    state==WAITING_END_FRAME && master_interrupt_recieve |->
      master_write &&
      master_address==PACKET_READER_INTERRUPT_ADDRESS &&
      master_writedata==2
  );

  // do_control_packet usage
  assert property (do_control_packet |-> state==SENDING_ADDRESS);
  assert property (state==SENDING_ADDRESS |=> !do_control_packet);

  // running behavior: high throughout active sequence, low in idle when not starting
  assert property ((state inside {SENDING_ADDRESS,SENDING_SAMPLES,SENDING_WORDS,SENDING_TYPE,SENDING_GO_AND_ENABLE_INTERRUPT,WAITING_END_FRAME}) |-> running);
  assert property (state==IDLE && !go_bit |-> !running);

  // frame_complete pulse only on interrupt servicing and for one cycle
  assert property (state==WAITING_END_FRAME && master_interrupt_recieve |-> frame_complete);
  assert property (frame_complete |-> $past(state==WAITING_END_FRAME && master_interrupt_recieve) && state==IDLE);
  assert property (frame_complete |=> !frame_complete);

  // Minimal functional coverage
  cover property (
    state==IDLE && go_bit && next_bank==1'b0 ##1
    state==SENDING_ADDRESS ##1
    state==SENDING_SAMPLES ##1
    state==SENDING_WORDS ##1
    state==SENDING_TYPE ##1
    state==SENDING_GO_AND_ENABLE_INTERRUPT ##1
    state==WAITING_END_FRAME ##[1:50]
    (state==WAITING_END_FRAME && master_interrupt_recieve) ##1
    state==IDLE
  );

  cover property (
    state==IDLE && go_bit && next_bank==1'b1 ##1
    state==SENDING_ADDRESS ##1
    state==SENDING_SAMPLES ##1
    state==SENDING_WORDS ##1
    state==SENDING_TYPE ##1
    state==SENDING_GO_AND_ENABLE_INTERRUPT ##1
    state==WAITING_END_FRAME ##[1:50]
    (state==WAITING_END_FRAME && master_interrupt_recieve) ##1
    state==IDLE
  );

  cover property (state==SENDING_ADDRESS && do_control_packet ##1 state==SENDING_SAMPLES && !do_control_packet);
  cover property (frame_complete);

endmodule

// Bind into DUT; connects to internal state and bank_to_read
bind alt_vipvfr131_vfr_controller
  alt_vipvfr131_vfr_controller_asserts #(
    .MASTER_ADDRESS_WIDTH(MASTER_ADDRESS_WIDTH),
    .MASTER_DATA_WIDTH(MASTER_DATA_WIDTH),
    .CONTROL_PACKET_RESOLUTION_REQUIREDWIDTH(CONTROL_PACKET_RESOLUTION_REQUIREDWIDTH),
    .CONTROL_PACKET_INTERLACED_REQUIREDWIDTH(CONTROL_PACKET_INTERLACED_REQUIREDWIDTH),
    .PACKET_ADDRESS_WIDTH(PACKET_ADDRESS_WIDTH),
    .PACKET_SAMPLES_WIDTH(PACKET_SAMPLES_WIDTH),
    .PACKET_WORDS_WIDTH(PACKET_WORDS_WIDTH)
  ) vfr_ctrl_sva (
    .clock(clock),
    .reset(reset),

    .master_address(master_address),
    .master_write(master_write),
    .master_writedata(master_writedata),
    .master_interrupt_recieve(master_interrupt_recieve),

    .go_bit(go_bit),
    .next_bank(next_bank),

    .ctrl_packet_width_bank0(ctrl_packet_width_bank0),
    .ctrl_packet_height_bank0(ctrl_packet_height_bank0),
    .ctrl_packet_interlaced_bank0(ctrl_packet_interlaced_bank0),

    .vid_packet_base_address_bank0(vid_packet_base_address_bank0),
    .vid_packet_samples_bank0(vid_packet_samples_bank0),
    .vid_packet_words_bank0(vid_packet_words_bank0),

    .ctrl_packet_width_bank1(ctrl_packet_width_bank1),
    .ctrl_packet_height_bank1(ctrl_packet_height_bank1),
    .ctrl_packet_interlaced_bank1(ctrl_packet_interlaced_bank1),

    .vid_packet_base_address_bank1(vid_packet_base_address_bank1),
    .vid_packet_samples_bank1(vid_packet_samples_bank1),
    .vid_packet_words_bank1(vid_packet_words_bank1),

    .width_of_next_vid_packet(width_of_next_vid_packet),
    .height_of_next_vid_packet(height_of_next_vid_packet),
    .interlaced_of_next_vid_packet(interlaced_of_next_vid_packet),
    .do_control_packet(do_control_packet),

    .running(running),
    .frame_complete(frame_complete),

    .state(state),
    .bank_to_read(bank_to_read)
  );