// SVA for nukv_Read
// Bind this module to the DUT to check protocol, state-machine, and data/addr behavior.

module nukv_Read_sva #(
  parameter KEY_WIDTH = 128,
  parameter META_WIDTH = 96,
  parameter HASHADDR_WIDTH = 32,
  parameter MEMADDR_WIDTH = 20
)(
  input  logic clk,
  input  logic rst,

  // DUT primary I/O we observe
  input  logic [KEY_WIDTH+META_WIDTH+HASHADDR_WIDTH-1:0] input_data,
  input  logic                                           input_valid,
  input  logic                                           input_ready,

  input  logic [KEY_WIDTH+META_WIDTH+HASHADDR_WIDTH-1:0] feedback_data,
  input  logic                                           feedback_valid,
  input  logic                                           feedback_ready,

  input  logic [KEY_WIDTH+META_WIDTH+HASHADDR_WIDTH-1:0] output_data,
  input  logic                                           output_valid,
  input  logic                                           output_ready,

  input  logic [31:0]                                    rdcmd_data,
  input  logic                                           rdcmd_valid,
  input  logic                                           rdcmd_ready,

  input  logic [31:0]                                    mem_data,
  input  logic                                           mem_valid,

  // DUT internal signals (connected via bind to internal names)
  input  logic                                           selectInput,
  input  logic                                           selectInputNext,
  input  logic [2:0]                                     state,
  input  logic [KEY_WIDTH+META_WIDTH+HASHADDR_WIDTH-1:0] in_data,
  input  logic                                           in_valid,
  input  logic                                           in_ready,
  input  logic [31:0]                                    hash_data,
  input  logic [MEMADDR_WIDTH-1:0]                       addr
);

  localparam int ST_IDLE        = 3'd0;
  localparam int ST_ISSUE_READ  = 3'd3;
  localparam int ST_OUTPUT_KEY  = 3'd4;

  localparam int UPPER_HI = KEY_WIDTH+META_WIDTH+HASHADDR_WIDTH-1;
  localparam int UPPER_LO = KEY_WIDTH+META_WIDTH;
  localparam int IGN_BIT  = KEY_WIDTH+META_WIDTH-4;

  // Reset values
  assert property (@(posedge clk) rst |=> (selectInput==1'b1 && selectInputNext==1'b0 &&
                                           state==ST_IDLE && in_ready==1'b0 &&
                                           rdcmd_valid==1'b0 && output_valid==1'b0 && mem_valid==1'b0));

  // Ready routing matches select
  assert property (@(posedge clk) disable iff (rst)  selectInput  |-> (input_ready==in_ready && feedback_ready==1'b0));
  assert property (@(posedge clk) disable iff (rst) !selectInput  |-> (feedback_ready==in_ready && input_ready  ==1'b0));
  assert property (@(posedge clk) disable iff (rst)  selectInput  |-> (in_valid==input_valid));
  assert property (@(posedge clk) disable iff (rst) !selectInput  |-> (in_valid==feedback_valid));
  assert property (@(posedge clk) disable iff (rst) !(input_ready && feedback_ready)); // never both

  // Handshake stickiness
  assert property (@(posedge clk) disable iff (rst) (output_valid && !output_ready) |=> output_valid);
  assert property (@(posedge clk) disable iff (rst) (rdcmd_valid  && !rdcmd_ready)  |=> rdcmd_valid);

  // IDLE stay/leave conditions
  wire cond_can_issue = (output_ready && rdcmd_ready) &&
                        (( selectInput && input_valid) || (!selectInput && feedback_valid));
  assert property (@(posedge clk) disable iff (rst) (state==ST_IDLE && !cond_can_issue) |=> state==ST_IDLE);
  assert property (@(posedge clk) disable iff (rst) (state==ST_IDLE &&  cond_can_issue) |=> state==ST_ISSUE_READ);

  // Ignore-bit: no read or output when set
  assert property (@(posedge clk) disable iff (rst)
                   (state==ST_ISSUE_READ && in_data[IGN_BIT]) |-> (!rdcmd_valid && !output_valid));

  // in_ready only asserted in ISSUE_READ and should only accept when valid
  assert property (@(posedge clk) disable iff (rst) in_ready |-> (state==ST_ISSUE_READ));
  assert property (@(posedge clk) disable iff (rst) in_ready |->  in_valid);

  // Address function equals RTL expression
  assert property (@(posedge clk) disable iff (rst)
                   addr == (hash_data[31:32-MEMADDR_WIDTH] ^ hash_data[MEMADDR_WIDTH-1:0]));

  // rdcmd_data formatting on issue (check at rising edge)
  assert property (@(posedge clk) disable iff (rst)
                   $rose(rdcmd_valid) |-> (rdcmd_data[31:MEMADDR_WIDTH]=='0 && rdcmd_data[MEMADDR_WIDTH-1:0]==$past(addr)));

  // On miss (rdcmd_valid issues), next state is ST_OUTPUT_KEY
  assert property (@(posedge clk) disable iff (rst)
                   $rose(rdcmd_valid) |=> state==ST_OUTPUT_KEY);

  // ST_OUTPUT_KEY outputs only when ready, and tags addr in upper bits
  assert property (@(posedge clk) disable iff (rst)
                   (state==ST_OUTPUT_KEY && !output_ready) |-> !output_valid);
  assert property (@(posedge clk) disable iff (rst)
                   $rose(output_valid) |-> (output_data[UPPER_HI:UPPER_LO] == addr));

  // Output only from ISSUE_READ (hit) or OUTPUT_KEY
  assert property (@(posedge clk) disable iff (rst)
                   output_valid |-> (state==ST_ISSUE_READ || state==ST_OUTPUT_KEY));

  // On hit (no ignore, in ISSUE_READ), no read command should be sent
  assert property (@(posedge clk) disable iff (rst)
                   (state==ST_ISSUE_READ && !in_data[IGN_BIT] && output_valid) |-> !rdcmd_valid);

  // Basic coverage
  cover property (@(posedge clk) disable iff (rst)
                  state==ST_IDLE ##1 cond_can_issue ##1 state==ST_ISSUE_READ);
  cover property (@(posedge clk) disable iff (rst)
                  state==ST_ISSUE_READ && !in_data[IGN_BIT] && output_valid); // hit path
  cover property (@(posedge clk) disable iff (rst)
                  $rose(rdcmd_valid) ##[1:10] $rose(output_valid));          // miss path
  cover property (@(posedge clk) disable iff (rst)
                  state==ST_ISSUE_READ && in_data[IGN_BIT]);                 // ignore path
  cover property (@(posedge clk) disable iff (rst)
                  selectInput && input_valid ##1 !selectInput && feedback_valid); // both sources used

endmodule

// Bind example (instantiate once per nukv_Read)
// Place in a separate bind file or testbench.
// bind nukv_Read nukv_Read_sva #(.KEY_WIDTH(KEY_WIDTH), .META_WIDTH(META_WIDTH), .HASHADDR_WIDTH(HASHADDR_WIDTH), .MEMADDR_WIDTH(MEMADDR_WIDTH))
// ( .clk(clk), .rst(rst),
//   .input_data(input_data), .input_valid(input_valid), .input_ready(input_ready),
//   .feedback_data(feedback_data), .feedback_valid(feedback_valid), .feedback_ready(feedback_ready),
//   .output_data(output_data), .output_valid(output_valid), .output_ready(output_ready),
//   .rdcmd_data(rdcmd_data), .rdcmd_valid(rdcmd_valid), .rdcmd_ready(rdcmd_ready),
//   .mem_data(mem_data), .mem_valid(mem_valid),
//   .selectInput(selectInput), .selectInputNext(selectInputNext), .state(state),
//   .in_data(in_data), .in_valid(in_valid), .in_ready(in_ready), .hash_data(hash_data), .addr(addr) );