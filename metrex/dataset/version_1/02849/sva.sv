module fifo_sva #(
  parameter int SIZE = 20,
  parameter int INDEX_WIDTH = 8,
  parameter int MAX_INDEX = SIZE*8 - 1
)(
  input  logic                   clk,
  input  logic                   reset_n,
  input  logic [7:0]             din,
  input  logic                   din_valid,
  input  logic [7:0]             dout,
  input  logic                   indicator,
  input  logic [2:0]             state,
  input  logic [2:0]             next_state,
  input  logic [MAX_INDEX:0]     queue,
  input  logic [MAX_INDEX:0]     next_queue,
  input  logic [INDEX_WIDTH-1:0] head,
  input  logic [INDEX_WIDTH-1:0] next_head,
  input  logic [6:0]             count,
  input  logic [6:0]             next_count
);

  // Mirror DUT encodings
  localparam int WAITING     = 0;
  localparam int RECEIVING   = 1;
  localparam int LEFT_PADDING= 2;
  localparam int TRANSFERING = 3;
  localparam int RIGHT_PADDING=4;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // Registering follows next_* (combinational "next" logic consistency)
  assert property ($past(reset_n) |-> (state==$past(next_state) && head==$past(next_head) &&
                                       count==$past(next_count) && queue==$past(next_queue)));

  // Reset values
  assert property (!reset_n |-> (state==WAITING && head==0 && count==0 && queue==0));

  // Head alignment (byte aligned) and legal range for variable part-select
  assert property (head[2:0]==3'b000);
  assert property (head <= MAX_INDEX+1);

  // State/output indicator semantics
  assert property (state==WAITING      |-> indicator==1'b0);
  assert property (state==LEFT_PADDING |-> indicator==1'b0);
  assert property (state==RIGHT_PADDING|-> indicator==1'b0);
  assert property (state==RECEIVING    |-> indicator==!din_valid);
  assert property (state==TRANSFERING  |-> indicator==((count==7) && (head==8)));

  // dout behavior
  assert property (head==0 |-> dout==8'h00);
  assert property (state==LEFT_PADDING |-> $stable(dout));
  assert property (state==TRANSFERING && count<7 |-> $stable(dout));

  // WAITING transitions
  assert property (state==WAITING && din_valid   |=> state==RECEIVING && head==8 && count==0);
  assert property (state==WAITING && !din_valid  |=> state==WAITING   && head==0 && count==0);

  // RECEIVING transitions
  assert property (state==RECEIVING && din_valid  |=> state==RECEIVING && head==$past(head)+8 && count==0);
  assert property (state==RECEIVING && !din_valid |=> state==LEFT_PADDING && head==$past(head) && count==0);

  // LEFT_PADDING behavior: 80 cycles, head/queue stable
  assert property (state==LEFT_PADDING && $past(state)!=LEFT_PADDING |-> count==0);
  assert property (state==LEFT_PADDING && count<79 |=> state==LEFT_PADDING && count==$past(count)+1);
  assert property (state==LEFT_PADDING && count==79 |=> state==TRANSFERING && count==0);
  assert property (state==LEFT_PADDING |-> $stable(head) && $stable(queue));

  // TRANSFERING invariants and stepping
  assert property (state==TRANSFERING |-> count<=7 && head>=8);
  assert property (state==TRANSFERING && count<7 |=> state==TRANSFERING && count==$past(count)+1 && head==$past(head));
  assert property (state==TRANSFERING && count==7 && head>8 |=> state==TRANSFERING && count==0 && head==$past(head)-8);
  assert property (state==TRANSFERING && count==7 && head==8 |=> state==RIGHT_PADDING && count==0 && head==0);

  // RIGHT_PADDING behavior: 16 cycles, clear queue/head, then WAITING
  assert property (state==RIGHT_PADDING |-> head==0);
  // queue forced to 0 one cycle after entry
  assert property (state==RIGHT_PADDING && $past(state)!=RIGHT_PADDING |=> queue==0);
  assert property (state==RIGHT_PADDING && count<15 |=> state==RIGHT_PADDING && count==$past(count)+1);
  assert property (state==RIGHT_PADDING && count==15 |=> state==WAITING && count==0 && head==0 && queue==0);

  // Optional environment constraint: prevent overfilling burst beyond SIZE bytes
  // Once full (head==MAX_INDEX+1) while still RECEIVING, the next cycle must end the burst.
  assume property (state==RECEIVING && head==MAX_INDEX+1 && din_valid |-> ##1 !din_valid);

  // Functional coverage
  cover property (state==RECEIVING && head>=24 && !din_valid ##1 state==LEFT_PADDING ##1
                  state==TRANSFERING ##[1:$] state==RIGHT_PADDING ##1 state==WAITING);

  cover property (state==RECEIVING && !din_valid && indicator);
  cover property (state==TRANSFERING && count==7 && head==8 && indicator);

  cover property (state==LEFT_PADDING && count==79 ##1 state==TRANSFERING);
  cover property (state==RIGHT_PADDING && count==15 ##1 state==WAITING);

endmodule

// Bind into DUT (connects to internal regs/nets)
bind fifo fifo_sva #(.SIZE(SIZE), .INDEX_WIDTH(INDEX_WIDTH), .MAX_INDEX(MAX_INDEX)) fifo_sva_i (
  .clk(clk),
  .reset_n(reset_n),
  .din(din),
  .din_valid(din_valid),
  .dout(dout),
  .indicator(indicator),
  .state(state),
  .next_state(next_state),
  .queue(queue),
  .next_queue(next_queue),
  .head(head),
  .next_head(next_head),
  .count(count),
  .next_count(next_count)
);