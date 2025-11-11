// SVA for autoasciienum_onehot
module autoasciienum_onehot_sva
  #(parameter int IDLE=0, S1=1, S2=2, S3=3, DONE=4)
  (input  logic        clk,
   input  logic        rst_n,
   input  logic [4:0]  cur_state,
   input  logic [4:0]  nxt_state,
   input  logic        ack,
   input  logic [31:0] cur_state_ascii);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  localparam logic [4:0] IDLE_V = (5'b1<<IDLE);
  localparam logic [4:0] S1_V   = (5'b1<<S1);
  localparam logic [4:0] S2_V   = (5'b1<<S2);
  localparam logic [4:0] S3_V   = (5'b1<<S3);
  localparam logic [4:0] DONE_V = (5'b1<<DONE);

  // Async reset drives IDLE onehot
  assert property (@(posedge clk or negedge rst_n) !rst_n |-> cur_state == IDLE_V);

  // No X/Z on key signals after reset deasserts
  assert property (!$isunknown({cur_state, nxt_state, ack, cur_state_ascii}));

  // Onehot encoding enforced
  assert property ($onehot(cur_state));
  assert property ($onehot(nxt_state));

  // Clocked state transitions
  assert property (cur_state[IDLE] |=> cur_state == S1_V);
  assert property (cur_state[S1]   |=> cur_state == S2_V);
  assert property (cur_state[S2]   |=> cur_state == S3_V);
  assert property (cur_state[S3]   |=> cur_state == DONE_V);
  assert property (cur_state[DONE] |=> cur_state == DONE_V);

  // Combinational next-state mapping
  assert property (cur_state[IDLE] |-> nxt_state == S1_V);
  assert property (cur_state[S1]   |-> nxt_state == S2_V);
  assert property (cur_state[S2]   |-> nxt_state == S3_V);
  assert property (cur_state[S3]   |-> nxt_state == DONE_V);
  assert property (cur_state[DONE] |-> nxt_state == DONE_V);

  // ACK behavior
  assert property (ack == cur_state[DONE]);
  assert property ($rose(ack) |-> ($past(cur_state[S3]) && cur_state[DONE]));
  assert property (ack |=> ack); // sticky after DONE

  // ASCII decode matches state
  assert property (cur_state[IDLE] |-> cur_state_ascii == "idle");
  assert property (cur_state[S1]   |-> cur_state_ascii == "s1  ");
  assert property (cur_state[S2]   |-> cur_state_ascii == "s2  ");
  assert property (cur_state[S3]   |-> cur_state_ascii == "s3  ");
  assert property (cur_state[DONE] |-> cur_state_ascii == "done");
  // Illegal encoding maps to "%Err" (guard against multi/zero-hot even though onehot is asserted)
  assert property (!$onehot(cur_state) |-> cur_state_ascii == "%Err");

  // Coverage
  cover property (cur_state == IDLE_V ##1 cur_state == S1_V ##1 cur_state == S2_V ##1 cur_state == S3_V ##1 cur_state == DONE_V);
  cover property ($rose(ack));
  cover property (cur_state_ascii == "idle");
  cover property (cur_state_ascii == "s1  ");
  cover property (cur_state_ascii == "s2  ");
  cover property (cur_state_ascii == "s3  ");
  cover property (cur_state_ascii == "done");

endmodule

// Bind into DUT
bind autoasciienum_onehot autoasciienum_onehot_sva
  i_autoasciienum_onehot_sva(.clk(clk),
                              .rst_n(rst_n),
                              .cur_state(cur_state),
                              .nxt_state(nxt_state),
                              .ack(ack),
                              .cur_state_ascii(cur_state_ascii));