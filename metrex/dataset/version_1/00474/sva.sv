// SVA checker for raycast_stack
module raycast_stack_sva #(
  parameter int dw = 32,
  parameter int depth = 8,
  parameter int depth_log2 = 3
)(
  input  logic                      clk,
  input  logic                      push,
  input  logic                      pop,
  input  logic [dw-1:0]             data_i,
  input  logic [dw-1:0]             data_o,
  input  logic [depth_log2-1:0]     stack_ptr
);
  default clocking cb @(posedge clk); endclocking

  localparam int MAX = depth-1;

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Simple reference model (level/top and memory)
  int level;
  logic [dw-1:0] model_mem [0:depth-1];

  // Initialize model
  always_ff @(posedge clk) begin
    if (!past_valid) begin
      level <= 0;
    end else begin
      int delta = push ? 1 : (pop ? -1 : 0);
      int n = level + delta;
      if (n >= 0 && n <= MAX) begin
        level <= n;
        if (push) model_mem[n] <= data_i; // new top after push
      end
    end
  end

  // Sanity/knownness
  assert property (past_valid |-> !$isunknown({push,pop})) else $error("push/pop X");
  assert property (past_valid |-> !$isunknown({stack_ptr,data_o})) else $error("ptr/data_o X");

  // No overflow/underflow (given push has priority over pop)
  assert property (past_valid |-> !(level==MAX && push)) else $error("Overflow");
  assert property (past_valid |-> !(level==0 && !push && pop)) else $error("Underflow");

  // Pointer transitions and priority (push wins)
  assert property (past_valid && $past(push)                         |=> stack_ptr == $past(stack_ptr)+1) else $error("Ptr inc");
  assert property (past_valid && $past(!push && pop)                 |=> stack_ptr == $past(stack_ptr)-1) else $error("Ptr dec");
  assert property (past_valid && $past(!push && !pop)                |=> stack_ptr == $past(stack_ptr)   ) else $error("Ptr hold");
  assert property (past_valid && $past(push && pop)                  |=> stack_ptr == $past(stack_ptr)+1) else $error("Priority");

  // Pointer equals model level
  assert property (past_valid |-> stack_ptr == level) else $error("Ptr != model level");

  // Data correctness
  // After a legal push, top is the pushed data next cycle
  assert property (past_valid && $past(push) && ($past(level) < MAX) |=> data_o == $past(data_i)) else $error("Data after push");
  // After a legal pop, new top matches model below prior top
  assert property (past_valid && $past(!push && pop) && ($past(level) > 0) |=> data_o == model_mem[$past(level)-1]) else $error("Data after pop");
  // Hold when idle
  assert property (past_valid && $past(!push && !pop)                |=> data_o == $past(data_o)) else $error("Data hold");

  // Bounds (defensive)
  assert property (past_valid |-> stack_ptr <= MAX) else $error("Ptr out of range");

  // Coverage
  cover property (past_valid && push);
  cover property (past_valid && pop && !push);
  cover property (past_valid && push && pop);                 // priority case
  cover property (past_valid && level==0);                    // empty
  cover property (past_valid && level==MAX);                  // full
  sequence fill_seq; (push && !pop)[*MAX]; endsequence
  cover property (past_valid ##1 fill_seq ##1 (level==MAX));  // fill to full
  sequence drain_seq; (pop && !push)[*MAX]; endsequence
  cover property (past_valid && level==MAX ##1 drain_seq ##1 (level==0)); // drain to empty
endmodule

// Bind into DUT (connects to internal stack_ptr)
bind raycast_stack raycast_stack_sva #(
  .dw(dw), .depth(depth), .depth_log2(depth_log2)
) i_raycast_stack_sva (
  .clk      (clk),
  .push     (push),
  .pop      (pop),
  .data_i   (data_i),
  .data_o   (data_o),
  .stack_ptr(stack_ptr)
);