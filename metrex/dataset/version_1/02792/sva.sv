// SVA checker for fifo_counter. Provide a sampling clock from your TB (sva_clk).
module fifo_counter_sva #(bit COV = 1) (
  input  logic        clk,
  input  logic        empty,
  input  logic        ge2_free,
  input  logic        ge3_free,
  input  logic [1:0]  input_tm_cnt,
  input  logic [4:0]  fifo_cnt_inc
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [4:0] exp_val(
    logic        empty_i,
    logic        ge2_i,
    logic        ge3_i,
    logic [1:0]  cnt_i
  );
    if (empty_i)                      exp_val = {3'b000, cnt_i};
    else if (ge3_i && (cnt_i==2'd3))  exp_val = 5'd2;
    else if (ge2_i && (cnt_i>=2))     exp_val = 5'd1;
    else if (cnt_i>=1)                exp_val = 5'd0;
    else                              exp_val = 5'd31;
  endfunction

  // No X/Zs on critical signals
  a_known:  assert property (!$isunknown({empty,ge2_free,ge3_free,input_tm_cnt,fifo_cnt_inc})));

  // Golden functional equivalence (concise, covers full truth table)
  a_func:   assert property (fifo_cnt_inc == exp_val(empty, ge2_free, ge3_free, input_tm_cnt));

  // Sanity range check (should only be 0,1,2,3,31)
  a_range:  assert property (fifo_cnt_inc inside {5'd0,5'd1,5'd2,5'd3,5'd31});

  // Else-branch invert check: 31 occurs only for !empty && cnt==0
  a_31_only_when: assert property ((fifo_cnt_inc==5'd31) |-> (!empty && input_tm_cnt==2'd0));

  // Optional coverage of each decision path and key priority overlap
  if (COV) begin
    // empty path (all cnt values)
    c_empty_0: cover property (empty && input_tm_cnt==2'd0 && fifo_cnt_inc==5'd0);
    c_empty_1: cover property (empty && input_tm_cnt==2'd1 && fifo_cnt_inc==5'd1);
    c_empty_2: cover property (empty && input_tm_cnt==2'd2 && fifo_cnt_inc==5'd2);
    c_empty_3: cover property (empty && input_tm_cnt==2'd3 && fifo_cnt_inc==5'd3);

    // ge3_free path
    c_ge3:     cover property (!empty && ge3_free && input_tm_cnt==2'd3 && fifo_cnt_inc==5'd2);

    // ge2_free path (both cnt=2 and cnt=3 when ge3_free is low)
    c_ge2_2:   cover property (!empty && ge2_free && !ge3_free && input_tm_cnt==2'd2 && fifo_cnt_inc==5'd1);
    c_ge2_3:   cover property (!empty && ge2_free && !ge3_free && input_tm_cnt==2'd3 && fifo_cnt_inc==5'd1);

    // >=1 else path
    c_else_ge1_1: cover property (!empty && input_tm_cnt==2'd1 && fifo_cnt_inc==5'd0);
    c_else_ge1_2: cover property (!empty && !ge2_free && input_tm_cnt==2'd2 && fifo_cnt_inc==5'd0);
    c_else_ge1_3: cover property (!empty && !ge2_free && !ge3_free && input_tm_cnt==2'd3 && fifo_cnt_inc==5'd0);

    // final else path (cnt==0)
    c_else_0:  cover property (!empty && input_tm_cnt==2'd0 && fifo_cnt_inc==5'd31);

    // Priority overlap: when both frees true at cnt=3, ge3_free wins
    c_priority: cover property (!empty && input_tm_cnt==2'd3 && ge3_free && ge2_free && fifo_cnt_inc==5'd2);
  end
endmodule

// Bind into DUT (ensure sva_clk exists in your TB scope)
bind fifo_counter fifo_counter_sva u_fifo_counter_sva (
  .clk          (sva_clk),
  .empty        (empty),
  .ge2_free     (ge2_free),
  .ge3_free     (ge3_free),
  .input_tm_cnt (input_tm_cnt),
  .fifo_cnt_inc (fifo_cnt_inc)
);