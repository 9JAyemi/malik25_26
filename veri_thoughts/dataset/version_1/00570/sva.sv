// SVA checker for fifo_counter
module fifo_counter_sva (
  input  logic        empty,
  input  logic        ge2_free,
  input  logic        ge3_free,
  input  logic [1:0]  input_tm_cnt,
  input  logic [4:0]  fifo_cnt_inc
);
  default clocking cb @($global_clock); endclocking

  function automatic [4:0] exp_cnt (
    input logic       empty_i,
    input logic       ge2_i,
    input logic       ge3_i,
    input logic [1:0] c
  );
    if (empty_i)                           exp_cnt = {3'b000, c};
    else if (ge3_i && (c == 2'b11))        exp_cnt = 5'd2;
    else if (ge2_i && (c >= 2))            exp_cnt = 5'd1;
    else if (c >= 1)                       exp_cnt = 5'd0;
    else                                   exp_cnt = 5'd31;
  endfunction

  // Functional equivalence and X-robustness
  assert property (!$isunknown({empty,ge2_free,ge3_free,input_tm_cnt})
                   |-> (fifo_cnt_inc == exp_cnt(empty,ge2_free,ge3_free,input_tm_cnt)));
  assert property (!$isunknown({empty,ge2_free,ge3_free,input_tm_cnt})
                   |-> !$isunknown(fifo_cnt_inc));

  // Output domain when not empty; and 31 only when !empty && input_tm_cnt==0
  assert property (!empty |-> (fifo_cnt_inc inside {5'd0,5'd1,5'd2,5'd31}));
  assert property ((fifo_cnt_inc == 5'd31) |-> (!empty && input_tm_cnt == 2'd0));

  // Coverage: all branches and key corners
  cover property (empty && (input_tm_cnt==2'd0) && (fifo_cnt_inc==5'd0));
  cover property (empty && (input_tm_cnt==2'd1) && (fifo_cnt_inc==5'd1));
  cover property (empty && (input_tm_cnt==2'd2) && (fifo_cnt_inc==5'd2));
  cover property (empty && (input_tm_cnt==2'd3) && (fifo_cnt_inc==5'd3));

  cover property (!empty && ge3_free && (input_tm_cnt==2'd3) && (fifo_cnt_inc==5'd2));

  cover property (!empty && !ge3_free && ge2_free && (input_tm_cnt==2'd2) && (fifo_cnt_inc==5'd1));
  cover property (!empty && !ge3_free && ge2_free && (input_tm_cnt==2'd3) && (fifo_cnt_inc==5'd1));

  cover property (!empty && (input_tm_cnt==2'd1) && (fifo_cnt_inc==5'd0));
  cover property (!empty && !ge2_free && (input_tm_cnt==2'd2) && (fifo_cnt_inc==5'd0));
  cover property (!empty && !ge3_free && !ge2_free && (input_tm_cnt==2'd3) && (fifo_cnt_inc==5'd0));

  cover property (!empty && (input_tm_cnt==2'd0) && (fifo_cnt_inc==5'd31));
endmodule

bind fifo_counter fifo_counter_sva sva_i (.*);