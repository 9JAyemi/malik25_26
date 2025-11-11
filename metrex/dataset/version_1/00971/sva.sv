// SVA checker for fifo_controller
module fifo_controller_sva (
  input logic        ge2_free,
  input logic        ge3_free,
  input logic [1:0]  input_tm_cnt,
  input logic [3:0]  fifo_wrptr_inc
);
  default clocking cb @($global_clock); endclocking

  // Range and X-prop checks
  assert property (fifo_wrptr_inc inside {[4'd0:4'd3)});
  assert property ((!$isunknown({ge2_free,ge3_free,input_tm_cnt})) |-> (!$isunknown(fifo_wrptr_inc)));

  // Priority encoder behavior (matches DUT else-if order)
  assert property (ge3_free && (input_tm_cnt == 2'd3) |-> fifo_wrptr_inc == 4'd3);
  assert property (!(ge3_free && (input_tm_cnt == 2'd3)) && ge2_free && (input_tm_cnt >= 2'd2) |-> fifo_wrptr_inc == 4'd2);
  assert property (!(ge3_free && (input_tm_cnt == 2'd3)) && !(ge2_free && (input_tm_cnt >= 2'd2)) && (input_tm_cnt >= 2'd1) |-> fifo_wrptr_inc == 4'd1);
  assert property (!(ge3_free && (input_tm_cnt == 2'd3)) && !(ge2_free && (input_tm_cnt >= 2'd2)) && !(input_tm_cnt >= 2'd1) |-> fifo_wrptr_inc == 4'd0);

  // Concise functional coverage (hit all outcomes and key boundaries)
  cover property (ge3_free && (input_tm_cnt == 2'd3) && fifo_wrptr_inc == 4'd3);
  cover property (!(ge3_free && (input_tm_cnt == 2'd3)) && ge2_free && (input_tm_cnt >= 2'd2) && fifo_wrptr_inc == 4'd2);
  cover property (!(ge3_free && (input_tm_cnt == 2'd3)) && !(ge2_free && (input_tm_cnt >= 2'd2)) && (input_tm_cnt >= 2'd1) && fifo_wrptr_inc == 4'd1);
  cover property ((input_tm_cnt == 2'd0) && fifo_wrptr_inc == 4'd0);

  // Boundary distinctions
  cover property ((input_tm_cnt == 2'd2) &&  ge2_free && fifo_wrptr_inc == 4'd2);
  cover property ((input_tm_cnt == 2'd2) && !ge2_free && fifo_wrptr_inc == 4'd1);
  cover property ((input_tm_cnt == 2'd3) && !ge3_free &&  ge2_free && fifo_wrptr_inc == 4'd2);
  cover property ((input_tm_cnt == 2'd3) && !ge3_free && !ge2_free && fifo_wrptr_inc == 4'd1);
endmodule

// Bind into DUT
bind fifo_controller fifo_controller_sva sva_i (.*);