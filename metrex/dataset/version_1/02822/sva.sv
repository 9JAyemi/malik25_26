// SVA checker for fifo_counter
// - Samples on user-provided clock
// - Concise full-functional equivalence plus key corner/uniqueness checks
// - Branch coverage

module fifo_counter_sva (
  input logic        clk,
  input logic        rst_n,         // active-low; tie high if unused
  input logic        empty,
  input logic        free2,
  input logic        free3,
  input logic [1:0]  tm_count,
  input logic [4:0]  fifocount_inc
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  function automatic [4:0] exp_inc(
    input logic empty_i, free2_i, free3_i,
    input logic [1:0] tm_i
  );
    if (empty_i)                           exp_inc = {3'b000, tm_i};
    else if (free3_i && (tm_i == 2'b11))   exp_inc = 5'd2;
    else if (free2_i && (tm_i >= 2))       exp_inc = 5'd1;
    else if (tm_i >= 1)                    exp_inc = 5'd0;
    else                                   exp_inc = 5'd31;
  endfunction

  // Inputs/outputs must be known at sample
  assert property (!$isunknown({empty, free2, free3, tm_count})))
    else $error("fifo_counter: inputs X/Z");
  assert property (!$isunknown(fifocount_inc))
    else $error("fifo_counter: output X/Z");

  // Golden functional equivalence (covers all priority/branches)
  assert property (fifocount_inc == exp_inc(empty, free2, free3, tm_count))
    else $error("fifo_counter: output mismatch");

  // Structural/uniqueness checks
  assert property ( empty |-> (fifocount_inc[4:2] == 3'b000
                               && fifocount_inc[1:0] == tm_count))
    else $error("fifo_counter: empty path not zero-extended tm_count");

  assert property (!empty |-> (fifocount_inc inside {5'd0,5'd1,5'd2,5'd31}))
    else $error("fifo_counter: non-empty produced illegal value");

  // 31 is unique to non-empty and tm_count==0
  assert property (fifocount_inc == 5'd31 |-> (!empty && tm_count == 2'd0))
    else $error("fifo_counter: 31 only allowed when !empty && tm_count==0");

  // Priority sanity: when both free3 and free2 conditions could match, free3 wins
  assert property (!empty && free3 && tm_count==2'd3 && free2 |-> fifocount_inc == 5'd2)
    else $error("fifo_counter: priority error (free3 case)");

  // Branch coverage: hit each guarded path with correct result
  cover property ( empty && (fifocount_inc == {3'b000, tm_count}) );
  cover property (!empty && free3 && (tm_count==2'd3) && (fifocount_inc==5'd2));
  cover property (!empty && !free3 && free2 && (tm_count>=2) && (fifocount_inc==5'd1));
  cover property (!empty && !free3 && (!free2 || tm_count<2) && (tm_count>=1) && (fifocount_inc==5'd0));
  cover property (!empty && (tm_count==2'd0) && (fifocount_inc==5'd31));

endmodule

// Bind example (hook clk/rst_n from your environment)
// bind fifo_counter fifo_counter_sva u_fifo_counter_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));