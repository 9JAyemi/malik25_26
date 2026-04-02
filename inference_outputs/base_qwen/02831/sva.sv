module flip_flop_sva (
  input logic clk,
  input logic rst,
  input logic data,
  input logic type,
  output logic q,
  output logic q_bar
);
  // Reset behavior: q and q_bar should be 1'b1 and 1'b0 respectively for type 1 or 3, and vice versa for type 0 or 2
  reset_behavior: assert property (
    @(posedge clk) disable iff (!rst) (type == 1 || type == 3) |-> (q == 1'b1 && q_bar == 1'b0)
  ) else $error("Reset behavior violated for type 1 or 3");

  reset_behavior_2: assert property (
    @(posedge clk) disable iff (!rst) (type == 0 || type == 2) |-> (q == 1'b0 && q_bar == 1'b1)
  ) else $error("Reset behavior violated for type 0 or 2");

  // D flip-flop behavior: q should be equal to data and q_bar should be the complement of data
  d_flip_flop: assert property (
    @(posedge clk) disable iff (!rst) (type == 0) |-> (q == data && q_bar == ~data)
  ) else $error("D flip-flop behavior violated");

  // JK flip-flop behavior: q should toggle when data is 1 and q_bar should toggle when data is 1
  jk_flip_flop: assert property (
    @(posedge clk) disable iff (!rst) (type == 1) |-> (data |-> (q != q_bar))
  ) else $error("JK flip-flop behavior violated");

  // T flip-flop behavior: q should toggle when data is 1
  t_flip_flop: assert property (
    @(posedge clk) disable iff (!rst) (type == 2) |-> (data |-> (q != q_bar))
  ) else $error("T flip-flop behavior violated");

  // SR flip-flop behavior: q should be 1'b1 and q_bar should be 1'b0 when data is 1, and vice versa when data is 0
  sr_flip_flop: assert property (
    @(posedge clk) disable iff (!rst) (type == 3) |-> (data |-> (q == 1'b1 && q_bar == 1'b0)) && (!data |-> (q == 1'b0 && q_bar == 1'b1))
  ) else $error("SR flip-flop behavior violated");
endmodule