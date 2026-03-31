```systemverilog
module fifo_controller_sva (
  input wire ge2_free,
  input wire ge3_free,
  input wire [1:0] input_tm_cnt,
  output reg [3:0] fifo_wrptr_inc
);
  // Sequential logic, no clock signal present

  // fifo_wrptr_inc should be 0 when ge3_free and input_tm_cnt is not 3
  property p_fifo_wrptr_inc_0;
    @(posedge ge3_free) disable iff (!ge3_free) fifo_wrptr_inc == 4'd0;
  endproperty
  assert property (p_fifo_wrptr_inc_0) else $error("fifo_wrptr_inc should be 0 when ge3_free and input_tm_cnt is not 3");

  // fifo_wrptr_inc should be 3 when ge3_free and input_tm_cnt is 3
  property p_fifo_wrptr_inc_3;
    @(posedge ge3_free) disable iff (!ge3_free) (ge3_free && (input_tm_cnt == 2'd3)) |-> fifo_wrptr_inc == 4'd3;
  endproperty
  assert property (p_fifo_wrptr_inc_3) else $error("fifo_wrptr_inc should be 3 when ge3_free and input_tm_cnt is 3");

  // fifo_wrptr_inc should be 2 when ge2_free and input_tm_cnt is greater than or equal to 2
  property p_fifo_wrptr_inc_2;
    @(posedge ge2_free) disable iff (!ge2_free) (ge2_free && (input_tm_cnt >= 2'd2)) |-> fifo_wrptr_inc == 4'd2;
  endproperty
  assert property (p_fifo_wrptr_inc_2) else $error("fifo_wrptr_inc should be 2 when ge2_free and input_tm_cnt is greater than or equal to 2");

  // fifo_wrptr_inc should be 1 when input_tm_cnt is greater than or equal to 1
  property p_fifo_wrptr_inc_1;
    @(posedge input_tm_cnt) disable iff (!input_tm_cnt) (input_tm_cnt >= 2'd1) |-> fifo_wrptr_inc == 4'd1;
  endproperty
  assert property (p_fifo_wrptr_inc_1) else $error("fifo_wrptr_inc should be 1 when input_tm_cnt is greater than or equal to 1");

  // fifo_wrptr_inc should be 0 when input_tm_cnt is less than 1
  property p_fifo_wrptr_inc_0;
    @(posedge input_tm_cnt) disable iff (!input_tm_cnt) (input_tm_cnt < 2'd1) |-> fifo_wrptr_inc == 4'd0;
  endproperty
  assert property (p_fifo_wrptr_inc_0) else $error("fifo_wrptr_inc should be 0 when input_tm_cnt is less than 1");

endmodule
```