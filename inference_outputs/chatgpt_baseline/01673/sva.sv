module FSM_sva #(
  parameter int n = 2,
  parameter int m = 1
)(
  input  logic [n-1:0] in,
  input  logic [m-1:0] out,
  input  logic clk,
  input  logic rst,
  input  logic [1:0] state
);
  // Local copies of encodings used in RTL
  localparam logic [1:0] S0 = 2'b00;
  localparam logic [1:0] S1 = 2'b01;
  localparam logic [1:0] S2 = 2'b10;
  localparam logic [1:0] S3 = 2'b11;

  ///// Reset behavior /////
  // While reset is asserted low, state=S0 and out=0.
  reset_values_hold: assert property (
    @(posedge clk) !rst |-> (state == S0) && (out == 1'b0)
  );
  // On reset falling edge, state and out clear immediately.
  reset_edge_clears: assert property (
    @(posedge clk) $fell(rst) |-> (state == S0) && (out == 1'b0)
  );

  ///// Output function (independent of state) /////
  // If in==01, out must be 1 on the next cycle.
  out_next_one_on_i1: assert property (
    @(posedge clk) disable iff (~rst) (in == 2'b01) |=> (out == 1'b1)
  );
  // If in!=01, out must be 0 on the next cycle.
  out_next_zero_on_not_i1: assert property (
    @(posedge clk) disable iff (~rst) (in != 2'b01) |=> (out == 1'b0)
  );
  // Out is never X/Z when not in reset.
  out_never_x: assert property (
    @(posedge clk) disable iff (~rst) !$isunknown(out)
  );

  ///// State transition function (per RTL case) /////
  // From S0 with in==00, go to S1 and out=0 next cycle.
  s0_i0_next_s1_o0: assert property (
    @(posedge clk) disable iff (~rst) (state == S0 && in == 2'b00) |=> (state == S1 && out == 1'b0)
  );
  // From S0 with in==01, go to S2 and out=1 next cycle.
  s0_i1_next_s2_o1: assert property (
    @(posedge clk) disable iff (~rst) (state == S0 && in == 2'b01) |=> (state == S2 && out == 1'b1)
  );
  // From S0 with in==10/11, stay S0 and out=0 next cycle.
  s0_other_next_s0_o0: assert property (
    @(posedge clk) disable iff (~rst) (state == S0 && (in != 2'b00) && (in != 2'b01)) |=> (state == S0 && out == 1'b0)
  );

  // From S1 with in==00, go to S2 and out=0 next cycle.
  s1_i0_next_s2_o0: assert property (
    @(posedge clk) disable iff (~rst) (state == S1 && in == 2'b00) |=> (state == S2 && out == 1'b0)
  );
  // From S1 with in==01, go to S3 and out=1 next cycle.
  s1_i1_next_s3_o1: assert property (
    @(posedge clk) disable iff (~rst) (state == S1 && in == 2'b01) |=> (state == S3 && out == 1'b1)
  );
  // From S1 with in==10/11, stay S1 and out=0 next cycle.
  s1_other_next_s1_o0: assert property (
    @(posedge clk) disable iff (~rst) (state == S1 && (in != 2'b00) && (in != 2'b01)) |=> (state == S1 && out == 1'b0)
  );

  // From S2 with in==00, go to S3 and out=0 next cycle.
  s2_i0_next_s3_o0: assert property (
    @(posedge clk) disable iff (~rst) (state == S2 && in == 2'b00) |=> (state == S3 && out == 1'b0)
  );
  // From S2 with in==01, go to S0 and out=1 next cycle.
  s2_i1_next_s0_o1: assert property (
    @(posedge clk) disable iff (~rst) (state == S2 && in == 2'b01) |=> (state == S0 && out == 1'b1)
  );
  // From S2 with in==10/11, stay S2 and out=0 next cycle.
  s2_other_next_s2_o0: assert property (
    @(posedge clk) disable iff (~rst) (state == S2 && (in != 2'b00) && (in != 2'b01)) |=> (state == S2 && out == 1'b0)
  );

  // From S3 with in==00, go to S0 and out=0 next cycle.
  s3_i0_next_s0_o0: assert property (
    @(posedge clk) disable iff (~rst) (state == S3 && in == 2'b00) |=> (state == S0 && out == 1'b0)
  );
  // From S3 with in==01, go to S1 and out=1 next cycle.
  s3_i1_next_s1_o1: assert property (
    @(posedge clk) disable iff (~rst) (state == S3 && in == 2'b01) |=> (state == S1 && out == 1'b1)
  );
  // From S3 with in==10/11, stay S3 and out=0 next cycle.
  s3_other_next_s3_o0: assert property (
    @(posedge clk) disable iff (~rst) (state == S3 && (in != 2'b00) && (in != 2'b01)) |=> (state == S3 && out == 1'b0)
  );

endmodule