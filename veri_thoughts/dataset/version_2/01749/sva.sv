module bitwise_operators_sva #(
  parameter int n = 8
)(
  input logic clk,
  input logic [n-1:0] a,
  input logic [n-1:0] b,
  input logic [1:0] ctrl,
  input logic [n-1:0] res
);
  // res equals a & b when ctrl==00
  check_ctrl00_and: assert property (
    @(posedge clk) (ctrl == 2'b00) |=> (res == (a & b))
  );

  // res equals a | b when ctrl==01
  check_ctrl01_or: assert property (
    @(posedge clk) (ctrl == 2'b01) |=> (res == (a | b))
  );

  // res equals a ^ b when ctrl==10
  check_ctrl10_xor: assert property (
    @(posedge clk) (ctrl == 2'b10) |=> (res == (a ^ b))
  );

  // res equals ~a when ctrl==11
  check_ctrl11_not: assert property (
    @(posedge clk) (ctrl == 2'b11) |=> (res == (~a))
  );

  // AND: b==0 drives res==0
  and_zero_when_b_zero: assert property (
    @(posedge clk) (ctrl == 2'b00 && b == {n{1'b0}}) |=> (res == {n{1'b0}})
  );

  // AND: a==0 drives res==0
  and_zero_when_a_zero: assert property (
    @(posedge clk) (ctrl == 2'b00 && a == {n{1'b0}}) |=> (res == {n{1'b0}})
  );

  // AND: b==all1 passes a through
  and_pass_a_when_b_ones: assert property (
    @(posedge clk) (ctrl == 2'b00 && b == {n{1'b1}}) |=> (res == a)
  );

  // OR: b==0 passes a through
  or_pass_a_when_b_zero: assert property (
    @(posedge clk) (ctrl == 2'b01 && b == {n{1'b0}}) |=> (res == a)
  );

  // OR: a==all1 drives res==all1
  or_allones_when_a_ones: assert property (
    @(posedge clk) (ctrl == 2'b01 && a == {n{1'b1}}) |=> (res == {n{1'b1}})
  );

  // XOR: b==0 passes a through
  xor_pass_a_when_b_zero: assert property (
    @(posedge clk) (ctrl == 2'b10 && b == {n{1'b0}}) |=> (res == a)
  );

  // XOR: a==b drives res==0
  xor_zero_when_equal: assert property (
    @(posedge clk) (ctrl == 2'b10 && a == b) |=> (res == {n{1'b0}})
  );
endmodule