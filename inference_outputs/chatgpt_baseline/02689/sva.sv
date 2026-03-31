module bitwise_operators_sva #(
  parameter int n = 4
) (
  input  logic                 CLK,
  input  logic                 RESETn,
  input  logic [n-1:0]         A,
  input  logic [n-1:0]         B,
  input  logic [n-1:0]         and_res,
  input  logic [n-1:0]         or_res,
  input  logic [n-1:0]         xor_res,
  input  logic [n-1:0]         not_res
);

  // and_res equals bitwise AND of A and B.
  check_and_definition: assert property (
    @(posedge CLK) disable iff (!RESETn) and_res == (A & B)
  );

  // or_res equals bitwise OR of A and B.
  check_or_definition: assert property (
    @(posedge CLK) disable iff (!RESETn) or_res == (A | B)
  );

  // xor_res equals bitwise XOR of A and B.
  check_xor_definition: assert property (
    @(posedge CLK) disable iff (!RESETn) xor_res == (A ^ B)
  );

  // not_res equals bitwise NOT of A.
  check_not_definition: assert property (
    @(posedge CLK) disable iff (!RESETn) not_res == (~A)
  );

  // OR equals XOR OR AND.
  check_or_is_xor_or_and: assert property (
    @(posedge CLK) disable iff (!RESETn) or_res == (xor_res | and_res)
  );

  // XOR equals OR masked by NOT AND.
  check_xor_is_or_andmask: assert property (
    @(posedge CLK) disable iff (!RESETn) xor_res == (or_res & ~and_res)
  );

  // AND and XOR are disjoint (no overlapping 1s).
  check_and_xor_disjoint_zero: assert property (
    @(posedge CLK) disable iff (!RESETn) ((and_res & xor_res) == '0)
  );

  // NOT(A) AND A is always zero.
  check_not_and_zero: assert property (
    @(posedge CLK) disable iff (!RESETn) ((not_res & A) == '0)
  );

  // NOT(A) OR A is all ones.
  check_not_or_ones: assert property (
    @(posedge CLK) disable iff (!RESETn) ((not_res | A) == '1)
  );

  // OR covers all 1s present in A.
  check_or_covers_A: assert property (
    @(posedge CLK) disable iff (!RESETn) ((~or_res & A) == '0)
  );

endmodule