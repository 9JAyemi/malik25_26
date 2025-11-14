// SVA checker for arithmetic_module
module arithmetic_module_sva (
  input logic [7:0] A,
  input logic [7:0] B,
  input logic       operation,
  input logic       reset,
  input logic [7:0] C
);

  // Expected combinational behavior (8-bit wrap)
  function automatic logic [7:0] exp_c(logic [7:0] a, b, logic op, rst);
    if (rst) exp_c = 8'h00;
    else     exp_c = op ? (a - b) : (a + b);
  endfunction

  // Core functional check (sampled after NBA to avoid delta-cycle races)
  assert property (@(*) (!$isunknown({A,B,operation,reset}))
                   |-> ##0 (!$isunknown(C) && C == exp_c(A,B,operation,reset)))
    else $error("C mismatch: A=%0h B=%0h op=%0b rst=%0b C=%0h exp=%0h",
                A,B,operation,reset,C,exp_c(A,B,operation,reset));

  // Basic path coverage
  cover property (@(*) reset ##0 (C==8'h00));
  cover property (@(*) !reset && !operation);
  cover property (@(*) !reset &&  operation);

  // Add overflow / no-overflow coverage
  cover property (@(*) !reset && !operation && ({1'b0,A}+{1'b0,B})[8]);
  cover property (@(*) !reset && !operation && !({1'b0,A}+{1'b0,B})[8]);

  // Sub borrow / no-borrow coverage
  cover property (@(*) !reset && operation && ({1'b0,A}-{1'b0,B})[8]);
  cover property (@(*) !reset && operation && !({1'b0,A}-{1'b0,B})[8]);

  // Subtraction resulting in zero
  cover property (@(*) !reset && operation && (A==B) ##0 (C==8'h00));

endmodule

// Bind into the DUT (instance-level or module-level as needed)
bind arithmetic_module arithmetic_module_sva u_arithmetic_module_sva (
  .A(A), .B(B), .operation(operation), .reset(reset), .C(C)
);