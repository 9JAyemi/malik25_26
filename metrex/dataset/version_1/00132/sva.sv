// SVA checker for simple_calculator
module simple_calculator_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       op,
  input logic [3:0] Z
);

  // helpers
  function automatic logic [3:0] add4(input logic [3:0] a,b);
    add4 = (a + b) & 4'hF;
  endfunction
  function automatic logic [3:0] sub4(input logic [3:0] a,b);
    sub4 = (a - b) & 4'hF;
  endfunction
  function automatic logic add_carry(input logic [3:0] a,b);
    logic [4:0] s;
    begin s = {1'b0,a} + {1'b0,b}; add_carry = s[4]; end
  endfunction
  function automatic logic sub_borrow(input logic [3:0] a,b);
    logic [4:0] d;
    begin d = {1'b0,a} - {1'b0,b}; sub_borrow = d[4]; end
  endfunction

  // correctness (combinational, zero-delay after input change)
  property p_comb_correct;
    @(A or B or op)
      disable iff ($isunknown({A,B,op}))
      1 |-> ##0 (Z === (op ? sub4(A,B) : add4(A,B)));
  endproperty
  assert property (p_comb_correct);

  // output must be known when inputs are known
  property p_known_out_when_known_in;
    @(A or B or op)
      disable iff ($isunknown({A,B,op}))
      1 |-> ##0 (!$isunknown(Z));
  endproperty
  assert property (p_known_out_when_known_in);

  // basic op mode coverage
  cover property (@(A or B or op) !($isunknown({A,B,op})) && (op==1'b0));
  cover property (@(A or B or op) !($isunknown({A,B,op})) && (op==1'b1));

  // interesting arithmetic corner coverage
  cover property (@(A or B or op) !($isunknown({A,B,op})) && (op==1'b0) && add_carry(A,B)); // add overflow
  cover property (@(A or B or op) !($isunknown({A,B,op})) && (op==1'b1) && sub_borrow(A,B)); // sub borrow
  cover property (@(A or B or op) !($isunknown({A,B,op})) && (op==1'b0) && (B==4'h0));       // add identity
  cover property (@(A or B or op) !($isunknown({A,B,op})) && (op==1'b1) && (A==B));         // sub to zero

endmodule

// Bind into the DUT
bind simple_calculator simple_calculator_sva u_simple_calculator_sva (.A(A), .B(B), .op(op), .Z(Z));