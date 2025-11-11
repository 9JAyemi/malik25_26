// SVA monitor for floating_point_arithmetic
// Bind example (modify clock/reset names as needed):
// bind floating_point_arithmetic floating_point_arithmetic_sva u_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));

module floating_point_arithmetic_sva (
  input logic              clk,
  input logic              rst_n,
  input logic [31:0]       a,
  input logic [31:0]       b,
  input logic [1:0]        ctrl,
  input logic [31:0]       result
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Helpers
  function automatic bit known32 (logic [31:0] v); return !$isunknown(v); endfunction
  function automatic bit known_all (logic [65:0] v); return !$isunknown(v); endfunction

  // Basic sanity: inputs known => result known (except div-by-zero case)
  assert property ( known_all({a,b,ctrl}) && !(ctrl==2'b11 && b==32'b0) |-> known32(result) )
    else $error("Result contains X/Z with known inputs (and not div-by-zero)");

  // Default branch behavior: any X/Z in ctrl must drive result to 0
  assert property ( $isunknown(ctrl) |-> result==32'b0 )
    else $error("Default branch violated: ctrl has X/Z but result != 0");

  // Functional correctness per operation
  assert property ( known_all({a,b,ctrl}) && ctrl==2'b00 |-> result == (a + b) )
    else $error("ADD mismatch: result != a+b");

  assert property ( known_all({a,b,ctrl}) && ctrl==2'b01 |-> result == (a - b) )
    else $error("SUB mismatch: result != a-b");

  assert property ( known_all({a,b,ctrl}) && ctrl==2'b10 |-> result == (a * b) )
    else $error("MUL mismatch: result != a*b");

  assert property ( known_all({a,b,ctrl}) && ctrl==2'b11 && b!=32'b0 |-> result == (a / b) )
    else $error("DIV mismatch (b!=0): result != a/b");

  // Division by zero should produce Xs from Verilog '/'
  assert property ( known_all({a,b,ctrl}) && ctrl==2'b11 && b==32'b0 |-> $isunknown(result) )
    else $error("DIV by zero should yield X/Z result");

  // Combinational stability: when inputs stable, result stable
  assert property ( $stable({a,b,ctrl}) |-> $stable(result) )
    else $error("Combinational instability: result changed while inputs stable");

  // Result changes only when inputs change
  assert property ( !$stable(result) |-> !$stable({a,b,ctrl}) )
    else $error("Result changed without input change");

  // Coverage: exercise all operations and div-by-zero
  cover property ( ctrl==2'b00 && known_all({a,b,ctrl}) );
  cover property ( ctrl==2'b01 && known_all({a,b,ctrl}) );
  cover property ( ctrl==2'b10 && known_all({a,b,ctrl}) );
  cover property ( ctrl==2'b11 && b!=32'b0 && known_all({a,b,ctrl}) );
  cover property ( ctrl==2'b11 && b==32'b0 && known_all({a,b,ctrl}) );

  // A few interesting operand patterns (bit-level, since DUT is not real IEEE-754)
  cover property ( ctrl==2'b00 && a==32'h0000_0000 && b==32'h0000_0000 );
  cover property ( ctrl==2'b01 && a==32'hFFFF_FFFF && b==32'h0000_0001 );
  cover property ( ctrl==2'b10 && a==32'h8000_0000 && b==32'h0000_0002 );
  cover property ( ctrl==2'b11 && b==32'h0000_0001 );

endmodule