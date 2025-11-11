// SVA checker for logic_module
// - Asserts functional equivalence
// - Asserts correctness for key minterms (each term solely driving X high)
// - Asserts X is 0 when all terms are false
// - Asserts no X/Z on X when inputs are 0/1
// - Includes concise coverage
//
// Two modes:
//   1) Clocked concurrent SVA (preferred): set CLOCKED=1 and connect clk
//   2) Clockless immediate assertions: set CLOCKED=0 (no clk needed)

module logic_module_sva
#(parameter bit CLOCKED = 1)
(
  input logic clk,      // used only when CLOCKED=1
  input logic A, B, C, D, E, F, G, H,
  input logic X
);

  // Local terms matching DUT structure/function
  wire t_and0  = A & B;
  wire t_or0   = C | D;
  wire t_nand1 = !(E & F);
  wire t_nor1  = !(G | H);

  if (CLOCKED) begin : gen_clocked
    default clocking cb @(posedge clk); endclocking

    // Functional equivalence
    a_func: assert property (X === (t_and0 | t_or0 | t_nand1 | t_nor1));

    // Deterministic low (all terms false)
    a_low:  assert property ((!t_and0 && !t_or0 && !t_nand1 && !t_nor1) |-> (X == 1'b0));

    // Sole-contributor correctness
    a_and0_only:  assert property (( t_and0 && !t_or0 && !t_nand1 && !t_nor1) |-> (X == 1'b1));
    a_or0_only:   assert property ((!t_and0 &&  t_or0 && !t_nand1 && !t_nor1) |-> (X == 1'b1));
    a_nand1_only: assert property ((!t_and0 && !t_or0 &&  t_nand1 && !t_nor1) |-> (X == 1'b1));
    a_nor1_only:  assert property ((!t_and0 && !t_or0 && !t_nand1 &&  t_nor1) |-> (X == 1'b1));

    // No unknown on X when inputs are known
    a_no_x: assert property (!$isunknown({A,B,C,D,E,F,G,H}) |-> !$isunknown(X));

    // Coverage: both X values and each sole-contributor scenario
    c_x0:      cover property (X == 1'b0);
    c_x1:      cover property (X == 1'b1);
    c_and0:    cover property ( t_and0 && !t_or0 && !t_nand1 && !t_nor1);
    c_or0:     cover property (!t_and0 &&  t_or0 && !t_nand1 && !t_nor1);
    c_nand1:   cover property (!t_and0 && !t_or0 &&  t_nand1 && !t_nor1);
    c_nor1:    cover property (!t_and0 && !t_or0 && !t_nand1 &&  t_nor1);

  end else begin : gen_clockless
    // Immediate, clockless checks (safe for purely combinational DUTs)
    always_comb begin
      assert (X === (t_and0 | t_or0 | t_nand1 | t_nor1))
        else $error("X functional mismatch");

      if (!t_and0 && !t_or0 && !t_nand1 && !t_nor1)
        assert (X == 1'b0) else $error("X should be 0 when all terms false");

      if ( t_and0 && !t_or0 && !t_nand1 && !t_nor1)
        assert (X == 1'b1) else $error("X should be 1 when only and0 true");

      if (!t_and0 &&  t_or0 && !t_nand1 && !t_nor1)
        assert (X == 1'b1) else $error("X should be 1 when only or0 true");

      if (!t_and0 && !t_or0 &&  t_nand1 && !t_nor1)
        assert (X == 1'b1) else $error("X should be 1 when only !and1 true");

      if (!t_and0 && !t_or0 && !t_nand1 &&  t_nor1)
        assert (X == 1'b1) else $error("X should be 1 when only !or1 true");

      if (!$isunknown({A,B,C,D,E,F,G,H}))
        assert (!$isunknown(X)) else $error("X is X/Z while inputs are 0/1");
    end

    // Procedural coverage for key points
    always_comb begin
      cover (X == 1'b0);
      cover (X == 1'b1);
      cover ( t_and0 && !t_or0 && !t_nand1 && !t_nor1);
      cover (!t_and0 &&  t_or0 && !t_nand1 && !t_nor1);
      cover (!t_and0 && !t_or0 &&  t_nand1 && !t_nor1);
      cover (!t_and0 && !t_or0 && !t_nand1 &&  t_nor1);
    end
  end

endmodule

// Simple bind examples:
// Clocked (preferred):
//   bind logic_module logic_module_sva #(.CLOCKED(1)) u_sva ( .clk(tb_clk),
//     .A(A),.B(B),.C(C),.D(D),.E(E),.F(F),.G(G),.H(H),.X(X) );
//
// Clockless:
//   bind logic_module logic_module_sva #(.CLOCKED(0)) u_sva ( .clk(1'b0),
//     .A(A),.B(B),.C(C),.D(D),.E(E),.F(F),.G(G),.H(H),.X(X) );