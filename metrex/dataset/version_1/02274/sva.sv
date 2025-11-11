// SVA for alu
// Assumes an external clk and active-low reset rst_n are available in the bind scope.

module alu_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [4:0]  aluc,
  input logic [31:0] result
);
  default clocking cb @(posedge clk); endclocking

  // Helper sets
  localparam logic [4:0] ADD0 = 5'd0, ADD1 = 5'd1;
  localparam logic [4:0] SUB0 = 5'd2, SUB1 = 5'd3;
  localparam logic [4:0] ANDC = 5'd4, ORC = 5'd5, XORC = 5'd6, NORC = 5'd7;
  localparam logic [4:0] SLT0 = 5'd8, SLT1 = 5'd9;
  localparam logic [4:0] SLLV = 5'd10, SRLV = 5'd11, SRAV = 5'd12;
  localparam logic [4:0] L16  = 5'd14;

  function automatic bit in_known_set(input logic [4:0] x);
    in_known_set = (x==ADD0)||(x==ADD1)||(x==SUB0)||(x==SUB1)||(x==ANDC)||(x==ORC)||
                   (x==XORC)||(x==NORC)||(x==SLT0)||(x==SLT1)||(x==SLLV)||(x==SRLV)||
                   (x==SRAV)||(x==L16);
  endfunction

  // X-propagation guard: if inputs known, result must be known
  assert property (disable iff (!rst_n)
                   !$isunknown({a,b,aluc}) |-> !$isunknown(result))
    else $error("alu: result has X/Z with known inputs");

  // Arithmetic operations
  assert property (disable iff (!rst_n)
                   (aluc inside {ADD0,ADD1}) |-> result == (a + b))
    else $error("alu add mismatch");

  assert property (disable iff (!rst_n)
                   (aluc inside {SUB0,SUB1}) |-> result == (a - b))
    else $error("alu sub mismatch");

  // Bitwise operations
  assert property (disable iff (!rst_n)
                   (aluc==ANDC) |-> result == (a & b))
    else $error("alu and mismatch");

  assert property (disable iff (!rst_n)
                   (aluc==ORC) |-> result == (a | b))
    else $error("alu or mismatch");

  assert property (disable iff (!rst_n)
                   (aluc==XORC) |-> result == (a ^ b))
    else $error("alu xor mismatch");

  assert property (disable iff (!rst_n)
                   (aluc==NORC) |-> result == ~(a | b))
    else $error("alu nor mismatch");

  // Set-less-than (unsigned compare; result is 32'h1 or 32'h0)
  assert property (disable iff (!rst_n)
                   (aluc inside {SLT0,SLT1}) |-> result == {31'b0, (a < b)})
    else $error("alu slt mismatch");

  // Shifts (note: SLL/SRL use full a as shift amount; SRA uses a[4:0])
  assert property (disable iff (!rst_n)
                   (aluc==SLLV) |-> result == (b << a))
    else $error("alu sllv mismatch");

  assert property (disable iff (!rst_n)
                   (aluc==SRLV) |-> result == (b >> a))
    else $error("alu srlv mismatch");

  assert property (disable iff (!rst_n)
                   (aluc==SRAV) |-> result == ($signed(b) >>> a[4:0]))
    else $error("alu srav mismatch");

  // Load upper halfword (equivalent to b << 16)
  assert property (disable iff (!rst_n)
                   (aluc==L16) |-> result == {b[15:0],16'h0000})
    else $error("alu l16 mismatch");

  // Default behavior for all other opcodes
  assert property (disable iff (!rst_n)
                   !in_known_set(aluc) |-> result == 32'h0000_0000)
    else $error("alu default mismatch");

  // Basic determinism: if inputs stable, result stable
  assert property (disable iff (!rst_n)
                   $stable({a,b,aluc}) |-> $stable(result))
    else $error("alu non-deterministic result");

  // Functional coverage
  covergroup cg_opcode @(posedge clk);
    option.per_instance = 1;
    cp_aluc : coverpoint aluc {
      bins add  = {ADD0,ADD1};
      bins sub  = {SUB0,SUB1};
      bins band = {ANDC};
      bins bor  = {ORC};
      bins bxor = {XORC};
      bins bnor = {NORC};
      bins slt  = {SLT0,SLT1};
      bins sllv = {SLLV};
      bins srlv = {SRLV};
      bins srav = {SRAV};
      bins l16  = {L16};
      bins other[] = default;
    }
  endgroup
  cg_opcode cg_ops = new();

  // Corner-case covers
  // Add carry-out
  cover property (disable iff (!rst_n)
                  (aluc inside {ADD0,ADD1}) &&
                  ({1'b0,a} + {1'b0,b})[32]);

  // Sub borrow (unsigned a<b)
  cover property (disable iff (!rst_n)
                  (aluc inside {SUB0,SUB1}) && (a < b));

  // SLT outcomes
  cover property (disable iff (!rst_n)
                  (aluc inside {SLT0,SLT1}) && (a < b));
  cover property (disable iff (!rst_n)
                  (aluc inside {SLT0,SLT1}) && !(a < b));

  // Shift amounts: 0, 1, 31, >=32 for variable logical shifts
  cover property (disable iff (!rst_n) (aluc==SLLV) && (a==0));
  cover property (disable iff (!rst_n) (aluc==SLLV) && (a==1));
  cover property (disable iff (!rst_n) (aluc==SLLV) && (a==31));
  cover property (disable iff (!rst_n) (aluc==SLLV) && (a>=32) && (result==32'h0));

  cover property (disable iff (!rst_n) (aluc==SRLV) && (a==0));
  cover property (disable iff (!rst_n) (aluc==SRLV) && (a==1));
  cover property (disable iff (!rst_n) (aluc==SRLV) && (a==31));
  cover property (disable iff (!rst_n) (aluc==SRLV) && (a>=32) && (result==32'h0));

  // Arithmetic right shift sign fill
  cover property (disable iff (!rst_n) (aluc==SRAV) && (a[4:0]!=0) && (b[31]==1) && (result[31]==1));
  cover property (disable iff (!rst_n) (aluc==SRAV) && (a[4:0]!=0) && (b[31]==0) && (result[31]==0));

  // L16 operation observed
  cover property (disable iff (!rst_n) (aluc==L16));
endmodule

// Bind into DUT (ensure clk and rst_n exist in the bind scope)
bind alu alu_sva u_alu_sva (
  .clk   (clk),
  .rst_n (rst_n),
  .a     (a),
  .b     (b),
  .aluc  (aluc),
  .result(result)
);