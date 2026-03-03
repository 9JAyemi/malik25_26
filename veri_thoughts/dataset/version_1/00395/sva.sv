// SVA for alu. Bind this module to the DUT.
// Focused, concise, and covers/validates all ops, flags, and key invariants.

module alu_sva (
  input  logic [3:0] op,
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic       cin,
  input  logic [7:0] y,
  input  logic       cout,
  input  logic       zout
);
  // Mirror DUT opcodes
  localparam logic [3:0] ALUOP_ADD  = 4'b0000;
  localparam logic [3:0] ALUOP_SUB  = 4'b1000;
  localparam logic [3:0] ALUOP_AND  = 4'b0001;
  localparam logic [3:0] ALUOP_OR   = 4'b0010;
  localparam logic [3:0] ALUOP_XOR  = 4'b0011;
  localparam logic [3:0] ALUOP_COM  = 4'b0100;
  localparam logic [3:0] ALUOP_ROR  = 4'b0101;
  localparam logic [3:0] ALUOP_ROL  = 4'b0110;
  localparam logic [3:0] ALUOP_SWAP = 4'b0111;

  // Helper predicates
  function automatic logic valid_op (logic [3:0] x);
    return (x inside {ALUOP_ADD,ALUOP_SUB,ALUOP_AND,ALUOP_OR,ALUOP_XOR,ALUOP_COM,ALUOP_ROR,ALUOP_ROL,ALUOP_SWAP});
  endfunction

  // Known outputs when inputs known
  assert property (@(a or b or cin or op)
    !$isunknown({a,b,cin,op}) |-> ##0 !$isunknown({y,cout,zout})
  );

  // Zero flag consistency (always)
  assert property (@(a or b or cin or op)
    !$isunknown({a,b,cin,op}) |-> ##0 (zout == (y == 8'h00))
  );

  // ADD
  assert property (@(a or b or cin or op)
    !$isunknown({a,b,op}) && op==ALUOP_ADD |-> ##0
      (y == (({1'b0,a}+{1'b0,b})[7:0]) && cout == (({1'b0,a}+{1'b0,b})[8]))
  );

  // SUB (cout is borrow)
  assert property (@(a or b or cin or op)
    !$isunknown({a,b,op}) && op==ALUOP_SUB |-> ##0
      (y == (({1'b0,a}-{1'b0,b})[7:0]) && cout == ~(({1'b0,a}-{1'b0,b})[8]))
  );

  // AND/OR/XOR
  assert property (@(a or b or cin or op)
    !$isunknown({a,b,op}) && op==ALUOP_AND |-> ##0 (y == (a & b) && cout==1'b0)
  );
  assert property (@(a or b or cin or op)
    !$isunknown({a,b,op}) && op==ALUOP_OR  |-> ##0 (y == (a | b) && cout==1'b0)
  );
  assert property (@(a or b or cin or op)
    !$isunknown({a,b,op}) && op==ALUOP_XOR |-> ##0 (y == (a ^ b) && cout==1'b0)
  );

  // COM
  assert property (@(a or b or cin or op)
    !$isunknown({a,op}) && op==ALUOP_COM |-> ##0 (y == ~a && cout==1'b0)
  );

  // ROR (rotate right through carry)
  assert property (@(a or b or cin or op)
    !$isunknown({a,cin,op}) && op==ALUOP_ROR |-> ##0
      (y == {cin, a[7:1]} && cout == a[0])
  );

  // ROL (rotate left through carry)
  assert property (@(a or b or cin or op)
    !$isunknown({a,cin,op}) && op==ALUOP_ROL |-> ##0
      (y == {a[6:0], cin} && cout == a[7])
  );

  // SWAP nibbles
  assert property (@(a or b or cin or op)
    !$isunknown({a,op}) && op==ALUOP_SWAP |-> ##0 (y == {a[3:0], a[7:4]} && cout==1'b0)
  );

  // DEFAULT (illegal op)
  assert property (@(a or b or cin or op)
    !$isunknown({a,b,cin,op}) && !valid_op(op) |-> ##0 (y==8'h00 && cout==1'b0)
  );

  // Independence checks for ignored inputs
  // cin is ignored for all ops except ROR/ROL
  assert property (@(cin)
    !$isunknown({a,b,op,cin}) && (op inside {ALUOP_ADD,ALUOP_SUB,ALUOP_AND,ALUOP_OR,ALUOP_XOR,ALUOP_COM,ALUOP_SWAP})
      && $stable(a) && $stable(b) && $stable(op)
    |-> ##0 $stable({y,cout,zout})
  );
  // b is ignored for COM/ROR/ROL/SWAP
  assert property (@(b)
    !$isunknown({a,b,cin,op}) && (op inside {ALUOP_COM,ALUOP_ROR,ALUOP_ROL,ALUOP_SWAP})
      && $stable(a) && $stable(cin) && $stable(op)
    |-> ##0 $stable({y,cout,zout})
  );

  // Minimal functional coverage
  cover property (@(a or b or cin or op) op==ALUOP_ADD);
  cover property (@(a or b or cin or op) op==ALUOP_SUB);
  cover property (@(a or b or cin or op) op==ALUOP_AND);
  cover property (@(a or b or cin or op) op==ALUOP_OR);
  cover property (@(a or b or cin or op) op==ALUOP_XOR);
  cover property (@(a or b or cin or op) op==ALUOP_COM);
  cover property (@(a or b or cin or op) op==ALUOP_ROR);
  cover property (@(a or b or cin or op) op==ALUOP_ROL);
  cover property (@(a or b or cin or op) op==ALUOP_SWAP);
  cover property (@(a or b or cin or op) !valid_op(op));

  // Corner covers
  cover property (@(a or b or cin or op) op==ALUOP_ADD && (({1'b0,a}+{1'b0,b})[8]) ); // carry
  cover property (@(a or b or cin or op) op==ALUOP_SUB && (a < b) );                  // borrow
  cover property (@(a or b or cin or op) zout);                                       // zero result
  cover property (@(a or b or cin or op) op==ALUOP_ROR && a[0]);                      // ROR cout=1
  cover property (@(a or b or cin or op) op==ALUOP_ROL && a[7]);                      // ROL cout=1
  cover property (@(a or b or cin or op) op==ALUOP_ROR && cin);                       // ROR MSB from cin
  cover property (@(a or b or cin or op) op==ALUOP_ROL && cin);                       // ROL LSB from cin
endmodule

// Bind into the DUT
bind alu alu_sva alu_sva_i (.*);