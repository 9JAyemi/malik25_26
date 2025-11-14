Below is a concise SVA bind file that thoroughly checks the ALU’s functionality, flags, X-cleanliness, and provides focused coverage. It binds into the DUT and references internal addercout and op parameters. It uses ##0 (and when needed ##0##0) to allow delta cycles for nonblocking combinational updates.

```systemverilog
// Bind these assertions into the ALU
bind alu alu_sva alu_sva_i();

module alu_sva;

  // Helper for legal op decode
  function automatic bit is_legal_op (logic [3:0] x);
    return (x inside {ALUOP_ADD,ALUOP_SUB,ALUOP_AND,ALUOP_OR,
                      ALUOP_XOR,ALUOP_COM,ALUOP_ROR,ALUOP_ROL,ALUOP_SWAP});
  endfunction

  // X-clean outputs when inputs are known (allow two deltas for cascaded NBAs)
  property p_no_x_out;
    @(op or a or b or cin)
      !$isunknown({op,a,b,cin}) |-> ##0 ##0 !$isunknown({y,cout,zout,addercout});
  endproperty
  assert property (p_no_x_out);

  // Zero flag consistent with y
  property p_zout_map;
    @(y or zout) !$isunknown(y) |-> ##0 (zout == (y == 8'h00));
  endproperty
  assert property (p_zout_map);

  // cout mapping (invert only for SUB)
  property p_cout_map;
    @(addercout or op or cout)
      !$isunknown({addercout,op}) |-> ##0 ((op == ALUOP_SUB) ? (cout == ~addercout)
                                                          : (cout ==  addercout));
  endproperty
  assert property (p_cout_map);

  // Default/illegal op drives zeros
  property p_default;
    @(op or a or b or cin)
      (!$isunknown(op) && !is_legal_op(op)) |-> ##0 ({addercout,y} == 9'h000);
  endproperty
  assert property (p_default);

  // Arithmetic (explicitly size-extend to 9 bits to check true carry/borrow)
  property p_add;
    @(op or a or b)
      (!$isunknown({op,a,b}) && op == ALUOP_ADD) |-> ##0
        ({addercout,y} == ({1'b0,a} + {1'b0,b}));
  endproperty
  assert property (p_add);

  property p_sub;
    @(op or a or b)
      (!$isunknown({op,a,b}) && op == ALUOP_SUB) |-> ##0
        ({addercout,y} == ({1'b0,a} - {1'b0,b}));
  endproperty
  assert property (p_sub);

  // Logical
  property p_and;
    @(op or a or b)
      (!$isunknown({op,a,b}) && op == ALUOP_AND) |-> ##0
        ({addercout,y} == {1'b0, (a & b)});
  endproperty
  assert property (p_and);

  property p_or;
    @(op or a or b)
      (!$isunknown({op,a,b}) && op == ALUOP_OR) |-> ##0
        ({addercout,y} == {1'b0, (a | b)});
  endproperty
  assert property (p_or);

  property p_xor;
    @(op or a or b)
      (!$isunknown({op,a,b}) && op == ALUOP_XOR) |-> ##0
        ({addercout,y} == {1'b0, (a ^ b)});
  endproperty
  assert property (p_xor);

  property p_com;
    @(op or a)
      (!$isunknown({op,a}) && op == ALUOP_COM) |-> ##0
        ({addercout,y} == {1'b0, ~a});
  endproperty
  assert property (p_com);

  // Rotates
  property p_ror;
    @(op or a or cin)
      (!$isunknown({op,a,cin}) && op == ALUOP_ROR) |-> ##0
        ({addercout,y} == {a[0], cin, a[7:1]});
  endproperty
  assert property (p_ror);

  property p_rol;
    @(op or a or cin)
      (!$isunknown({op,a,cin}) && op == ALUOP_ROL) |-> ##0
        ({addercout,y} == {a[7], a[6:0], cin});
  endproperty
  assert property (p_rol);

  property p_swap;
    @(op or a)
      (!$isunknown({op,a}) && op == ALUOP_SWAP) |-> ##0
        ({addercout,y} == {1'b0, a[3:0], a[7:4]});
  endproperty
  assert property (p_swap);

  // cin must not affect y/cout for non-rotate ops (allow two deltas for cascaded NBAs)
  property p_cin_irrelevant_nonrot;
    @(a or b or op or cin)
      (!$isunknown({a,b,op,cin}) &&
       (op inside {ALUOP_ADD,ALUOP_SUB,ALUOP_AND,ALUOP_OR,ALUOP_XOR,ALUOP_COM,ALUOP_SWAP}) &&
       $changed(cin) && $stable({a,b,op}))
      |-> ##0 ##0 ($stable(y) && $stable(cout));
  endproperty
  assert property (p_cin_irrelevant_nonrot);

  // ----------------
  // Coverage (concise, focused)
  // ----------------
  cover property (@(op) op == ALUOP_ADD);
  cover property (@(op) op == ALUOP_SUB);
  cover property (@(op) op == ALUOP_AND);
  cover property (@(op) op == ALUOP_OR);
  cover property (@(op) op == ALUOP_XOR);
  cover property (@(op) op == ALUOP_COM);
  cover property (@(op) op == ALUOP_ROR);
  cover property (@(op) op == ALUOP_ROL);
  cover property (@(op) op == ALUOP_SWAP);

  // Carry and borrow scenarios
  cover property (@(op or a or b) (op == ALUOP_ADD) ##0 addercout);
  cover property (@(op or a or b) (op == ALUOP_ADD) ##0 !addercout);
  cover property (@(op or a or b) (op == ALUOP_SUB) ##0 ##0 cout);   // borrow asserted
  cover property (@(op or a or b) (op == ALUOP_SUB) ##0 ##0 !cout);   // no borrow

  // Zero flag asserted
  cover property (@(y or zout) zout);

  // Rotates with meaningful flag effects
  cover property (@(op or a or cin) (op == ALUOP_ROR && a[0] && cin));
  cover property (@(op or a or cin) (op == ALUOP_ROL && a[7] && cin));

endmodule
```