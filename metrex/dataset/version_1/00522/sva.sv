// SVA for bitwise_operations
// Concurrent assertions use event-based sampling on input changes and ##0 to avoid delta races.

module bitwise_operations_sva (
  input logic [7:0] A,
  input logic [7:0] B,
  input logic [2:0] OP,
  input logic [7:0] AND_out,
  input logic [7:0] OR_out,
  input logic [7:0] XOR_out,
  input logic [7:0] NOT_out
);

  // Outputs must be known when inputs are known
  property p_known_outputs;
    @(A or B or OP or AND_out or OR_out or XOR_out or NOT_out)
      disable iff ($isunknown({A,B,OP}))
      1 |-> ##0 !$isunknown({AND_out,OR_out,XOR_out,NOT_out});
  endproperty
  assert property (p_known_outputs);

  // Functional correctness per opcode
  property p_and;
    @(A or B or OP) disable iff ($isunknown({A,B,OP}))
      (OP==3'b000) |-> ##0
        (AND_out==(A&B) && OR_out==8'h00 && XOR_out==8'h00 && NOT_out==8'h00);
  endproperty
  assert property (p_and);

  property p_or;
    @(A or B or OP) disable iff ($isunknown({A,B,OP}))
      (OP==3'b001) |-> ##0
        (AND_out==8'h00 && OR_out==(A|B) && XOR_out==8'h00 && NOT_out==8'h00);
  endproperty
  assert property (p_or);

  property p_xor;
    @(A or B or OP) disable iff ($isunknown({A,B,OP}))
      (OP==3'b010) |-> ##0
        (AND_out==8'h00 && OR_out==8'h00 && XOR_out==(A^B) && NOT_out==8'h00);
  endproperty
  assert property (p_xor);

  property p_not;
    @(A or B or OP) disable iff ($isunknown({A,B,OP}))
      (OP==3'b011) |-> ##0
        (AND_out==8'h00 && OR_out==8'h00 && XOR_out==8'h00 && NOT_out==~A);
  endproperty
  assert property (p_not);

  // Invalid opcodes drive all zeros
  property p_default_zero;
    @(A or B or OP) disable iff ($isunknown({A,B,OP}))
      (!(OP inside {3'b000,3'b001,3'b010,3'b011})) |-> ##0
        (AND_out==8'h00 && OR_out==8'h00 && XOR_out==8'h00 && NOT_out==8'h00);
  endproperty
  assert property (p_default_zero);

  // Basic opcode coverage
  cover property (@(A or B or OP) (! $isunknown({A,B,OP}) && OP==3'b000));
  cover property (@(A or B or OP) (! $isunknown({A,B,OP}) && OP==3'b001));
  cover property (@(A or B or OP) (! $isunknown({A,B,OP}) && OP==3'b010));
  cover property (@(A or B or OP) (! $isunknown({A,B,OP}) && OP==3'b011));
  cover property (@(A or B or OP) (! $isunknown({A,B,OP}) && !(OP inside {3'b000,3'b001,3'b010,3'b011})));

  // Extremal result coverage per op
  cover property (@(A or B or OP) (OP==3'b000 && (A&B)==8'h00));
  cover property (@(A or B or OP) (OP==3'b000 && (A&B)==8'hFF));
  cover property (@(A or B or OP) (OP==3'b001 && (A|B)==8'h00));
  cover property (@(A or B or OP) (OP==3'b001 && (A|B)==8'hFF));
  cover property (@(A or B or OP) (OP==3'b010 && (A^B)==8'h00));
  cover property (@(A or B or OP) (OP==3'b010 && (A^B)==8'hFF));
  cover property (@(A or B or OP) (OP==3'b011 && (~A)==8'h00));
  cover property (@(A or B or OP) (OP==3'b011 && (~A)==8'hFF));

endmodule

// Bind into DUT
bind bitwise_operations bitwise_operations_sva sva_inst (.*);