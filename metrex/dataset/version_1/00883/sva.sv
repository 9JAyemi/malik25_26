// SVA bind file for the given design.
// Focused, concise assertions and coverage.

`ifndef SVA_BIND_V
`define SVA_BIND_V

// -----------------------------
// binary_to_3bit_decoder SVA
// -----------------------------
module sva_binary_to_3bit_decoder (
  input  logic [2:0] in,
  input  logic       o0,
  input  logic       o1,
  input  logic       o2
);
  // Functional mapping checks (guard unknowns)
  assert property (@(*) !$isunknown(in[0]) |-> (o0 == in[0]));
  assert property (@(*) !$isunknown(in[1]) |-> (o1 == in[1]));
  assert property (@(*) !$isunknown(in[2]) |-> (o2 == in[2]));
  assert property (@(*) !$isunknown(in)    |-> !$isunknown({o2,o1,o0}));

  // Full input space coverage (8 patterns)
  cover property (@(*) in == 3'd0);
  cover property (@(*) in == 3'd1);
  cover property (@(*) in == 3'd2);
  cover property (@(*) in == 3'd3);
  cover property (@(*) in == 3'd4);
  cover property (@(*) in == 3'd5);
  cover property (@(*) in == 3'd6);
  cover property (@(*) in == 3'd7);
endmodule

bind binary_to_3bit_decoder sva_binary_to_3bit_decoder DEC_SVA (.*);

// -----------------------------
// nor_gate_using_nand SVA
// -----------------------------
module sva_nor_gate_using_nand (
  input  logic a,
  input  logic b,
  input  logic out
);
  // Functional check (NAND)
  assert property (@(*) !$isunknown({a,b}) |-> (out == ~(a & b)));
  assert property (@(*) !$isunknown({a,b}) |-> !$isunknown(out));

  // Truth-table coverage
  cover property (@(*) (a==0 && b==0 && out==1));
  cover property (@(*) (a==0 && b==1 && out==1));
  cover property (@(*) (a==1 && b==0 && out==1));
  cover property (@(*) (a==1 && b==1 && out==0));
endmodule

bind nor_gate_using_nand sva_nor_gate_using_nand NAND_SVA (.*);

// -----------------------------
// top_module SVA
// -----------------------------
module sva_top_module (
  input  logic [2:0] vec,
  input  logic       a,
  input  logic       b,
  input  logic       out,
  // tap internal nets
  input  logic       o0,
  input  logic       o1,
  input  logic       o2
);
  // End-to-end functional check: out depends only on vec[1:0] via NAND
  assert property (@(*) (out == ~(vec[0] & vec[1])));
  assert property (@(*) !$isunknown(vec[1:0]) |-> !$isunknown(out));

  // Connectivity checks to decoder outputs inside top
  assert property (@(*) (o0 == vec[0] && o1 == vec[1] && o2 == vec[2]));

  // Independence checks: out must not change with these when vec[1:0] stable
  assert property (@(*) $changed(vec[2]) && $stable(vec[1:0]) |-> $stable(out));
  assert property (@(*) $changed(a)      && $stable(vec[1:0]) |-> $stable(out));
  assert property (@(*) $changed(b)      && $stable(vec[1:0]) |-> $stable(out));

  // Output state coverage
  cover property (@(*) (vec[1:0] == 2'b11) && out==0);
  cover property (@(*) (vec[1:0] != 2'b11) && out==1);

  // Independence coverage: toggle unused inputs with stable output
  cover property (@(*) $changed(a)      && $stable(vec[1:0]) && $stable(out));
  cover property (@(*) $changed(b)      && $stable(vec[1:0]) && $stable(out));
  cover property (@(*) $changed(vec[2]) && $stable(vec[1:0]) && $stable(out));
endmodule

bind top_module sva_top_module TOP_SVA (
  .vec(vec), .a(a), .b(b), .out(out),
  .o0(o0), .o1(o1), .o2(o2)
);

`endif