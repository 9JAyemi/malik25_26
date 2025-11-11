// SVA checker for bitwise_or_logical_not
module bitwise_or_logical_not_sva (
  input logic [2:0] a,
  input logic [2:0] b,
  input logic [2:0] out_or_bitwise,
  input logic       out_or_logical,
  input logic [5:0] out_not
);

  // sample on any combinational change
  event sample_ev;
  always @* -> sample_ev;

  // Functional correctness (concurrent SVA)
  assert property (@(sample_ev) disable iff ($isunknown({a,b}))
                   (out_or_bitwise === ~(a ^ b)))
    else $error("out_or_bitwise != ~(a^b): a=%0b b=%0b got=%0b exp=%0b",
                a,b,out_or_bitwise,~(a^b));

  assert property (@(sample_ev) disable iff ($isunknown({a,b}))
                   (out_or_logical === |(a & b)))
    else $error("out_or_logical != |(a&b): a=%0b b=%0b got=%0b exp=%0b",
                a,b,out_or_logical,|(a&b));

  assert property (@(sample_ev) disable iff ($isunknown({a,b}))
                   (out_not === {~a, ~b}))
    else $error("out_not != {~a,~b}: a=%0b b=%0b got=%0b exp=%0b",
                a,b,out_not,{~a,~b});

  // Key scenario coverage (SVA)
  cover property (@(sample_ev) !$isunknown({a,b}) && (a & b) == 3'b000 && (out_or_logical == 1'b0));
  cover property (@(sample_ev) !$isunknown({a,b}) && (a & b) != 3'b000 && (out_or_logical == 1'b1));
  cover property (@(sample_ev) !$isunknown({a,b}) && (out_or_bitwise == 3'b111));
  cover property (@(sample_ev) !$isunknown({a,b}) && (out_or_bitwise == 3'b000));

  // Full functional coverage of inputs and outputs
  covergroup cg @(sample_ev);
    option.per_instance = 1;
    cp_a: coverpoint a { bins all[] = {[0:7]}; }
    cp_b: coverpoint b { bins all[] = {[0:7]}; }
    axb: cross cp_a, cp_b;
    cp_out_or_bitwise: coverpoint out_or_bitwise { bins all[] = {[0:7]}; }
    cp_out_or_logical: coverpoint out_or_logical { bins b0 = {0}; bins b1 = {1}; }
    cp_out_not: coverpoint out_not { bins all[] = {[0:63]}; }
  endgroup
  cg cg_i = new();

endmodule

// Bind example:
// bind bitwise_or_logical_not bitwise_or_logical_not_sva
//   (.a(a), .b(b), .out_or_bitwise(out_or_bitwise), .out_or_logical(out_or_logical), .out_not(out_not));