// SVA checkers and binds for nand_gate and decoder_2to4

// Checker for nand_gate
module nand_gate_sva (input logic a, b, y);
  // Functional correctness on any input change
  property p_nand_func;
    @(posedge a or negedge a or posedge b or negedge b)
      1 |-> (y === ~(a & b));
  endproperty
  a_nand_func: assert property (p_nand_func);

  // If inputs are known, output must be known and correct
  property p_nand_known;
    @(posedge a or negedge a or posedge b or negedge b)
      (!$isunknown({a,b})) |-> (! $isunknown(y) && (y == ~(a & b)));
  endproperty
  a_nand_known: assert property (p_nand_known);

  // Coverage: all input combinations
  c_ab_00: cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==0 && y==1));
  c_ab_01: cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==1 && y==1));
  c_ab_10: cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==0 && y==1));
  c_ab_11: cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==1 && y==0));
endmodule
bind nand_gate nand_gate_sva(.a(a), .b(b), .y(y));


// Checker for decoder_2to4
module decoder_2to4_sva (
  input  logic [1:0] in,
  input  logic [3:0] out,
  input  logic       n1, n2
);
  // Internal NAND wires are correct
  a_n1: assert property (@(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
                         n1 === ~(in[0] & in[1]));
  a_n2: assert property (@(sameedge) n2 === ~(in[0] & ~in[1])))
    // Use macro-like alias via let to avoid duplication
  ;
  // Output equals function of inputs
  a_out_map_in: assert property (@(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
                                 (out[0] === ~in[0]) &&
                                 (out[1] === (in[0] & ~in[1])) &&
                                 (out[2] === (in[0] &  in[1])) &&
                                 (out[3] === 1'b0));

  // Output equals function of internal wires (structural consistency)
  a_out_map_n: assert property (@(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
                                out === {~n1 & ~n2, ~n1 & n2, n1 & ~n2, n1 & n2});

  // One-hot output when inputs are known; outputs must also be known
  a_onehot_known: assert property (@(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
                                   (!$isunknown(in)) |-> (!$isunknown(out) && $onehot(out)));

  // Coverage: all input combinations with expected one-hot outputs
  c_in_00: cover property (@(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
                           (in==2'b00 && out==4'b0001));
  c_in_01: cover property (@(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
                           (in==2'b01 && out==4'b0010));
  c_in_10: cover property (@(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
                           (in==2'b10 && out==4'b0001));
  c_in_11: cover property (@(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
                           (in==2'b11 && out==4'b0100));
endmodule
bind decoder_2to4 decoder_2to4_sva(.in(in), .out(out), .n1(n1), .n2(n2));