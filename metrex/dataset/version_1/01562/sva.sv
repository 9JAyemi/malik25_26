// SVA for top_module and its submodules
// Concise, functionally focused checks with key coverage

// Bind to CLA: must behave as unsigned a+b
module cla_adder_4bit_sva (
  input logic [3:0] a, b,
  input logic [3:0] sum,
  input logic       carry_out
);
  // Functional equivalence
  assert property (@(*)
    disable iff ($isunknown({a,b}))
    {carry_out, sum} == $unsigned(a) + $unsigned(b)
  ) else $error("CLA: {carry,sum} != a+b");

  // Key coverage
  cover property (@(*)) (a==4'h0 && b==4'h0);
  cover property (@(*)) (a==4'hF && b==4'hF && carry_out); // overflow case
  cover property (@(*)) carry_out;                          // any carry
endmodule
bind cla_adder_4bit cla_adder_4bit_sva(.a(a),.b(b),.sum(sum),.carry_out(carry_out));


// Bind to twos_comp_adder: as coded, it computes a_ext + ~b_ext
module twos_comp_adder_sva (
  input  logic [2:0] a,
  input  logic       b_in,
  input  logic [2:0] sum,
  input  logic       overflow
);
  let a_ext     = $unsigned({1'b0,a});
  let b3        = b_in ? 3'b111 : 3'b000;
  let b_ext_inv = ~$unsigned({1'b0,b3});          // ~b_ext
  let add5      = a_ext + b_ext_inv;              // 5-bit expected result

  assert property (@(*)
    disable iff ($isunknown({a,b_in}))
    sum == add5[2:0]
  ) else $error("TCA: sum mismatch");

  assert property (@(*)
    disable iff ($isunknown({a,b_in}))
    overflow == add5[4]
  ) else $error("TCA: overflow mismatch");

  // Key coverage: both b_in modes and overflow
  cover property (@(*)) (b_in==0);
  cover property (@(*)) (b_in==1);
  cover property (@(*)) (add5[4]==1);
endmodule
bind twos_comp_adder twos_comp_adder_sva(.a(a),.b_in(b_in),.sum(sum),.overflow(overflow));


// Bind to top: check all observable functionality and internal adder2 outputs
module top_module_sva (
  input  logic [2:0] a, b,
  input  logic [2:0] out_or_bitwise,
  input  logic       out_or_logical,
  input  logic [5:0] out_not,
  input  logic [7:0] s,
  input  logic       overflow,

  // internal signals from adder2
  input  logic [2:0] add_out2,
  input  logic       add_overflow
);
  // Local lets for expectations
  let bit_or   = (a | b);
  let log_or   = |bit_or;
  let sum5     = $unsigned({1'b0,a}) + $unsigned({1'b0,b}); // 5-bit a+b
  let s5       = {overflow, s[3:0]};
  let add2_5   = $unsigned({1'b0,bit_or}) + (~$unsigned({1'b0,(log_or?3'b111:3'b000)}));

  // OR logic
  assert property (@(*)
    disable iff ($isunknown({a,b}))
    out_or_bitwise == bit_or
  ) else $error("top: out_or_bitwise != a|b");

  assert property (@(*)
    disable iff ($isunknown({a,b}))
    out_or_logical == log_or
  ) else $error("top: out_or_logical != |(a|b)");

  // NOT outputs
  assert property (@(*)
    disable iff ($isunknown({a,b}))
    out_not == {~b, ~a}
  ) else $error("top: out_not mismatch");

  // Adder and overflow mapping into s
  assert property (@(*)
    disable iff ($isunknown({a,b}))
    s[7:5] == 3'b000
  ) else $error("top: s[7:5] must be 0");

  assert property (@(*)
    disable iff ($isunknown({a,b}))
    s5 == sum5
  ) else $error("top: {overflow,s[3:0]} != a+b");

  assert property (@(*)
    disable iff ($isunknown({a,b}))
    overflow == s[4]
  ) else $error("top: overflow != s[4]");

  // Internal twos_comp_adder outputs are consistent with inputs it receives
  assert property (@(*)
    disable iff ($isunknown({a,b}))
    add_out2 == add2_5[2:0]
  ) else $error("top: add_out2 mismatch");

  assert property (@(*)
    disable iff ($isunknown({a,b}))
    add_overflow == add2_5[4]
  ) else $error("top: add_overflow mismatch");

  // Sanity: outputs not X/Z when inputs known
  assert property (@(*)
    disable iff ($isunknown({a,b}))
    !$isunknown({out_or_bitwise,out_or_logical,out_not,s,overflow,add_out2,add_overflow})
  ) else $error("top: X/Z detected on outputs");

  // Key coverage: main adder carry, OR reduction 0/1, adder2 carry
  cover property (@(*)) (sum5[4]==1);           // CLA carry-out
  cover property (@(*)) (bit_or==3'b000);       // OR path all zero
  cover property (@(*)) (log_or==1);            // OR reduction asserted
  cover property (@(*)) (add2_5[4]==1);         // adder2 carry-out
endmodule
bind top_module top_module_sva(
  .a(a), .b(b),
  .out_or_bitwise(out_or_bitwise),
  .out_or_logical(out_or_logical),
  .out_not(out_not),
  .s(s),
  .overflow(overflow),
  .add_out2(add_out2),
  .add_overflow(add_overflow)
);