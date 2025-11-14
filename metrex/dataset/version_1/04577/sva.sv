// SVA binders for top_module design
// Focus: concise, high-quality checks and meaningful coverage

// ---------- adder ----------
module adder_sva (
  input  logic [31:0] a, b,
  input  logic        carry_in,
  input  logic [31:0] sum,
  input  logic        carry_out
);
  logic [32:0] exp;
  always_comb begin
    exp = {1'b0,a} + {1'b0,b} + carry_in;
    assert ({carry_out,sum} == exp) else $error("adder: {carry,sum} != a+b+carry_in");

    // Coverage
    cover (carry_in==0 && exp[32]); // carry from pure add
    cover (carry_in==1 && exp[32]); // carry with carry_in
    cover (sum==32'h0000_0000);     // zero result
  end
endmodule

// ---------- adder_subtractor ----------
module adder_subtractor_sva (
  input  logic [31:0] a, b,
  input  logic        sub_select,
  input  logic [31:0] add_out,
  input  logic [31:0] sub_out,
  input  logic        carry_out,
  input  logic        overflow
);
  logic [32:0] add_ext, sub_ext;
  always_comb begin
    add_ext = {1'b0,a} + {1'b0,b};
    sub_ext = {1'b0,a} + {1'b0,~b} + 33'd1; // expected a - b

    if (!sub_select) begin
      assert (add_out == add_ext[31:0]) else $error("add_out != a+b");
      assert (overflow == add_ext[32])  else $error("overflow(add) != carry_out(a+b)");
    end else begin
      assert (sub_out == sub_ext[31:0]) else $error("sub_out != a-b");
      assert (overflow == sub_ext[32])  else $error("overflow(sub) != carry_out(a-b)");
    end

    // Implementation wiring check (as-coded): carry_out is driven by sub_select
    assert (carry_out == sub_select) else $error("carry_out wiring != sub_select");

    // X/Z checks guarded by valid inputs
    if (!$isunknown({a,b,sub_select}))
      assert (!$isunknown({add_out,sub_out,overflow,carry_out})) else $error("X/Z on adder_subtractor outputs");

    // Coverage
    cover (!sub_select && add_ext[32]);               // add carry
    cover ( sub_select && sub_ext[32]);               // sub borrow/carry
    cover ( sub_select && (a==b) && (sub_out==32'h0)); // a-b==0
    cover (!sub_select && (add_out==32'hFFFF_FFFF));  // maxed sum
  end
endmodule

// ---------- functional_logic ----------
module functional_logic_sva (
  input  logic [31:0] in1, in2,
  input  logic [31:0] out,
  input  logic        carry_in,
  input  logic        overflow_in
);
  always_comb begin
    // Intended 32-bit gating across all bits (will flag if single-bit gating is used)
    assert (out == (in1 & in2 & ~{32{carry_in}} & ~{32{overflow_in}}))
      else $error("functional_logic: missing 32-bit replication on carry/overflow gates");

    // Coverage
    cover (!carry_in && !overflow_in && |(in1 & in2)); // passes through when not gated
    cover (carry_in || overflow_in);                   // gating active
  end
endmodule

// ---------- top_module ----------
module top_module_sva (
  input  logic [31:0] a, b, sum,
  input  logic        sub_select,
  // internal taps
  input  logic [31:0] add_out, sub_out, and_out,
  input  logic        carry_out, overflow
);
  logic [31:0] exp_sum;
  always_comb begin
    // Mux correctness
    assert (sum == (sub_select ? sub_out : add_out)) else $error("top: sum mux incorrect");

    // End-to-end arithmetic (flags bug if subtraction path off by one)
    exp_sum = sub_select ? (a - b) : (a + b);
    assert (sum == exp_sum) else $error("top: end-to-end sum != arithmetic");

    // Functional AND path intent
    assert (and_out == (add_out & sub_out & ~{32{carry_out}} & ~{32{overflow}}))
      else $error("top: and_out != intended gating of add/sub");

    // X/Z checks when inputs are known
    if (!$isunknown({a,b,sub_select}))
      assert (!$isunknown({sum,add_out,sub_out,and_out,carry_out,overflow})) else $error("top: X/Z on outputs");

    // Coverage
    cover (sub_select==0);
    cover (sub_select==1);
    cover (sum==32'h0000_0000);
  end
endmodule

// ---------- Binds ----------
bind adder             adder_sva             adder_sva_i             (.*);
bind adder_subtractor  adder_subtractor_sva  adder_subtractor_sva_i  (.*);
bind functional_logic  functional_logic_sva  functional_logic_sva_i  (.*);
bind top_module        top_module_sva        top_module_sva_i        (.a(a), .b(b), .sum(sum),
                                                                     .sub_select(sub_select),
                                                                     .add_out(add_out),
                                                                     .sub_out(sub_out),
                                                                     .and_out(and_out),
                                                                     .carry_out(carry_out),
                                                                     .overflow(overflow));