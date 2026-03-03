// SVA for top_module
// Concise, functionally canonical checks + essential coverage

`default_nettype none
module top_module_sva (
  input  logic [99:0] in,
  input  logic [3:0]  in1,
  input  logic [3:0]  in2,
  input  logic        select,
  input  logic        out_and,
  input  logic        out_or,
  input  logic        out_xor,
  input  logic [24:0] and_out,
  input  logic [3:0]  and_out_1,
  input  logic [3:0]  or_out_1,
  input  logic [3:0]  xor_out_1,
  input  logic [3:0]  and_out_2,
  input  logic [3:0]  or_out_2,
  input  logic [3:0]  xor_out_2,
  input  logic [3:0]  final_out
);

  // X/Z on inputs not allowed
  always_comb begin
    assert (!$isunknown({in,in1,in2,select})) else $error("X/Z on inputs");
  end

  // 100-input AND canonical check and per-4-bit tree check
  always_comb assert (out_and === &in) else $error("out_and != &in");
  genvar gi;
  generate
    for (gi=0; gi<25; gi++) begin : g_and_groups
      always_comb assert (and_out[gi] === &in[gi*4 +: 4])
        else $error("and_out[%0d] mismatch", gi);
    end
  endgenerate

  // Bitwise module outputs must match spec and duplicates must agree
  always_comb begin
    assert (and_out_1 === (in1 & in2)) else $error("and_out_1 mismatch");
    assert (and_out_2 === (in1 & in2)) else $error("and_out_2 mismatch");
    assert (or_out_1  === (in1 | in2)) else $error("or_out_1 mismatch");
    assert (or_out_2  === (in1 | in2)) else $error("or_out_2 mismatch");
    assert (xor_out_1 === (in1 ^ in2)) else $error("xor_out_1 mismatch");
    assert (xor_out_2 === (in1 ^ in2)) else $error("xor_out_2 mismatch");

    assert (and_out_1 === and_out_2) else $error("and_out_1 != and_out_2");
    assert (or_out_1  === or_out_2)  else $error("or_out_1  != or_out_2");
    assert (xor_out_1 === xor_out_2) else $error("xor_out_1 != xor_out_2");
  end

  // final_out select logic, plus canonical against in1/in2
  always_comb begin
    assert (final_out === (select ? (and_out_1 & and_out_2)
                                  : (or_out_1  | or_out_2)))
      else $error("final_out select mux mismatch");
    assert ( select  -> (final_out === (in1 & in2)))
      else $error("final_out != in1&in2 when select=1");
    assert (!select  -> (final_out === (in1 | in2)))
      else $error("final_out != in1|in2 when select=0");
  end

  // Output reductions
  always_comb assert (out_or  === |final_out)    else $error("out_or mismatch");
  always_comb assert (out_xor === ^xor_out_1)    else $error("out_xor != ^xor_out_1");
  always_comb assert (out_xor === ^(in1 ^ in2))  else $error("out_xor != ^(in1^in2)");

  // Minimal functional coverage
  cover property (@(in or in1 or in2 or select) select==0);
  cover property (@(in or in1 or in2 or select) select==1);
  cover property (@(posedge select) 1);
  cover property (@(negedge select) 1);

  cover property (@(in or in1 or in2 or select) out_and);
  cover property (@(in or in1 or in2 or select) !out_and);

  cover property (@(in or in1 or in2 or select) out_or);
  cover property (@(in or in1 or in2 or select) !out_or);

  cover property (@(in or in1 or in2 or select) out_xor);
  cover property (@(in or in1 or in2 or select) !out_xor);

  cover property (@(in1 or in2 or select)  select && (final_out == (in1 & in2)));
  cover property (@(in1 or in2 or select) !select && (final_out == (in1 | in2)));

endmodule

bind top_module top_module_sva i_top_module_sva (
  .in(in),
  .in1(in1),
  .in2(in2),
  .select(select),
  .out_and(out_and),
  .out_or(out_or),
  .out_xor(out_xor),
  .and_out(and_out),
  .and_out_1(and_out_1),
  .or_out_1(or_out_1),
  .xor_out_1(xor_out_1),
  .and_out_2(and_out_2),
  .or_out_2(or_out_2),
  .xor_out_2(xor_out_2),
  .final_out(final_out)
);