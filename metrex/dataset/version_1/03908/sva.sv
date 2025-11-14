// SVA checkers and binds for the provided DUTs

// Top-level checker
module top_module_sva (
  input  logic [2:0] a,
  input  logic [2:0] b,
  input  logic [2:0] out_or_bitwise,
  input  logic       out_or_logical,
  input  logic [5:0] out_not
);
  // Combinational assertions sampled after delta cycle
  always_comb begin
    #0;
    assert (out_or_bitwise == (a | b))
      else $error("out_or_bitwise != a|b a=%b b=%b out=%b", a,b,out_or_bitwise);

    assert (out_not == {~b, ~a})
      else $error("out_not != {~b,~a} a=%b b=%b out_not=%b", a,b,out_not);

    // RTL implements an all-ones detector on (a|b)
    assert (out_or_logical == &(a | b))
      else $error("out_or_logical != &(a|b) a=%b b=%b out=%b", a,b,out_or_logical);

    // X/Z on outputs
    assert (!$isunknown({out_or_bitwise, out_or_logical, out_not}))
      else $error("Output contains X/Z: out_or_bitwise=%b out_or_logical=%b out_not=%b",
                  out_or_bitwise, out_or_logical, out_not);

    // Functional coverage (concise and meaningful)
    cover ((a | b) == 3'b000);
    cover ((a | b) == 3'b111);
    cover ((a | b) inside {3'b001,3'b010,3'b100}); // single-bit
    cover ((a | b) inside {3'b011,3'b101,3'b110}); // two-bits
    cover (out_or_logical == 1'b0);
    cover (out_or_logical == 1'b1);

    // Divergence between "logical OR" semantics and implemented all-ones detector
    cover (((|a) || (|b)) && !( &(a|b) )); // highlights potential spec mismatch
  end
endmodule

bind top_module top_module_sva top_module_sva_i (
  .a(a), .b(b),
  .out_or_bitwise(out_or_bitwise),
  .out_or_logical(out_or_logical),
  .out_not(out_not)
);


// Checker for logic_or_bitwise_or_module
module logic_or_bitwise_or_module_sva (
  input logic [2:0] a,
  input logic [2:0] b,
  input logic [2:0] out
);
  always_comb begin
    #0;
    assert (out == (a | b))
      else $error("bitwise_or out != a|b a=%b b=%b out=%b", a,b,out);
    assert (!$isunknown(out))
      else $error("bitwise_or out has X/Z: %b", out);

    cover (out == 3'b000);
    cover (out == 3'b111);
  end
endmodule

bind logic_or_bitwise_or_module logic_or_bitwise_or_module_sva lb_sva_i (
  .a(a), .b(b), .out(out)
);


// Checker for inverter_module
module inverter_module_sva (
  input logic [2:0] in,
  input logic [2:0] out
);
  always_comb begin
    #0;
    assert (out == ~in)
      else $error("inverter out != ~in in=%b out=%b", in,out);
    assert (!$isunknown(out))
      else $error("inverter out has X/Z: %b", out);

    cover (in == 3'b000);
    cover (in == 3'b111);
    cover ((|in) && (~&in)); // mixed pattern
  end
endmodule

bind inverter_module inverter_module_sva inv_sva_i (
  .in(in), .out(out)
);