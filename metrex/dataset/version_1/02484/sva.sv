// SVA for top_module and its functionality
module top_module_sva (
  input  [3:0] in,
  input  [2:0] a,
  input  [2:0] b,
  input  [1:0] select,
  input  [1:0] pos,
  input  [2:0] out_or_bitwise,
  input        out_or_logical,
  input  [5:0] out_not,
  input  [2:0] out
);
  // Combinational assertions and coverage
  always_comb begin
    // priority_encoder correctness
    assert (pos == (in[3] ? 2'b11 :
                    in[2] ? 2'b10 :
                    in[1] ? 2'b01 : 2'b00))
      else $error("priority_encoder mismatch: in=%b pos=%b", in, pos);

    // binary_module correctness
    assert (out_or_bitwise == (a | b))
      else $error("bitwise OR mismatch: a=%b b=%b out_or_bitwise=%b", a, b, out_or_bitwise);

    assert (out_or_logical == ((a != 3'b000) || (b != 3'b000)))
      else $error("logical OR mismatch: a=%b b=%b out_or_logical=%b", a, b, out_or_logical);

    assert (out_not == ~{a,b})
      else $error("NOT concat mismatch: a=%b b=%b out_not=%b", a, b, out_not);

    // cross-consistency checks
    assert (out_or_logical == (|out_or_bitwise))
      else $error("logical OR != reduction of bitwise OR");

    assert (out_not[5:3] == ~a && out_not[2:0] == ~b)
      else $error("out_not partition mismatch");

    // functional_module select path and sizing/truncation behavior
    unique case (select)
      2'd0: assert (out[1:0] == pos && out[2] == 1'b0)
              else $error("select=0: out should be {0,pos}. out=%b pos=%b", out, pos);
      2'd1: assert (out == out_not[5:3])
              else $error("select=1: out should be out_not[5:3]. out=%b out_not[5:3]=%b", out, out_not[5:3]);
      default: assert (out == (out_or_logical ? out_not[2:0] : 3'b000))
              else $error("select>=2: out should be (out_or_logical ? out_not[2:0] : 0). out=%b", out);
    endcase

    // X/Z hygiene: if inputs known, outputs must be known
    if (!$isunknown({in,a,b,select}))
      assert (!$isunknown({pos,out_or_bitwise,out_or_logical,out_not,out}))
        else $error("Outputs contain X/Z while inputs are known");

    // Coverage
    // priority_encoder
    cover (in == 4'b0000 && pos == 2'b00);
    cover (in == 4'b0001 && pos == 2'b00);
    cover (in == 4'b0010 && pos == 2'b01);
    cover (in == 4'b0100 && pos == 2'b10);
    cover (in == 4'b1000 && pos == 2'b11);
    cover (in == 4'b1010 && pos == 2'b11); // priority with multiple 1s

    // binary_module
    cover (a == 3'b000 && b == 3'b000 && out_or_logical == 1'b0);
    cover ((a != 3'b000 || b != 3'b000) && out_or_logical == 1'b1);
    cover (out_or_bitwise == (a | b));
    cover (out_not == ~{a,b});

    // select paths
    cover (select == 2'd0 && out[1:0] == pos && out[2] == 1'b0);
    cover (select == 2'd1 && out == out_not[5:3]);
    cover (select inside {2,3} && out_or_logical == 1'b0 && out == 3'b000);
    cover (select inside {2,3} && out_or_logical == 1'b1 && out == out_not[2:0]);
  end
endmodule

bind top_module top_module_sva
(
  .in(in),
  .a(a),
  .b(b),
  .select(select),
  .pos(pos),
  .out_or_bitwise(out_or_bitwise),
  .out_or_logical(out_or_logical),
  .out_not(out_not),
  .out(out)
);