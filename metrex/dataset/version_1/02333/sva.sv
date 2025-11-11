// SVA for the given design. Bind these into the DUT.

// Top-level assertions and coverage
module top_module_sva(
  input logic [4:0] in,
  input logic select,
  input logic out_and,
  input logic out_or,
  input logic out_nor,
  input logic [3:0] decoder_out,
  input logic en_and, en_or, en_nor
);
  always_comb begin
    logic [3:0] exp_dec;
    if (!$isunknown({in,select})) begin
      exp_dec = select ? (4'b0001 << in[1:0]) : 4'b0000;
      assert (decoder_out === exp_dec)
        else $error("decoder_out mismatch exp=%b got=%b", exp_dec, decoder_out);

      assert (en_and === decoder_out[0]);
      assert (en_or  === decoder_out[1]);
      assert (en_nor === decoder_out[2]);

      if (select && in[1:0] <= 2) assert ($onehot({en_nor,en_or,en_and}));
      else                          assert ({en_nor,en_or,en_and} == 3'b000);
    end

    if (!$isunknown({in,en_and})) assert (out_and === (en_and ? &in : 1'b0));
    if (!$isunknown({in,en_or })) assert (out_or  === (en_or  ? (|in) : 1'b0));
    if (!$isunknown({in,en_nor})) assert (out_nor === ~(en_nor ? (|in) : 1'b0));

    // Key scenario coverage
    cover (select==0 && decoder_out==4'b0000 && en_and==0 && en_or==0 && en_nor==0
           && out_and==0 && out_or==0 && out_nor==1);
    cover (select==1 && in[1:0]==2'd0 && en_and && !en_or && !en_nor);
    cover (select==1 && in[1:0]==2'd1 && en_or  && !en_and && !en_nor);
    cover (select==1 && in[1:0]==2'd2 && en_nor && !en_and && !en_or);
    cover (select==1 && in[1:0]==2'd3 && !en_and && !en_or && !en_nor);

    cover (en_and && &in     && out_and);
    cover (en_and && !(&in)  && !out_and);
    cover (en_or  && (|in)   && out_or);
    cover (en_or  && !(|in)  && !out_or);
    cover (en_nor && !(|in)  && out_nor);
    cover (en_nor && (|in)   && !out_nor);
    cover (!en_nor && out_nor); // NOR disabled => 1
  end
endmodule

bind top_module top_module_sva top_sva(
  .in(in), .select(select),
  .out_and(out_and), .out_or(out_or), .out_nor(out_nor),
  .decoder_out(decoder_out),
  .en_and(en_and), .en_or(en_or), .en_nor(en_nor)
);

// Decoder (2-to-4) assertions and coverage
module decoder_2to4_sva(
  input logic [1:0] in,
  input logic [3:0] out
);
  always_comb begin
    if (!$isunknown(in)) begin
      assert (out === (4'b0001 << in));
      assert ($onehot(out));
    end
    cover (in==2'd0 && out==4'b0001);
    cover (in==2'd1 && out==4'b0010);
    cover (in==2'd2 && out==4'b0100);
    cover (in==2'd3 && out==4'b1000);
  end
endmodule

bind decoder_2to4 decoder_2to4_sva dec2to4_sva(.in(in), .out(out));

// Decoder with enable assertions and coverage
module decoder_2to4_with_enable_sva(
  input logic [1:0] in,
  input logic enable,
  input logic [3:0] out
);
  always_comb begin
    if (!$isunknown({in,enable})) begin
      assert (out === (enable ? (4'b0001 << in) : 4'b0000));
      if (enable) assert ($onehot(out)); else assert (out==4'b0000);
    end
    cover (!enable && out==4'b0000);
    cover (enable && in==2'd0 && out==4'b0001);
    cover (enable && in==2'd1 && out==4'b0010);
    cover (enable && in==2'd2 && out==4'b0100);
    cover (enable && in==2'd3 && out==4'b1000);
  end
endmodule

bind decoder_2to4_with_enable decoder_2to4_with_enable_sva dec_en_sva(.in(in), .enable(enable), .out(out));

// AND gate assertions and coverage
module and_gate_5input_sva(
  input logic [4:0] in,
  input logic enable,
  input logic out
);
  always_comb begin
    if (!$isunknown({in,enable})) begin
      assert (out === (enable ? &in : 1'b0));
      if (enable && out) assert (&in);
      if (!enable)       assert (out==1'b0);
    end
    cover (enable && &in    && out);
    cover (enable && !(&in) && !out);
  end
endmodule

bind and_gate_5input and_gate_5input_sva and5_sva(.in(in), .enable(enable), .out(out));

// OR gate assertions and coverage
module or_gate_5input_sva(
  input logic [4:0] in,
  input logic enable,
  input logic out
);
  always_comb begin
    if (!$isunknown({in,enable})) begin
      assert (out === (enable ? (|in) : 1'b0));
      if (!enable) assert (out==1'b0);
    end
    cover (enable && (|in)  && out);
    cover (enable && !(|in) && !out);
  end
endmodule

bind or_gate_5input or_gate_5input_sva or5_sva(.in(in), .enable(enable), .out(out));

// NOR gate assertions and coverage
module nor_gate_5input_sva(
  input logic [4:0] in,
  input logic enable,
  input logic out
);
  always_comb begin
    if (!$isunknown({in,enable})) begin
      assert (out === ~(enable ? (|in) : 1'b0)); // matches implementation
      if (!enable) assert (out==1'b1);
    end
    cover (enable && !(|in) && out);
    cover (enable &&  (|in) && !out);
    cover (!enable && out); // disabled => 1
  end
endmodule

bind nor_gate_5input nor_gate_5input_sva nor5_sva(.in(in), .enable(enable), .out(out));