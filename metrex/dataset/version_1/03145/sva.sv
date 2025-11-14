// SVA checker for top_module
module top_module_sva (
    input  logic        select,
    input  logic [2:0]  sel,
    input  logic [3:0]  data0, data1, data2, data3, data4, data5,
    input  logic [3:0]  out,       // DUT output
    input  logic [3:0]  mux_out,   // internal
    input  logic [5:0]  enc_out,   // internal
    input  logic [7:0]  dec_out    // internal
);

  // Recreate priority_encoder input (MSBs of data0..5)
  logic [5:0] pe_in;
  assign pe_in = {data0[3], data1[3], data2[3], data3[3], data4[3], data5[3]};

  // Bit-reversal for 6-bit vector
  function automatic logic [5:0] reverse6 (input logic [5:0] a);
    reverse6 = {a[0],a[1],a[2],a[3],a[4],a[5]};
  endfunction

  // Top-level mux equivalence
  always_comb begin
    assert (out === mux_out) else $error("out != mux_out");

    // Sanity on dynamic indexing domains
    assert (!(select && (sel > 3'd1))) else $error("select=1 with sel>1 causes OOB part-select on dec_out");
    assert (!select -> (sel <= 3'd3)) else $error("select=0 with sel>3 causes OOB bit-select on data[*][sel]");

    // select == 0: priority chain based on datai[sel]
    if (!select) begin
      if (data0[sel])                           assert (out == data0) else $error("Expected data0");
      if (!data0[sel] && data1[sel])            assert (out == data1) else $error("Expected data1");
      if (!data0[sel] && !data1[sel] && data2[sel]) assert (out == data2) else $error("Expected data2");
      if (!data0[sel] && !data1[sel] && !data2[sel] && data3[sel]) assert (out == data3) else $error("Expected data3");
      if (!data0[sel] && !data1[sel] && !data2[sel] && !data3[sel] && data4[sel]) assert (out == data4) else $error("Expected data4");
      if (!data0[sel] && !data1[sel] && !data2[sel] && !data3[sel] && !data4[sel]) assert (out == data5) else $error("Expected data5 (default)");
    end
    // select == 1: dynamic slice from decoder
    else begin
      assert (out === dec_out[sel*4 +: 4]) else $error("Decoder nibble mismatch");
    end
  end

  // priority_encoder checks
  always_comb begin
    assert ($onehot(pe_in) -> ( $onehot(enc_out) && enc_out == reverse6(pe_in) ))
      else $error("priority_encoder: onehot input must map to reversed onehot output");
    assert (!$onehot(pe_in) -> (enc_out == 6'b0))
      else $error("priority_encoder: non-onehot input must map to 0");
  end

  // decoder checks
  always_comb begin
    assert ($onehot(dec_out)) else $error("decoder: output not onehot");
    assert (dec_out == (8'b1 << sel)) else $error("decoder: wrong onehot position");
  end

  // Lightweight coverage
  always_comb begin
    // Decoder coverage
    cover (select && (sel==3'd0) && (out===dec_out[3:0]));
    cover (select && (sel==3'd1) && (out===dec_out[7:4]));
    // Illegal condition seen (useful to detect bad stimulus/design)
    cover (select && (sel>3'd1));

    // Priority path coverage
    cover (!select && (sel<=3) &&  data0[sel]                                       && out==data0);
    cover (!select && (sel<=3) && !data0[sel] &&  data1[sel]                         && out==data1);
    cover (!select && (sel<=3) && !data0[sel] && !data1[sel] &&  data2[sel]          && out==data2);
    cover (!select && (sel<=3) && !data0[sel] && !data1[sel] && !data2[sel] && data3[sel] && out==data3);
    cover (!select && (sel<=3) && !data0[sel] && !data1[sel] && !data2[sel] && !data3[sel] && data4[sel] && out==data4);
    cover (!select && (sel<=3) && !data0[sel] && !data1[sel] && !data2[sel] && !data3[sel] && !data4[sel] && out==data5);

    // priority_encoder coverage
    cover ($onehot(pe_in) && enc_out == reverse6(pe_in));
    cover (pe_in == 6'b0 && enc_out == 6'b0);

    // decoder full-range coverage
    cover (sel==3'd0 && dec_out==8'b0000_0001);
    cover (sel==3'd1 && dec_out==8'b0000_0010);
    cover (sel==3'd2 && dec_out==8'b0000_0100);
    cover (sel==3'd3 && dec_out==8'b0000_1000);
    cover (sel==3'd4 && dec_out==8'b0001_0000);
    cover (sel==3'd5 && dec_out==8'b0010_0000);
    cover (sel==3'd6 && dec_out==8'b0100_0000);
    cover (sel==3'd7 && dec_out==8'b1000_0000);
  end

endmodule

// Bind into DUT (connects to internal nets by name)
bind top_module top_module_sva sva_i (.*);