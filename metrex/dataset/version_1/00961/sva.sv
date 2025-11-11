// SVA checkers for the provided design (combinational, immediate assertions)

// Top-level end-to-end functional equivalence
module top_module_sva (
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic        mode,
  input logic [15:0] data_in,
  input logic [31:0] final_out
);
  always_comb begin
    assert (!$isunknown({a,b,mode,data_in,final_out})) else $error("X/Z on top I/O");

    logic [3:0]  add_sub_exp = mode ? (a + b) : (a - b);     // wraps to 4 bits
    logic [7:0]  cc_exp      = {~data_in[15:8], data_in[7:0]};
    logic [31:0] func_exp    = mode ? {add_sub_exp, cc_exp, 1'b0}
                                    : {add_sub_exp, cc_exp};

    assert (final_out === func_exp) else $error("final_out functional mismatch");

    // Integration coverage
    cover (mode);
    cover (!mode);
    cover (mode  && (a + b) > 4'hF); // add overflow/wrap
    cover (!mode && (a < b));        // sub underflow/wrap
    cover (cc_exp == 8'h00);
    cover (cc_exp == 8'hFF);
  end
endmodule

bind top_module top_module_sva i_top_module_sva (
  .a(a), .b(b), .mode(mode), .data_in(data_in), .final_out(final_out)
);


// Leaf: add_sub functional and corner coverage
module add_sub_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic       mode,
  input logic [3:0] out
);
  always_comb begin
    assert (!$isunknown({a,b,mode,out})) else $error("X/Z in add_sub I/O");

    logic [3:0] exp = mode ? (a + b) : (a - b); // 4-bit wrap
    assert (out === exp) else $error("add_sub out mismatch");

    cover (mode);
    cover (!mode);
    cover (mode  && (a + b) > 4'hF);
    cover (!mode && (a < b));
  end
endmodule

bind add_sub add_sub_sva i_add_sub_sva (.a(a), .b(b), .mode(mode), .out(out));


// Leaf: complement_concat functional and corner coverage
module complement_concat_sva (
  input logic [15:0] data_in,
  input logic [7:0]  out
);
  always_comb begin
    assert (!$isunknown({data_in,out})) else $error("X/Z in complement_concat I/O");

    logic [7:0] exp = {~data_in[15:8], data_in[7:0]};
    assert (out === exp) else $error("complement_concat out mismatch");

    cover (data_in[15:8] == 8'h00);
    cover (data_in[15:8] == 8'hFF);
    cover (data_in[7:0]  == 8'h00);
    cover (data_in[7:0]  == 8'hFF);
  end
endmodule

bind complement_concat complement_concat_sva i_complement_concat_sva (.data_in(data_in), .out(out));


// Leaf: functional_module width/packing and mode behavior
module functional_module_sva (
  input logic [3:0]  in1,
  input logic [7:0]  in2,
  input logic        mode,
  input logic [31:0] out
);
  always_comb begin
    assert (!$isunknown({in1,in2,mode,out})) else $error("X/Z in functional_module I/O");

    logic [31:0] exp = mode ? {in1, in2, 1'b0} : {in1, in2};
    assert (out === exp) else $error("functional_module out mismatch");

    if (mode) begin
      assert (out[0]     == 1'b0) else $error("mode=1 LSB not 0");
      assert (out[8:1]   === in2) else $error("mode=1 in2 mispacked");
      assert (out[12:9]  === in1) else $error("mode=1 in1 mispacked");
      assert (out[31:13] == '0)   else $error("mode=1 upper bits not zero");
    end else begin
      assert (out[7:0]   === in2) else $error("mode=0 in2 mispacked");
      assert (out[11:8]  === in1) else $error("mode=0 in1 mispacked");
      assert (out[31:12] == '0)   else $error("mode=0 upper bits not zero");
    end

    cover (mode);
    cover (!mode);
  end
endmodule

bind functional_module functional_module_sva i_functional_module_sva (.in1(in1), .in2(in2), .mode(mode), .out(out));