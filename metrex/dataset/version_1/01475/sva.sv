// SVA for the provided design. Bind these to the DUT; no DUT edits required.

// ---------------- Johnson counter ----------------
module johnson_counter_sva(input logic clk, input logic rst_n, input logic [7:0] out_vec);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (!rst_n |-> out_vec == 8'h00);

  // Allowed outputs only (as per case list)
  assert property (out_vec inside {8'h00,8'h80,8'hC0,8'hE0,8'hF0,8'h78,8'h3C,8'h1E,8'h0F});

  // Next-state relation (intended Johnson-like sequence)
  property p_jc_next;
    disable iff (!rst_n)
    case ($past(out_vec))
      8'h00: out_vec==8'h80;
      8'h80: out_vec==8'hC0;
      8'hC0: out_vec==8'hE0;
      8'hE0: out_vec==8'hF0;
      8'hF0: out_vec==8'h78;
      8'h78: out_vec==8'h3C;
      8'h3C: out_vec==8'h1E;
      8'h1E: out_vec==8'h0F;
      8'h0F: out_vec==8'h00;
      default: 1'b1;
    endcase
  endproperty
  assert property (p_jc_next);

  // Coverage
  cover property (rst_n ##1 out_vec != 8'h00);
  sequence s_jc_cycle;
    8'h00 ##1 8'h80 ##1 8'hC0 ##1 8'hE0 ##1 8'hF0 ##1 8'h78 ##1 8'h3C ##1 8'h1E ##1 8'h0F ##1 8'h00;
  endsequence
  cover property (disable iff (!rst_n) s_jc_cycle);
endmodule

bind johnson_counter johnson_counter_sva jc_sva(.clk(clk), .rst_n(rst_n), .out_vec(out_vec));


// ---------------- Binary number module ----------------
module binary_number_module_sva(
  input logic [3:0] in_vec,
  input logic [3:0] out_vec,
  input logic msb_out, input logic mid_out, input logic lsb_out
);
  // Pure combinational checks
  always @* begin
    assert (out_vec == in_vec) else $error("bn: out_vec != in_vec");
    assert (msb_out == in_vec[3]) else $error("bn: msb_out mismatch");
    assert (mid_out == in_vec[2]) else $error("bn: mid_out mismatch");
    assert (lsb_out == in_vec[0]) else $error("bn: lsb_out should reflect in_vec[0]");
  end
endmodule

bind binary_number_module binary_number_module_sva bn_sva(
  .in_vec(in_vec), .out_vec(out_vec), .msb_out(msb_out), .mid_out(mid_out), .lsb_out(lsb_out)
);


// ---------------- Functional module ----------------
module functional_module_sva(
  input logic [7:0] in_vec_1,
  input logic [3:0] in_vec_2,
  input logic [7:0] out_vec
);
  always @* begin
    assert (out_vec == (in_vec_1 | {4'b0000, in_vec_2}))
      else $error("fm: out_vec != in_vec_1 | {0,in_vec_2}");
  end
endmodule

bind functional_module functional_module_sva fm_sva(.*);


// ---------------- Top-level connectivity and end-to-end ----------------
module top_module_sva(
  input logic clk, input logic rst_n,
  input logic [3:0] in_vec,
  input logic [7:0] out_vec,
  input logic msb_out, input logic mid_out, input logic lsb_out
);
  default clocking cb @(posedge clk); endclocking

  // Connectivity to binary_number_module
  assert property (msb_out == in_vec[3]);
  assert property (mid_out == in_vec[2]);
  assert property (lsb_out == in_vec[0]);

  // End-to-end OR behavior
  assert property (out_vec == (jc_out | {4'b0000, bn_out}));

  // Reset effects at top: JC clears; lower nibble passes in_vec
  assert property (!rst_n |-> jc_out == 8'h00);
  assert property (!rst_n |-> out_vec[3:0] == in_vec);

  // Outputs are never X/Z
  assert property (!$isunknown({out_vec, msb_out, mid_out, lsb_out}));

  // Simple functional coverage
  cover property (msb_out==0 ##1 msb_out==1);
  cover property (lsb_out==0 ##1 lsb_out==1);
  cover property (bn_out != 4'h0 ##1 jc_out[7:4] != 4'h0 ##1 out_vec[7:4] != 4'h0);
endmodule

bind top_module top_module_sva top_sva(.*);