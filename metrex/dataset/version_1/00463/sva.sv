// SVA checker for circl_s
module circl_s_sva (
  input logic [4:0] in_addr,
  input logic [4:0] out_word
);
  // LUT of expected outputs
  localparam logic [4:0] LUT [0:31] = '{
    5'h00, 5'h05, 5'h09, 5'h0B, 5'h0D, 5'h0F, 5'h10, 5'h12,
    5'h13, 5'h14, 5'h15, 5'h16, 5'h17, 5'h17, 5'h18, 5'h19,
    5'h19, 5'h1A, 5'h1A, 5'h1B, 5'h1B, 5'h1C, 5'h1C, 5'h1C,
    5'h1C, 5'h1D, 5'h1D, 5'h1D, 5'h1D, 5'h1D, 5'h1D, 5'h00
  };

  // Interface sanity
  a_no_x_in:  assert property (!$isunknown(in_addr))
    else $error("circl_s: in_addr contains X/Z");
  a_no_x_out: assert property (!$isunknown(out_word))
    else $error("circl_s: out_word contains X/Z");

  // Functional equivalence (clockless, holds continuously)
  a_map: assert property (!$isunknown(in_addr) |-> out_word == LUT[in_addr])
    else $error("circl_s: out_word != LUT[in_addr]");

  // Explicit wrap check (redundant but highlights corner)
  a_wrap: assert property (in_addr == 5'h1F |-> out_word == 5'h00))
    else $error("circl_s: wrap case 1F->00 failed");

  // Functional coverage of every address/output pair
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : g_cov
      c_pair: cover property (in_addr == 5'(i) && out_word == LUT[i]);
    end
  endgenerate
endmodule

// Bind into the DUT
bind circl_s circl_s_sva u_circl_s_sva (.in_addr(in_addr), .out_word(out_word));