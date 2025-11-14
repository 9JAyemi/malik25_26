// SVA for gray_code_converter
// Assumed spec (standard binary->Gray, MSB preserved):
// G[3]=B[3]; G[2]=B[3]^B[2]; G[1]=B[2]^B[1]; G[0]=B[1]^B[0]

module gray_code_converter_sva (input [3:0] data_in, input [3:0] gray_out);

  function automatic [3:0] gray_ref(input [3:0] b);
    gray_ref = {b[3], b[3]^b[2], b[2]^b[1], b[1]^b[0]};
  endfunction

  // Functional correctness
  assert property (@(data_in) gray_out == gray_ref(data_in));

  // No X/Z on outputs when inputs are clean
  assert property (@(data_in or gray_out) !$isunknown(data_in) |-> !$isunknown(gray_out));

  // Purely combinational behavior
  assert property (@(data_in or gray_out) $stable(data_in) |-> $stable(gray_out));

  // Gray property: one-bit input change => one-bit output change
  assert property (@(data_in)
                   !$isunknown($past(data_in)) &&
                   $onehot(data_in ^ $past(data_in))
                   |-> $onehot(gray_out ^ $past(gray_out)));

  // Coverage
  cover property (@(data_in) gray_out == gray_ref(data_in)); // functional hit

  genvar v;
  generate
    // All input values seen
    for (v=0; v<16; v++) begin : cg_in_vals
      cover property (@(data_in) data_in == v[3:0]);
    end
    // All output values seen
    for (v=0; v<16; v++) begin : cg_out_vals
      cover property (@(data_in) gray_out == v[3:0]);
    end
    // Observe one-bit input changes produce one-bit output changes
    for (v=0; v<4; v++) begin : cg_onebit
      cover property (@(data_in)
                      !$isunknown($past(data_in)) &&
                      ((data_in ^ $past(data_in)) == (4'b1 << v)) &&
                      $onehot(gray_out ^ $past(gray_out)));
    end
  endgenerate
endmodule

bind gray_code_converter gray_code_converter_sva i_sva(.data_in(data_in), .gray_out(gray_out));