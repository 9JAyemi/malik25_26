// SVA for binary_to_gray
module binary_to_gray_sva (input logic [3:0] binary, input logic [3:0] gray);

  function automatic bit no_x4 (logic [3:0] v); no_x4 = !$isunknown(v); endfunction
  wire [3:0] exp_gray = binary ^ (binary >> 1);

  default clocking cb @(binary); endclocking

  // Functional correctness when inputs are known (0-delay combinational check)
  a_map:  assert property (no_x4(binary) |-> ##0 (gray == exp_gray));
  // No X/Z on output when inputs are known
  a_no_x: assert property (no_x4(binary) |-> no_x4(gray));

  // No spurious output changes without input change
  property p_gray_change_implies_binary_changed;
    @(gray) 1 |-> $changed(binary);
  endproperty
  a_no_spur: assert property (p_gray_change_implies_binary_changed);

  // Gray must flip exactly one bit when binary increments by +1
  a_onehot_on_inc: assert property (
    no_x4(binary) && no_x4($past(binary)) &&
    (binary == $past(binary) + 1) |-> $onehot(gray ^ $past(gray))
  );

  // Functional coverage: observe all 16 mappings
  genvar i;
  generate
    for (i=0; i<16; i++) begin : C
      localparam logic [3:0] BIN = i[3:0];
      localparam logic [3:0] G   = BIN ^ (BIN >> 1);
      c_map: cover property (binary == BIN && gray == G);
    end
  endgenerate

  // Coverage: observe one-bit flip on +1 increments
  c_onehot_inc: cover property (
    no_x4(binary) && no_x4($past(binary)) &&
    (binary == $past(binary) + 1) && $onehot(gray ^ $past(gray))
  );

endmodule

bind binary_to_gray binary_to_gray_sva sva_inst (.binary(binary), .gray(gray));