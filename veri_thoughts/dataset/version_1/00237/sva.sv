// SVA checker for power_of_2_detection
module power_of_2_detection_sva (
  input  logic [15:0] num,
  input  logic        is_power_of_2
);

  // No X/Z on interface
  assert property (@(num or is_power_of_2) !$isunknown({num, is_power_of_2}));

  // Functional equivalence: exactly one bit set -> 1, else 0 (covers num==0 too)
  assert property (@(num or is_power_of_2) is_power_of_2 == $onehot(num));

  // Redundant but explicit special/partitioned checks
  assert property (@(num or is_power_of_2) (num == 16'h0000) |-> (is_power_of_2 == 1'b0));
  assert property (@(num or is_power_of_2)  $onehot(num)     |-> (is_power_of_2 == 1'b1));
  assert property (@(num or is_power_of_2) (num != 0 && !$onehot(num)) |-> (is_power_of_2 == 1'b0));

  // Output only changes when input changes (no spontaneous glitches)
  assert property (@(num or is_power_of_2) $changed(is_power_of_2) |-> $changed(num));

  // Coverage
  cover property (@(num or is_power_of_2) num == 16'h0000 && is_power_of_2 == 1'b0);
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_ONEHOT
      cover property (@(num or is_power_of_2) num == (16'h1 << i) && is_power_of_2 == 1'b1);
    end
  endgenerate
  cover property (@(num or is_power_of_2) (num != 0 && !$onehot(num)) && is_power_of_2 == 1'b0);

endmodule

// Bind into DUT
bind power_of_2_detection power_of_2_detection_sva sva_i (
  .num(num),
  .is_power_of_2(is_power_of_2)
);