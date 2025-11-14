// SVA checker for priority_encoder
module priority_encoder_sva (
  input logic [7:0] I,
  input logic       EN,
  input logic [2:0] Y
);

  // Outputs must be 0/1 when inputs are known
  assert property (@(I or EN or Y) !$isunknown(I) |-> !$isunknown({EN,Y}));

  // Default/else case: anything not exactly 1-hot (including I==0 or multi-hot)
  assert property (@(I or EN or Y) !$isunknown(I) && !$onehot(I) |-> (EN==1 && Y==3'b000));

  // EN low implies exactly one bit is set and matches Y
  assert property (@(I or EN or Y) !($isunknown({I,EN,Y})) && (EN==0) |-> ($onehot(I) && I==(8'b1<<Y)));

  // EN high implies not one-hot and Y must be 0
  assert property (@(I or EN or Y) !($isunknown({I,EN,Y})) && (EN==1) |-> (!$onehot(I) && Y==3'b000));

  // Exact mapping for all 1-hot inputs
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_onehot_map
      assert property (@(I or EN or Y)
        !$isunknown(I) && (I == (8'b1<<i)) |-> (EN==0 && Y==3'(i))
      );
      // Functional coverage for each 1-hot input mapping
      cover property (@(I or EN or Y) (I==(8'b1<<i)) && EN==0 && (Y==3'(i)));
    end
  endgenerate

  // Coverage: default when I==0
  cover property (@(I or EN or Y) (I==8'b0) && EN==1 && Y==3'b000);

  // Coverage: at least one multi-hot case hits default
  cover property (@(I or EN or Y) (I!=8'b0) && !$onehot(I) && EN==1 && Y==3'b000);

endmodule

// Bind into the DUT
bind priority_encoder priority_encoder_sva sva_inst (.I(I), .EN(EN), .Y(Y));