// SVA for nor4b — concise, high-quality checks plus full truth-table coverage
module nor4b_sva (
  input logic A, B, C, D_N,
  input logic Y, Y_N,
  input logic not0_out, nor0_out_Y
);

  // Functional correctness (checked on any input change; settle via ##0)
  property p_func;
    !$isunknown({A,B,C,D_N}) |-> ##0
      (Y   === (~A & ~B & ~C & D_N) &&
       Y_N === ~Y);
  endproperty
  assert property (@(A or B or C or D_N) p_func);

  // Structural checks on internal nets
  assert property (@(D_N)                     !$isunknown(D_N)                     |-> ##0 (not0_out   === ~D_N));
  assert property (@(A or B or C or not0_out) !$isunknown({A,B,C,not0_out})        |-> ##0 (nor0_out_Y === ~(A|B|C|not0_out)));
  assert property (@(nor0_out_Y)              !$isunknown(nor0_out_Y)              |-> ##0 (Y          === nor0_out_Y));
  assert property (@(Y or Y_N)                !$isunknown({Y,Y_N})                 |-> ##0 (Y_N        === ~Y));

  // Outputs known when inputs are known
  assert property (@(A or B or C or D_N) !$isunknown({A,B,C,D_N}) |-> ##0 !$isunknown({Y,Y_N}));

  // Truth-table coverage: all 16 input combinations observed
  wire [3:0] combo = {A,B,C,D_N};
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_tt_cov
      cover property (@(A or B or C or D_N) ##0 (combo == i[3:0]));
    end
  endgenerate

  // Output state coverage
  cover property (@(A or B or C or D_N) ##0 (Y==1'b1 && Y_N==1'b0));
  cover property (@(A or B or C or D_N) ##0 (Y==1'b0 && Y_N==1'b1));

endmodule

// Bind into the DUT (connects to internal nets by name)
bind nor4b nor4b_sva u_nor4b_sva (.*);