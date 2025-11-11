// SVA checker for magnitude_comparator
module magnitude_comparator_sva (
    input valid,
    input [3:0] A,
    input [3:0] B,
    input [1:0] sel,
    input [1:0] out_mode0,
    input less_than,
    input equal_to,
    input greater_than
);

  default clocking cb @(posedge valid); endclocking

  logic lt, eq, gt;
  logic [1:0] exp_mag;

  always_comb begin
    lt = (A < B);
    eq = (A == B);
    gt = (A > B);
    unique case (1'b1)
      eq: exp_mag = 2'b00;
      gt: exp_mag = 2'b01;
      default: exp_mag = 2'b10; // lt
    endcase
  end

  // Functional equivalence (single concise check)
  ap_functional_all: assert property (
    1 |-> (out_mode0 == ((sel==2'b00) ? exp_mag : 2'b00)) &&
         (less_than == ((sel==2'b01) ? lt : 1'b0)) &&
         (equal_to == ((sel==2'b01) ? eq : 1'b0)) &&
         (greater_than == ((sel==2'b01) ? gt : 1'b0))
  );

  // Encodings and mutual exclusivity
  ap_mode0_enc:     assert property (sel==2'b00 |-> out_mode0 inside {2'b00,2'b01,2'b10});
  ap_mode1_onehot:  assert property (sel==2'b01 |-> $onehot({less_than,equal_to,greater_than}));

  // Outputs known when inputs known
  ap_known: assert property (
    !$isunknown({sel,A,B}) |-> !$isunknown({out_mode0,less_than,equal_to,greater_than})
  );

  // Basic coverage
  cv_eq_m0:  cover property (sel==2'b00 && eq && out_mode0==2'b00);
  cv_gt_m0:  cover property (sel==2'b00 && gt && out_mode0==2'b01);
  cv_lt_m0:  cover property (sel==2'b00 && lt && out_mode0==2'b10);

  cv_eq_m1:  cover property (sel==2'b01 && eq &&  equal_to);
  cv_gt_m1:  cover property (sel==2'b01 && gt &&  greater_than);
  cv_lt_m1:  cover property (sel==2'b01 && lt &&  less_than);

  cv_other:  cover property ((sel inside {2'b10,2'b11}) &&
                             out_mode0==2'b00 && !less_than && !equal_to && !greater_than);

endmodule

// Bind into DUT
bind magnitude_comparator magnitude_comparator_sva sva_i (
  .valid(valid),
  .A(A),
  .B(B),
  .sel(sel),
  .out_mode0(out_mode0),
  .less_than(less_than),
  .equal_to(equal_to),
  .greater_than(greater_than)
);