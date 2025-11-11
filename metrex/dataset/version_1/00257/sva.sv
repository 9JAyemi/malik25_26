// SVA for full_adder and add4 (bind-ready, concise, high-quality checks and coverage)

// Full-adder SVA: truth-table correctness, X-prop check, full 3-bit input coverage
module full_adder_sva (full_adder dut);

  // Functional correctness (cast to 2 bits avoids width warnings)
  assert property (@(*)
    {dut.cout, dut.sum} == logic [1:0]'(dut.a + dut.b + dut.cin)
  );

  // Outputs must be 2-state when inputs are 2-state
  assert property (@(*)
    !$isunknown({dut.a,dut.b,dut.cin}) |-> !$isunknown({dut.sum,dut.cout})
  );

  // Full input truth-table coverage (all 8 combinations)
  cover property (@(*) {dut.a,dut.b,dut.cin} == 3'b000);
  cover property (@(*) {dut.a,dut.b,dut.cin} == 3'b001);
  cover property (@(*) {dut.a,dut.b,dut.cin} == 3'b010);
  cover property (@(*) {dut.a,dut.b,dut.cin} == 3'b011);
  cover property (@(*) {dut.a,dut.b,dut.cin} == 3'b100);
  cover property (@(*) {dut.a,dut.b,dut.cin} == 3'b101);
  cover property (@(*) {dut.a,dut.b,dut.cin} == 3'b110);
  cover property (@(*) {dut.a,dut.b,dut.cin} == 3'b111);

  // Carry/no-carry seen
  cover property (@(*) dut.cout);
  cover property (@(*) !dut.cout);

endmodule


// 4-bit ripple-carry adder SVA: end-to-end arithmetic, internal chain, X-prop, key coverage
module add4_sva (add4 dut);

  // End-to-end arithmetic correctness (cast to 5 bits)
  assert property (@(*)
    {dut.cout, dut.sum} == logic [4:0]'(dut.a + dut.b + dut.cin)
  );

  // Sum mirrors internal s bus
  assert property (@(*)
    dut.sum == dut.s
  );

  // Bitwise ripple chain correctness
  assert property (@(*)
    {dut.c1, dut.s[0]} == logic [1:0]'(dut.a[0] + dut.b[0] + dut.cin)
  );
  assert property (@(*)
    {dut.c2, dut.s[1]} == logic [1:0]'(dut.a[1] + dut.b[1] + dut.c1)
  );
  assert property (@(*)
    {dut.c3, dut.s[2]} == logic [1:0]'(dut.a[2] + dut.b[2] + dut.c2)
  );
  assert property (@(*)
    {dut.cout, dut.s[3]} == logic [1:0]'(dut.a[3] + dut.b[3] + dut.c3)
  );

  // Outputs/internal nets must be 2-state when inputs are 2-state
  assert property (@(*)
    !$isunknown({dut.a, dut.b, dut.cin}) |-> !$isunknown({dut.sum, dut.cout, dut.s, dut.c1, dut.c2, dut.c3})
  );

  // Key scenario coverage
  cover property (@(*) {dut.a,dut.b,dut.cin} == {4'h0,4'h0,1'b0});        // zero + zero
  cover property (@(*) {dut.a,dut.b,dut.cin} == {4'hF,4'hF,1'b1});        // max + max + 1
  cover property (@(*) (dut.a ^ dut.b) == 4'hF && dut.cin && dut.cout);   // full propagate chain
  cover property (@(*) dut.cout);     // any carry out observed
  cover property (@(*) !dut.cout);    // no carry out observed

  // Per-bit generate/propagate/kill coverage
  genvar i;
  generate
    for (i=0; i<4; i++) begin : cov_bits
      cover property (@(*) (dut.a[i] & dut.b[i]));   // generate
      cover property (@(*) (dut.a[i] ^ dut.b[i]));   // propagate-capable
      cover property (@(*) ~(dut.a[i] | dut.b[i]));  // kill
    end
  endgenerate

endmodule

// Bind into the DUTs
bind full_adder full_adder_sva fa_sva();
bind add4       add4_sva       add4_sva();